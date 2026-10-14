"""Operating-system services only; no mining or arithmetic decisions."""
import ctypes
import errno
import os
from pathlib import Path
import select
import subprocess
import sys
import time

WINDOWS = sys.platform == 'win32'

if not WINDOWS:
    import fcntl
else:
    import msvcrt

    class fcntl:
        LOCK_EX, LOCK_NB, LOCK_UN = 2, 4, 8

        @staticmethod
        def flock(file, operation):
            fd = file if isinstance(file, int) else file.fileno()
            os.lseek(fd, 0, os.SEEK_SET)
            if operation & fcntl.LOCK_UN:
                msvcrt.locking(fd, msvcrt.LK_UNLCK, 1)
                return
            while True:
                try:
                    msvcrt.locking(fd, msvcrt.LK_NBLCK, 1)
                    return
                except OSError as error:
                    if error.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
                        raise
                    if operation & fcntl.LOCK_NB:
                        raise BlockingIOError(errno.EAGAIN, 'Lock already held') from None
                    time.sleep(.05)


def native_name(name):
    return name + ('.dll' if WINDOWS else '.dylib' if sys.platform == 'darwin' else '.so')


def bitcoin_directory():
    if WINDOWS:
        return Path(os.environ.get('APPDATA', Path.home()/'AppData'/'Roaming'))/'Bitcoin'
    if sys.platform == 'darwin':
        return Path.home()/'Library/Application Support/Bitcoin'
    return Path.home()/'.bitcoin'


def detached_options():
    if WINDOWS:
        return {'creationflags': subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.DETACHED_PROCESS}
    return {'start_new_session': True}


def private_file(path):
    """Protect local control credentials. Fail closed if Windows ACL setup fails."""
    if not WINDOWS:
        os.chmod(path, 0o600)
        return
    import csv
    row = list(csv.reader(subprocess.check_output(
        ['whoami', '/user', '/fo', 'csv', '/nh'], text=True).splitlines()))[0]
    sid = row[-1]
    if not sid.startswith('S-1-'):
        raise OSError('Cannot identify current Windows user')
    subprocess.run(['icacls', str(path), '/inheritance:r', '/grant:r', '*'+sid+':F'],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def pipe_read(pipe, size, timeout):
    if not WINDOWS:
        if not select.select([pipe], [], [], timeout)[0]:
            raise TimeoutError('pruning worker budget exceeded')
        return os.read(pipe.fileno(), size)
    import msvcrt
    from ctypes import wintypes
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.PeekNamedPipe.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD,
                                     ctypes.c_void_p, ctypes.POINTER(wintypes.DWORD), ctypes.c_void_p]
    handle = msvcrt.get_osfhandle(pipe.fileno())
    deadline = time.monotonic()+timeout
    while True:
        available = wintypes.DWORD()
        if not kernel.PeekNamedPipe(handle, None, 0, None, ctypes.byref(available), None):
            if ctypes.get_last_error() == 109: return b''
            raise ctypes.WinError(ctypes.get_last_error())
        if available.value:
            return os.read(pipe.fileno(), min(size, available.value))
        if time.monotonic() >= deadline:
            raise TimeoutError('pruning worker budget exceeded')
        time.sleep(.005)


class Terminal:
    def enter(self):
        if not WINDOWS:
            import termios, tty
            self.previous = termios.tcgetattr(sys.stdin.fileno())
            tty.setraw(sys.stdin.fileno())
            return
        from ctypes import wintypes
        self.kernel = ctypes.WinDLL('kernel32', use_last_error=True)
        self.kernel.GetStdHandle.restype = wintypes.HANDLE
        self.kernel.GetConsoleMode.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
        self.kernel.SetConsoleMode.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        self.modes = []
        try:
            for number, output in ((-11, True), (-10, False)):
                handle = self.kernel.GetStdHandle(number)
                old = wintypes.DWORD()
                if not self.kernel.GetConsoleMode(handle, ctypes.byref(old)):
                    raise OSError('Use an interactive Windows Terminal or PowerShell console')
                mode = old.value | 4 if output else (old.value & ~(2 | 4)) | 0x200
                if not self.kernel.SetConsoleMode(handle, mode):
                    raise ctypes.WinError(ctypes.get_last_error())
                self.modes.append((handle, old.value))
        except BaseException:
            self.restore()
            raise

    def read(self, timeout=.025):
        if not WINDOWS:
            if select.select([sys.stdin], [], [], timeout)[0]:
                return os.read(sys.stdin.fileno(), 4096)
            return None
        import msvcrt
        deadline = time.monotonic()+timeout
        while not msvcrt.kbhit():
            if time.monotonic() >= deadline: return None
            time.sleep(.005)
        char = msvcrt.getwch()
        if char in ('\x00', '\xe0'):
            return {'H': b'\x1b[A', 'P': b'\x1b[B', 'M': b'\x1b[C', 'K': b'\x1b[D',
                    'G': b'\x1b[H', 'O': b'\x1b[F', 'S': b'\x1b[3~'}.get(msvcrt.getwch())
        if 0xd800 <= ord(char) <= 0xdbff:
            char = (char+msvcrt.getwch()).encode('utf-16-le', 'surrogatepass').decode('utf-16-le')
        return char.encode('utf-8', 'replace')

    def restore(self):
        if not WINDOWS:
            import termios
            termios.tcsetattr(sys.stdin.fileno(), termios.TCSADRAIN, self.previous)
        else:
            for handle, mode in getattr(self, 'modes', []): self.kernel.SetConsoleMode(handle, mode)


def idle_seconds():
    if WINDOWS:
        from ctypes import wintypes
        class LastInput(ctypes.Structure):
            _fields_ = [('cbSize', wintypes.UINT), ('dwTime', wintypes.DWORD)]
        value = LastInput(ctypes.sizeof(LastInput), 0)
        if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(value)):
            raise OSError('Last input time unavailable')
        return ((ctypes.windll.kernel32.GetTickCount()-value.dwTime) & 0xffffffff)/1000
    if sys.platform == 'darwin':
        import re
        result = subprocess.run(['/usr/sbin/ioreg', '-c', 'IOHIDSystem'], capture_output=True, text=True, timeout=2)
        match = re.search(r'"HIDIdleTime"\s*=\s*(\d+)', result.stdout)
        return int(match[1])/1e9 if match else None
    # Linux desktop idle protocols differ between Wayland/X11/headless sessions.
    return None
