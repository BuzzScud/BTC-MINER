"""Project-scoped control socket and detached supervisor. No login service."""
from .platform_support import fcntl
import hashlib
import json
import os
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
from contextlib import contextmanager
from pathlib import Path
from . import ROOT
from .platform_support import WINDOWS, detached_options
from . import control_transport
from .settings import LOGS, load, atomic_json

def socket_path(root=None):
    digest = hashlib.sha256(str(root or ROOT).encode()).hexdigest()[:16]
    return Path(tempfile.gettempdir()) / f"btc-miner-{getattr(os, 'getuid', lambda: 'user')()}-{digest}.sock"

def moved_from():
    """The folder a still-running miner was started from, when this folder was moved since.

    The socket name comes from the folder path, so after a move the running miner
    still listens on its old socket and writes to its old logs folder.
    """
    try:
        root = Path(json.loads((LOGS/"process.json").read_text())["root"])
    except (OSError,ValueError,KeyError,TypeError):
        return None
    return root if root != ROOT and socket_path(root).exists() else None

def parse_control(data):
    command = json.loads(data)
    if not isinstance(command, dict) or not isinstance(command.get("command"), str):
        raise ValueError("Control request must contain a command string")
    if "summary" in command and not isinstance(command["summary"], bool):
        raise ValueError("summary must be true or false")
    return command

def request(command="status", **params):
    try:
        return _request(socket_path(),command,params)
    except OSError:
        old = moved_from()
        if old is None:
            raise
        return _request(socket_path(old),command,params)

def _request(address, command, params):
    sock, token = control_transport.connect(address)
    with sock:
        payload = {"command":command,**params}
        if token is not None: payload['_auth'] = token
        sock.sendall((json.dumps(payload)+"\n").encode())
        data = b""
        while b"\n" not in data:
            block = sock.recv(65536)
            if not block:
                break
            data += block
            if len(data)>2*1024*1024:
                raise ValueError("Control response too large")
        return json.loads(data)

def status():
    try:
        return request()
    except (OSError,ValueError):
        path = LOGS/"last-session.json"
        try:
            previous = json.loads(path.read_text())
        except (OSError,ValueError):
            previous = {"hashes":0,"shares_accepted":0,"shares_rejected":0,"blocks_accepted":0,"events":[]}
        return {**previous,"state":"STOPPED","connected":False,"running":False}

def validate_start(c):
    from .protocol import script_for_address
    from .connections import endpoint
    if c["connection"] == "core":
        script_for_address(c["address"],c["network"])
    else:
        endpoint(c["pool"],c["tls"])
        if c["backup"]:
            endpoint(c["backup"],c["tls"])
        if not c["pool_user"] and not c["address"]:
            raise ValueError("Set pool_user or a BTC payout address before starting")
    if c["strategy"] != "thesis2" and (c["native_nonce"] or c["native_candidates"] or c["recovery"]):
        from thesis_mining import _find_c_math_root
        root = _find_c_math_root()
        if root is None:
            raise ValueError("Optional c. math libraries are absent; install them under optional/c. math or disable native_nonce/native_candidates/recovery")

@contextmanager
def lifecycle_lock():
    LOGS.mkdir(exist_ok=True)
    with (LOGS/"control.lock").open("a+") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        yield

def supervisor_running():
    path = LOGS/"supervisor.lock"
    if not path.exists():
        return False
    with path.open("a+") as lock:
        try:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            return True
    return False

def start():
    with lifecycle_lock():
        return _start()

def _start():
    if (ROOT/'.updates/transaction.json').exists():
        raise ValueError('An update needs recovery. Run btc-miner update --rollback before starting.')
    try:
        existing = request()
        if existing.get("running"):
            return {"ok":True,"message":"Attached to the existing BTC miner",**existing}
    except (OSError,ValueError):
        pass
    validate_start(load())
    LOGS.mkdir(exist_ok=True)
    if (LOGS/"stop.request").exists():
        deadline = time.monotonic()+20
        while supervisor_running():
            if time.monotonic() >= deadline:
                raise RuntimeError("Previous miner is still stopping; inspect service logs")
            time.sleep(.05)
    (LOGS/"stop.request").unlink(missing_ok=True)
    if not supervisor_running():
        with (LOGS/"service.log").open("a") as output:
            from .runtime import interpreter
            subprocess.Popen([interpreter(ROOT),"-m","btcminer.service","supervise"],cwd=ROOT,
                             stdin=subprocess.DEVNULL,stdout=output,stderr=output,**detached_options())
    deadline = time.monotonic()+6
    while time.monotonic()<deadline:
        try:
            return {"ok":True,"message":"BTC miner started",**request()}
        except (OSError,ValueError):
            time.sleep(.1)
    raise RuntimeError("Miner did not start. Read logs/service.log for the startup error")

def stop(summary=True):
    with lifecycle_lock():
        return _stop(summary)

def _stop(summary=True):
    LOGS.mkdir(exist_ok=True)
    old = moved_from()
    try:
        reply = request("stop",summary=summary)
    except (OSError,ValueError):
        reply = {"ok":True,"message":"Miner supervisor stopped" if supervisor_running() else "BTC miner is already stopped"}
    else:
        reply = {**reply,"message":"BTC miner stopped; session saved"}
    (LOGS/"stop.request").touch()
    if old is not None and (old/"logs").is_dir():
        # a miner started before the folder moved watches its old folder for the stop request
        (old/"logs"/"stop.request").touch()
    deadline = time.monotonic()+20
    while time.monotonic()<deadline:
        try:
            request()
        except (OSError,ValueError):
            if not supervisor_running():
                return reply
        time.sleep(.1)
    raise RuntimeError("Stop is still draining a network request; check status before restarting")

def restart():
    with lifecycle_lock():
        _stop(summary=False)
        return _start()

def restart_for_math(expected_pid, implementation):
    """Reload reviewed math only for the same actively mining session.

    Drain submissions first and inspect the final counters so finding a block
    during the stop cannot be undone by an automatic restart.
    """
    from .mathrevision import fingerprint
    with lifecycle_lock():
        before = request()
        if (before.get('pid') != expected_pid or not before.get('running') or
                before.get('state') != 'MINING' or before.get('blocks_accepted', 0) or
                (LOGS/'stop.request').exists()):
            return {'applied':False, 'reason':'session changed, stopped, paused, or found a block'}
        if fingerprint() != implementation:
            return {'applied':False, 'reason':'implementation changed after validation'}
        if before.get('math_implementation') == implementation:
            return {'applied':False, 'reason':'already loaded'}
        _stop(summary=False)
        # _stop waits for the final session record and supervisor exit.
        final = json.loads((LOGS/'last-session.json').read_text())
        if final.get('pid') != expected_pid or final.get('blocks_accepted', 0):
            return {'applied':False, 'reason':'final session mismatch or accepted block; left stopped'}
        if fingerprint() != implementation:
            return {'applied':False, 'reason':'implementation changed while stopping; left stopped'}
        reply = _start()
        if not reply.get('running') or reply.get('math_implementation') != implementation:
            _stop(summary=False)
            raise RuntimeError('Updated miner did not load the expected math; left stopped')
        return {'applied':True, 'reason':'reviewed math loaded', 'pid':reply['pid']}


def supervise():
    LOGS.mkdir(exist_ok=True)
    with (LOGS/"supervisor.lock").open("a+") as lock:
        try:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            return 0
        child = None
        halted = threading.Event()
        def halt(*_):
            halted.set()
            if child and child.poll() is None:
                child.terminate()
        signal.signal(signal.SIGTERM,halt)
        signal.signal(signal.SIGINT,halt)
        crashes = []
        while not halted.is_set() and not (LOGS/"stop.request").exists():
            logpath = LOGS/"service.log"
            if logpath.exists() and logpath.stat().st_size > 5*1024*1024:
                os.replace(logpath,LOGS/"service.log.1")
            with logpath.open("a") as output:
                child = subprocess.Popen([sys.executable,"-m","btcminer.service","serve"],cwd=ROOT,stdout=output,stderr=output)
            stopping_at = None
            while child.poll() is None:
                if (LOGS/"stop.request").exists():
                    # The normal stop command reaches the socket; this also stops a crashed/restarting service.
                    halted.set()
                    if stopping_at is None: stopping_at = time.monotonic()
                    if not WINDOWS or time.monotonic()-stopping_at > 30: child.terminate()
                time.sleep(.2)
            code = child.returncode
            if code == 0 or halted.is_set():
                return 0
            now = time.time()
            crashes = [x for x in crashes if now-x<3600]
            from .engine import append_log
            if len(crashes)>=3:
                append_log(LOGS/"events.jsonl",{"ts":now,"kind":"error","message":"Watchdog stopped after 3 restarts in one hour"})
                return 1
            crashes.append(now)
            append_log(LOGS/"events.jsonl",{"ts":now,"kind":"watchdog","message":"Miner exited unexpectedly; restarting in 20 seconds"})
            for _ in range(100):
                if halted.wait(.2) or (LOGS/"stop.request").exists():
                    return 0
    return 0

def serve():
    from .engine import Engine
    config = load(); validate_start(config)
    from .diagnostics import self_test
    validation = self_test(config, require_native=config['native_hasher'])
    if not validation['ok']:
        raise RuntimeError('Mining startup hash/scanner validation failed: ' + json.dumps(validation))
    engine = Engine(config)
    engine.state['startup_hash_validation'] = validation
    engine.emit('validation', 'Startup hash/scanner checks passed', hasher=validation['hasher'])
    failed = []
    write_summary = [True]
    def mine():
        try:
            engine.run()
        except BaseException as e:
            import traceback
            traceback.print_exc()
            failed.append(str(e)); engine.state["error"] = str(e)
            engine.emit("error",str(e)); engine.stop.set()
    signal.signal(signal.SIGTERM,lambda *_: engine.stop.set())
    signal.signal(signal.SIGINT,lambda *_: engine.stop.set())
    address = socket_path()
    server, control_token = control_transport.listen(address)
    atomic_json(LOGS/"process.json",{"pid":os.getpid(),"root":str(ROOT)})
    thread = threading.Thread(target=mine,name="coordinator")
    thread.start()
    try:
        while thread.is_alive():
            if (LOGS/"stop.request").exists(): engine.stop.set()
            try:
                client,_ = server.accept()
            except socket.timeout:
                continue
            with client:
                client.settimeout(1)
                data = b""
                try:
                    while b"\n" not in data and len(data)<65536:
                        part = client.recv(4096)
                        if not part:
                            break
                        data += part
                    command = parse_control(data)
                    control_transport.authorize(command, control_token)
                    action = command.get("command")
                    if action == "status":
                        reply = {"ok":True,"running":True,**engine.snapshot()}
                    elif action == "stop":
                        write_summary[0] = bool(command.get("summary",True))
                        engine.emit("stop","Stop requested")
                        engine.stop.set()
                        engine.connection.close()
                        reply = {"ok":True,"message":"Stopping BTC miner; session summary will be saved"}
                    elif action == "pause":
                        engine.manual_pause.set()
                        reply = {"ok":True,"message":"Mining paused"}
                    elif action == "resume":
                        engine.manual_pause.clear()
                        reply = {"ok":True,"message":"Manual pause cleared; activity policy still applies"}
                    elif action == 'resource_workers':
                        reply={'ok':True,'message':'Session worker ceiling changed without restarting',
                               'resources':engine.resources.set_worker_ceiling(command.get('workers'))}
                    else:
                        reply = {"ok":False,"error":"Unknown control command"}
                    client.sendall((json.dumps(reply)+"\n").encode())
                except (ValueError,OSError) as e:
                    try:
                        client.sendall((json.dumps({"ok":False,"error":str(e)})+"\n").encode())
                    except OSError:
                        pass
        thread.join()
    finally:
        engine.stop.set(); engine.connection.close()
        server.close()
        if address.exists():
            address.unlink()
        path = engine.summary(desktop=write_summary[0] and not failed)
        engine.emit("stop",f"Session saved · {path}")
        atomic_json(LOGS/"status.json",engine.snapshot())
    return 1 if failed else 0

if __name__ == "__main__":
    raise SystemExit(supervise() if sys.argv[1:] == ["supervise"] else serve())
