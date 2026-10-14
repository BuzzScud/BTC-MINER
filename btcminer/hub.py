"""Launch the local Algorithm Observatory without changing miner lifecycle.

LIVE-01: start in --no-fixture mode, bind loopback only, and verify server/root
identity before reuse. This launcher is independent of service.start/stop.
See MASTER_PLAN.md and the Observatory's CONTRACTS.md (LIVE-01, RATE-01).
"""
from .platform_support import fcntl
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import urllib.error
import urllib.request
from . import ROOT
from .settings import LOGS, atomic_json


class LocalOnly(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, message, headers, new_url):
        return None


def locate(path=None):
    explicit = path or os.environ.get('BTC_OBSERVATORY_ROOT')
    candidates = [Path(explicit).expanduser()] if explicit else [
        ROOT/'observatory', ROOT.parent/'bitcoin-algorithm-observatory-2026-10-07',
        ROOT.parent.parent/'bitcoin-algorithm-observatory-2026-10-07']
    for folder in candidates:
        if (folder/'observatory_server.py').is_file() and (folder/'index.html').is_file():
            return folder.resolve()
    raise ValueError('Observatory not found. Use /hub --path /path/to/observatory or set BTC_OBSERVATORY_ROOT.')


def health(port, folder):
    if type(port) is not int or not 1024 <= port <= 65535:
        return None
    try:
        request = urllib.request.Request(f'http://127.0.0.1:{port}/health')
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), LocalOnly())
        with opener.open(request, timeout=.4) as response:
            result = json.loads(response.read(8192))
        if (result.get('service') == 'btc-observatory' and
                result.get('miner_root') == str(ROOT.resolve()) and
                result.get('observatory_root') == str(folder) and
                result.get('start_fixture') is False):
            return result
    except (OSError, ValueError, urllib.error.URLError, AttributeError):
        pass
    return None


def ensure_server(folder, preferred_port=63218):
    LOGS.mkdir(parents=True, exist_ok=True)
    with (LOGS/'hub.lock').open('a') as lock:
        deadline = time.monotonic()+12
        while True:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB); break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise ValueError('Hub startup is still in progress; try /hub again.')
                time.sleep(.05)
        try:
            saved = json.loads((LOGS/'hub.json').read_text()).get('port')
        except (OSError, ValueError, AttributeError):
            saved = None
        for port in dict.fromkeys([saved, preferred_port]):
            if health(port, folder):
                return port, False
        with socket.socket() as probe:
            try:
                probe.bind(('127.0.0.1', preferred_port))
            except OSError:
                probe.bind(('127.0.0.1', 0))
            port = probe.getsockname()[1]
        env = dict(os.environ, BTC_MINER_ROOT=str(ROOT.resolve()), PYTHONDONTWRITEBYTECODE='1')
        with (LOGS/'hub-server.log').open('ab') as output:
            process = subprocess.Popen([sys.executable, '-B', str(folder/'observatory_server.py'),
                                        '--no-fixture', '--port', str(port)], cwd=folder,
                                       env=env, stdin=subprocess.DEVNULL, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        deadline = time.monotonic()+10
        while time.monotonic() < deadline and process.poll() is None:
            if health(port, folder):
                atomic_json(LOGS/'hub.json', dict(port=port, pid=process.pid, root=str(folder)))
                return port, True
            time.sleep(.1)
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill(); process.wait(timeout=2)
        raise ValueError('Hub could not start. Check logs/hub-server.log; its Python environment needs aiohttp.')


def launch(path=None, open_browser=True, port=63218):
    folder = locate(path)
    if not 1024 <= port <= 65535:
        raise ValueError('Hub port must be between 1024 and 65535.')
    port, started = ensure_server(folder, port)
    url = f'http://127.0.0.1:{port}/#live-miner-study'
    opened = False
    if open_browser:
        try:
            opened = subprocess.run(['/usr/bin/open', url], stdin=subprocess.DEVNULL,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                    timeout=5).returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            pass
    return dict(ok=True, url=url, started=started, browser_opened=opened,
                message=('Hub opened: ' if opened else 'Hub ready: ')+url)
