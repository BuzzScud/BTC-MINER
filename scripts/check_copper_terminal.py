#!/usr/bin/env python3
"""Exercise Copper in a fixture-backed PTY without accessing a mining service."""
import datetime
import hashlib
import fcntl
import json
import os
from pathlib import Path
import pty
import select
import signal
import struct
import subprocess
import sys
import termios
import time

ROOT=Path(__file__).resolve().parents[1]
runner=r'''
import signal,sys,tempfile,termios
from pathlib import Path
from unittest.mock import patch
from btcminer.settings import DEFAULTS
from btcminer.tui import App
def forbidden(*args,**kwargs):
    raise AssertionError('Lifecycle commands must not run in this UI smoke check')
before=termios.tcgetattr(sys.stdin.fileno())
handlers={s:signal.getsignal(s) for s in (signal.SIGHUP,signal.SIGTERM)}
with tempfile.TemporaryDirectory() as folder:
    with patch('btcminer.tui.LOGS',Path(folder)), patch('btcminer.tui.CONFIG',Path(folder)/'missing.json'), patch('btcminer.tui.load',return_value=dict(DEFAULTS,network='testnet4')), patch('btcminer.tui.service.status',return_value={'state':'MINING','running':True,'rates':{'10':4820000},'shares_accepted':12}), patch('btcminer.tui.memory',return_value='mem 3.1 GB available / 8 GB'):
        app=App()
        app.execute=forbidden
        app.open_hub=lambda args: app.note('HUB_LAUNCH_CHECKED')
        app.loop()
after=termios.tcgetattr(sys.stdin.fileno())
# PENDIN is kernel-owned pending-input bookkeeping, not a UI mode flag.
after[3] &= ~getattr(termios,'PENDIN',0)
before[3] &= ~getattr(termios,'PENDIN',0)
assert after==before,repr((before,after))
assert all(signal.getsignal(s)==h for s,h in handlers.items()),'signal handlers not restored'
print('PTY_CHECK_OK',flush=True)
'''
results=[]
for exit_mode in ('q','Ctrl+C','SIGHUP','SIGTERM'):
    master,slave=pty.openpty()
    fcntl.ioctl(slave,termios.TIOCSWINSZ,struct.pack('HHHH',36,110,0,0))
    proc=subprocess.Popen([sys.executable,'-B','-c',runner],cwd=ROOT,stdin=slave,stdout=slave,stderr=slave,start_new_session=True)
    output=bytearray()
    def wait_for(marker,start=0):
        deadline=time.monotonic()+8
        while time.monotonic()<deadline:
            if marker in output[start:]: return
            if select.select([master],[],[],.1)[0]:
                try: block=os.read(master,65536)
                except OSError: block=b''
                output.extend(block)
                if not block: break
        raise AssertionError(f'{exit_mode}: missing {marker!r}: '+output[-1500:].decode(errors='replace'))
    try:
        wait_for(b'ENGINE / STRATEGY')
        assert b'\x1b]11;#201e1b\x07' in output
        begin=len(output);os.write(master,b'/');wait_for(b'Commands',begin)
        os.write(master,b'\x1b');time.sleep(.08)
        begin=len(output);os.write(master,b'/help\r');wait_for(b'Guided Core',begin)
        os.write(master,b'\x1b');time.sleep(.08)
        begin=len(output);os.write(master,b'f');wait_for(b'DISPLAY FROZEN',begin)
        os.write(master,b'f')
        begin=len(output);os.write(master,b'/HUB\r');wait_for(b'HUB_LAUNCH_CHECKED',begin)
        fcntl.ioctl(slave,termios.TIOCSWINSZ,struct.pack('HHHH',24,80,0,0))
        begin=len(output);wait_for(b'unknown outcomes',begin)
        fcntl.ioctl(slave,termios.TIOCSWINSZ,struct.pack('HHHH',45,140,0,0))
        begin=len(output);wait_for(b'ENGINE / STRATEGY',begin)
        if exit_mode in ('SIGHUP','SIGTERM'): proc.send_signal(getattr(signal,exit_mode))
        else: os.write(master,b'q' if exit_mode=='q' else b'\x03')
        wait_for(b'PTY_CHECK_OK')
        assert proc.wait(timeout=5)==0
        for sequence in (b'\x1b[?25h',b'\x1b[?7h',b'\x1b[?1049l',b'\x1b]111\x07'):
            assert sequence in output,sequence
        results.append({'exit':exit_mode,'palette':True,'help':True,'display_freeze':True,'hub_routing':True,'resize_80x24_and_140x45':True,'terminal_and_signal_restoration':True,'lifecycle_calls':0})
    finally:
        if proc.poll() is None: proc.kill();proc.wait()
        os.close(master);os.close(slave)
report={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                         for name in ('btcminer/tui.py','btcminer/copper.py','btcminer/ui_support.py','scripts/check_copper_terminal.py')},
        'fixture_only':True,'cases':results,'ok':True}
(ROOT/'validation/copper').mkdir(parents=True,exist_ok=True)
(ROOT/'validation/copper/pty-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
