"""Exercise actual Hub HTTP startup/reuse with isolated miner logs and no browser.

LIVE-01: symlink source code for import only; observations use fixture files in
a temporary root. No service controls, Core RPC, provider calls or mining work.
"""
import json
import os
from pathlib import Path
import signal
import socket
import sys
import tempfile
import time
import urllib.request
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from btcminer import hub

def main():
    folder=hub.locate();pid=None
    with tempfile.TemporaryDirectory(prefix='copper hub ') as temporary:
        root=Path(temporary).resolve();logs=root/'logs';logs.mkdir()
        (root/'btcminer').symlink_to(ROOT/'btcminer',target_is_directory=True)
        (logs/'status.json').write_text(json.dumps(dict(state='STOPPED',network='regtest',hashes=123,
                                                      blocks_accepted=0,shares_accepted=0)))
        with socket.socket() as occupied:
            occupied.bind(('127.0.0.1',0));occupied.listen(1)
            port=occupied.getsockname()[1]
            try:
                with patch.object(hub,'ROOT',root),patch.object(hub,'LOGS',logs):
                    first=hub.launch(folder,False,port)
                    receipt=json.loads((logs/'hub.json').read_text());pid=receipt['pid']
                    second=hub.launch(folder,False,port)
                    assert first['started'] and not second['started']
                    assert first['url']==second['url']
                    assert receipt['port']!=port
                    base=first['url'].split('/#')[0]
                    with urllib.request.urlopen(base+'/state',timeout=4) as response:
                        state=json.load(response)
                    assert state['status']=='idle',state['status']
                    assert state['live_miner']['counters']['hashes']=='123'
                    assert state['live_miner']['control']=='read_only'
                    with urllib.request.urlopen(base,timeout=4) as response:
                        assert b'live-miner-study' in response.read()
                    report=dict(ok=True,fixture_only=True,reused_server=True,occupied_port_fallback=True,
                                synthetic_study_started=False,live_hashes=state['live_miner']['counters']['hashes'])
            finally:
                if pid:
                    try:os.kill(pid,signal.SIGTERM)
                    except ProcessLookupError:pass
                    # The child belongs to this test launcher; reap it before temp cleanup.
                    deadline=time.monotonic()+5
                    while time.monotonic()<deadline:
                        try:
                            waited,_=os.waitpid(pid,os.WNOHANG)
                            if waited:break
                        except ChildProcessError:break
                        time.sleep(.05)
    out=ROOT/'validation/copper';out.mkdir(exist_ok=True)
    (out/'hub-check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__':main()
