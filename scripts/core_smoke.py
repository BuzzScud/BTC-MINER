"""One accepted block on an isolated, disconnected regtest node. Never use a live datadir."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import time

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from btcminer.settings import DEFAULTS
from btcminer.rpc import RPC
from btcminer.engine import Engine

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--bitcoind',required=True);args=p.parse_args()
    with tempfile.TemporaryDirectory(prefix='btc private block ') as directory:
        folder=Path(directory);node=folder/'node';node.mkdir()
        with socket.socket() as reserve:reserve.bind(('127.0.0.1',0));port=reserve.getsockname()[1]
        config=dict(DEFAULTS,network='regtest',rpc_datadir=str(node),rpc_port=port,
                    workers=1,pause_on_active=0,keep_awake=False,provider_enabled=False,
                    resource_control=False,stop_after_block=True,run_seconds=20,
                    nonce_log=False,supt_log=False,observatory_telemetry=False)
        rpc=RPC(config)
        with (folder/'core.log').open('w') as output:
            process=subprocess.Popen([str(Path(args.bitcoind).resolve()),'-regtest',f'-datadir={node}',
                '-server=1',f'-rpcport={port}','-listen=0','-discover=0','-dnsseed=0','-connect=0',
                '-networkactive=0','-fallbackfee=0.0002'],stdout=output,stderr=output)
        try:
            deadline=time.monotonic()+30
            while True:
                try:rpc.call('getblockchaininfo',timeout=1);break
                except Exception:
                    if process.poll() is not None or time.monotonic()>deadline:raise RuntimeError('Private Core startup failed')
                    time.sleep(.1)
            rpc.call('createwallet',['smoke']);config['address']=rpc.call('getnewaddress')
            # Coinbase funding blocks are node-generated fixtures, not miner results.
            rpc.call('generatetoaddress',[101,config['address']])
            recipient=rpc.call('getnewaddress');txid=rpc.call('sendtoaddress',[recipient,1])
            engine=Engine(config,logs=folder/'logs');engine.run()
            snapshot=engine.snapshot()
            if snapshot['blocks_accepted']!=1:raise RuntimeError('Expected exactly one accepted miner block')
            info=rpc.call('getblockchaininfo');block=rpc.call('getblock',[info['bestblockhash'],2])
            raw=bytes.fromhex(rpc.call('getblock',[info['bestblockhash'],0]))
            digest=hashlib.sha256(hashlib.sha256(raw[:80]).digest()).digest()[::-1].hex()
            assert digest==block['hash'] and block['height']==102
            assert txid in [tx['txid'] for tx in block['tx']]
            assert rpc.call('verifychain',[4,0]) is True
            print(json.dumps({'ok':True,'accepted_miner_blocks':1,'height':block['height'],
                'signed_transaction_included':True,'verifychain_level4':True,'sha256d_verified':True,
                'scope':'Disconnected disposable regtest; 101 funding fixtures excluded; stopped after first accepted miner block'}))
        finally:
            try:rpc.call('stop',timeout=2)
            except Exception:pass
            try:process.wait(10)
            except subprocess.TimeoutExpired:process.terminate();process.wait(10)

if __name__=='__main__':main()
