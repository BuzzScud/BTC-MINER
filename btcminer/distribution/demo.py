"""Two actual peer processes, provider models, duplex frames and hard restart."""
import base64
import json
import os
from pathlib import Path
import secrets
import sqlite3
import subprocess
import sys
import time

from .. import ROOT
from ..settings import atomic_json
from .buffers import MODEL, MODEL_ID
from .transport import Client


def run(folder,provider=True):
    folder=Path(folder).resolve()
    folder.mkdir(parents=True,exist_ok=True)
    if (folder/'auth.json').exists(): raise ValueError('Choose a fresh demo output folder')
    tokens={p:secrets.token_hex(32) for p in ('peer-A','peer-B')}
    atomic_json(folder/'auth.json',tokens)
    children=[];handles=[];server=None
    def start(name,arguments,node=None):
        log=(folder/(name+'.log')).open('a');handles.append(log)
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
        if node:env['BTC_NODE_ID']=node
        process=subprocess.Popen([sys.executable,'-B','-m','btcminer.distribution',*arguments],
            cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
        children.append(process);return process
    def wait_for(check,seconds=30):
        deadline=time.monotonic()+seconds
        while time.monotonic()<deadline:
            if check():return
            time.sleep(.1)
        raise TimeoutError('Isolated peer demo did not reach its expected state')
    def stop(process):
        if process.poll() is None:
            process.terminate()
            try:process.wait(timeout=10)
            except subprocess.TimeoutExpired:process.kill();process.wait(timeout=5)
    def start_server(port=0):
        return start('server',['fixture-server','--auth',str(folder/'auth.json'),
            '--state',str(folder/'coordinator'),'--port',str(port),'--positions','16384','--wait-peers','2'])
    def start_worker(node,other,url,suffix=''):
        return start(node+suffix,['worker','--url',url,'--auth',str(folder/'auth.json'),
            '--state',str(folder/node),'--peer',other,'--batch-size','64']+
            ([] if provider else ['--no-provider']),node)
    try:
        server=start_server()
        ready=folder/'coordinator/ready.json'
        wait_for(ready.exists)
        initial=json.loads(ready.read_text());port=initial['port'];url='http://127.0.0.1:'+str(port)
        clients={p:Client(url,t,folder/(p+'-control-pending.json')) for p,t in tokens.items()}
        a=start_worker('peer-A','peer-B',url);b=start_worker('peer-B','peer-A',url)
        def duplex():
            return all(any((folder/p/'buffers/received'/other).glob('*.json'))
                       for p,other in (('peer-A','peer-B'),('peer-B','peer-A')))
        wait_for(duplex,45)
        wait_for(lambda:clients['peer-A'].call('status').get('complete',False),30)
        stop(a);stop(b)
        marker=base64.b64encode(b'full-duplex retained buffer across hard coordinator restart').decode()
        sent=clients['peer-A'].call('buffer.send',receiver='peer-B',model_id=MODEL_ID,payload=marker)
        before=clients['peer-B'].call('buffer.read',sender='peer-A',after=0)
        server.kill();server.wait(timeout=5)
        oldpid=server.pid
        server=start_server(port)
        wait_for(lambda:json.loads(ready.read_text()).get('pid')!=oldpid)
        after=clients['peer-B'].call('buffer.read',sender='peer-A',after=0)
        if before!=after:raise AssertionError('Unacknowledged buffer changed after crash')
        a=start_worker('peer-A','peer-B',url,'-restart');b=start_worker('peer-B','peer-A',url,'-restart')
        marker_file=folder/'peer-B/buffers/received/peer-A'/(str(sent['sequence'])+'.json')
        wait_for(marker_file.exists,30)
        if json.loads(marker_file.read_text())['payload']!=marker:raise AssertionError('Peer received altered marker')
        stop(a);stop(b)
        status=clients['peer-A'].call('status')
        with sqlite3.connect(folder/'coordinator/work.sqlite') as db:
            rows=db.execute("SELECT start,stop,done,owner FROM regions WHERE state='done' ORDER BY start").fetchall()
            owners={r[3] for r in rows}
            if sum(r[2] for r in rows)!=16384 or any(x[1]>y[0] for x,y in zip(rows,rows[1:])):
                raise AssertionError('Coverage ledger inconsistent')
            if not {'peer-A','peer-B'}<=owners:raise AssertionError('Both peers must execute partition work')
        models={p:json.loads((folder/p/'buffers/model.json').read_text()) for p in tokens}
        if provider and not all(m.get('provider_model_available') for m in models.values()):
            raise AssertionError('Provider model calls did not succeed on both peers; see model receipts')
        report=dict(ok=True,scope='Separate local processes; public-header target-zero fixture, no network submission',
                    candidates=16384,coverage_complete=status['complete'],worker_nodes=sorted(owners),
                    duplex_both_directions=True,unacked_frame_survived_hard_restart=True,
                    received_marker_sequence=sent['sequence'],provider_models=models,
                    protocol_backend='local durable duplex with calculator model previews',
                    coordinator_restarted=True,children=[p.pid for p in children])
        atomic_json(folder/'report.json',report)
        return report
    finally:
        for child in children:stop(child)
        for handle in handles:handle.close()
