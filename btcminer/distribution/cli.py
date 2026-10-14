"""Node tooling. Production coordinator is owned by the normal mining engine."""
import argparse
from ..platform_support import fcntl
import json
import os
from pathlib import Path
import secrets
import signal
import threading
import time

from ..settings import atomic_json
from .buffers import Peer
from .runtime import node_id
from .transport import Client, read_tokens, serve
from .worker import Worker


def main(argv=None):
    parser=argparse.ArgumentParser(prog='btc-miner cluster')
    sub=parser.add_subparsers(dest='action',required=True)
    p=sub.add_parser('init',help='Create per-node credentials; never prints tokens')
    p.add_argument('--auth',required=True); p.add_argument('--node',action='append',required=True)
    p=sub.add_parser('worker',help='Pull partition work and exchange modeled duplex frames')
    p.add_argument('--url',required=True); p.add_argument('--auth',help='Mode-600 node credential file')
    p.add_argument('--state',required=True); p.add_argument('--ca'); p.add_argument('--peer',action='append',default=[])
    p.add_argument('--batch-size',type=int,default=16384); p.add_argument('--seconds',type=float,default=0)
    p.add_argument('--cpu-duty',type=int,default=100)
    p.add_argument('--resource-control');p.add_argument('--resource-session')
    p.add_argument('--no-provider',action='store_true',help='Use exact local model without provider preview calls')
    p=sub.add_parser('fixture-server',help='Isolated public-header fixture; never connects to Core or submits blocks')
    p.add_argument('--auth',required=True); p.add_argument('--state',required=True)
    p.add_argument('--port',type=int,default=0); p.add_argument('--positions',type=int,default=4096)
    p.add_argument('--seconds',type=float,default=0)
    p.add_argument('--wait-peers',type=int,default=0,help='Hold fixture work until this many models are registered')
    p=sub.add_parser('demo',help='Run two separate peers with duplex exchange and server crash recovery')
    p.add_argument('--output',required=True); p.add_argument('--no-provider',action='store_true')
    args=parser.parse_args(argv)
    if args.action=='init':
        if len(set(args.node))!=len(args.node): raise ValueError('Duplicate node IDs')
        path=Path(args.auth); path.parent.mkdir(parents=True,exist_ok=True)
        tokens={node:secrets.token_hex(32) for node in args.node}
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
        with os.fdopen(fd,'w') as handle: json.dump(tokens,handle); handle.write('\n')
        try: read_tokens(path)
        except BaseException:
            path.unlink(); raise
        print(json.dumps(dict(auth=str(path),nodes=args.node)))
        return 0
    if args.action=='demo':
        from .demo import run
        print(json.dumps(run(Path(args.output),provider=not args.no_provider),indent=2))
        return 0
    stop=threading.Event()
    for sig in (signal.SIGINT,signal.SIGTERM): signal.signal(sig,lambda *_:stop.set())
    if args.seconds:
        if not 0<args.seconds<=3600: raise ValueError('Test duration must be within 0..3600 seconds')
        timer=threading.Timer(args.seconds,stop.set); timer.daemon=True; timer.start()
    state=Path(args.state); state.mkdir(parents=True,exist_ok=True)
    with (state/'process.lock').open('a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        if args.action=='worker':
            node=node_id()
            token=read_tokens(args.auth)[node] if args.auth else os.environ.get('BTC_NODE_TOKEN','')
            client=Client(args.url,token,state/'pending.json',ca=args.ca)
            peer=Peer(client,node,state/'buffers',peers=args.peer,provider=not args.no_provider)
            atomic_json(state/'process.json',dict(node_id=node,pid=os.getpid(),state='running'))
            gate=None
            if args.resource_control:
                if not args.resource_session:raise ValueError('Resource control requires the owning session')
                from ..resources import PeerGate
                gate=PeerGate(args.resource_control,args.resource_session,node)
            try: Worker(client,batch_size=args.batch_size,stop=stop,peer=peer,cpu_duty=args.cpu_duty,admission=gate).run()
            finally: atomic_json(state/'process.json',dict(node_id=node,pid=os.getpid(),state='stopped'))
        else:
            from ..diagnostics import GENESIS
            from ..protocol import Work
            from ..thesis2 import Traversal
            from .geometry import job_spec
            from .store import Store
            # target zero is an isolated hashing/transport fixture, not a
            # historical block replay or a network block acceptance test.
            work=Work(GENESIS,0,0,0,'1d00ffff','duplex-fixture',1)
            store=Store(state/'work.sqlite',initial_region=128,max_region=128)
            server=thread=None
            job=store.activate(job_spec(work,Traversal(GENESIS,order='flower')),root_end=args.positions)
            waiting=args.wait_peers>0
            if waiting: store.deactivate(job)
            try:
                server,thread=serve(store,'127.0.0.1',args.port,read_tokens(args.auth))
                atomic_json(state/'ready.json',dict(port=server.server_port,pid=os.getpid(),job=job))
                while not stop.wait(.1):
                    if waiting:
                        with store.lock:
                            count=store.db.execute('SELECT count(*) FROM peer_models').fetchone()[0]
                        if count>=args.wait_peers:
                            store.activate(job_spec(work,Traversal(GENESIS,order='flower')),root_end=args.positions)
                            waiting=False
                    else: store.pulse(job)
            finally:
                store.deactivate(job)
                if server:
                    server.shutdown(); server.server_close(); thread.join(timeout=5)
                atomic_json(state/'final.json',store.stats(job)); store.close()
    return 0
