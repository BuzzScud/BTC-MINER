import base64
from contextlib import ExitStack
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import Mock, patch

from btcminer.diagnostics import GENESIS
from btcminer.distribution.buffers import MODEL, MODEL_ID, Peer, frame_geometry
from btcminer.distribution.geometry import Geometry, END, WIDTH, children, implementation, job_spec
from btcminer.distribution.store import Store, Rejected
from btcminer.distribution.transport import Client, LocalClient, TransportError, serve, strict_json
from btcminer.distribution.worker import Worker
from btcminer.native import Hasher, hash256
from btcminer.protocol import Work
from btcminer.thesis2 import Traversal


class GeometryTests(unittest.TestCase):
    def test_full_coverage_and_partial_tile_cardinality(self):
        for order in ('field','flower'):
            g=Geometry(Traversal(GENESIS,order=order))
            self.assertEqual(g.count(0,END),1<<32)
            a=g.partial_start
            self.assertEqual(g.count(a,a+WIDTH),23296)
            self.assertEqual(len({g.nonce(i) for i in range(a,a+WIDTH)}-{None}),23296)
            for nonce in (0,1,4294967295,2083236893,144000,144001):
                self.assertEqual(g.nonce(g.raw_index(nonce)),nonce)

    def test_recursive_split_disjoint_and_exhaustive(self):
        regions=[(0,END)]; seen=set()
        # Follow all branches of one tile and sampled branches of the tile tree.
        for _ in range(16):
            a,b=regions.pop(0); parts=children(a,b)
            self.assertEqual(parts[0][0],a);self.assertEqual(parts[-1][1],b)
            self.assertEqual(sum(y-x for x,y in parts),b-a)
            self.assertTrue(all(x[1]==y[0] for x,y in zip(parts,parts[1:])))
            regions.extend(parts)
        queue=[(0,WIDTH)]
        while queue:
            a,b=queue.pop()
            parts=children(a,b)
            if parts: queue.extend(parts)
            else:
                self.assertNotIn(a,seen);seen.add(a)
        self.assertEqual(seen,set(range(WIDTH)))

    def test_native_and_python_seek_agree_without_crossing_partial_boundary(self):
        native=Hasher(); python=Hasher(False)
        for order in ('field','flower'):
            g=Geometry(Traversal(GENESIS,order=order)); a=g.partial_start
            for start,stop in ((0,17),(a-17,a+17),(a,a+WIDTH),(a+WIDTH-9,a+WIDTH+9),(END-19,END)):
                expected=[g.nonce(i) for i in range(start,stop) if g.nonce(i) is not None]
                for h in (native,python):
                    cursor=start; actual=[]
                    while cursor<stop:
                        values,end=g.batch(h,cursor,stop,127)
                        self.assertGreater(end,cursor);self.assertLessEqual(end,stop)
                        actual.extend(values);cursor=end
                    self.assertEqual(actual,expected)

    def test_job_binding_rejects_target_and_descriptor_tampering(self):
        plan=Traversal(GENESIS); spec=job_spec(Work(GENESIS,0,0,0,'','test',1),plan)
        for key,value in [('target','1'),('descriptor','00'*24),('first_tile',0),('implementation','bad')]:
            changed=dict(spec,**{key:value})
            with self.assertRaises(ValueError):Geometry.from_spec(changed)

    def test_refinement_conserves_valid_mass_across_clipped_tile(self):
        g=Geometry(Traversal(GENESIS,order='flower'))
        queue=[(0,END),(g.partial_start,g.partial_start+WIDTH)]
        for _ in range(500):
            if not queue:break
            a,b=queue.pop(0);parts=children(a,b)
            if parts:
                self.assertEqual(sum(g.count(x,y) for x,y in parts),g.count(a,b))
                queue.extend(parts)


class LedgerTests(unittest.TestCase):
    def setUp(self):
        self.folder=tempfile.TemporaryDirectory();self.addCleanup(self.folder.cleanup)
        self.now=[1000.0];self.clock=lambda:self.now[0]
        self.path=Path(self.folder.name)/'work.sqlite'
        self.store=Store(self.path,initial_region=16,max_region=64,clock=self.clock)
        self.addCleanup(lambda:self.store.close())
        self.plan=Traversal(GENESIS,order='flower')
        self.spec=job_spec(Work(GENESIS,0,0,0,'','test',1),self.plan)
        self.job=self.store.activate(self.spec,root_end=128)
        self.a=LocalClient(self.store,'A');self.b=LocalClient(self.store,'B')

    def claim(self,client=None):return (client or self.a).call('claim',implementation=implementation())['assignment']
    def commit(self,lease,start=None,end=None,hits=None,client=None):
        start=lease['start'] if start is None else start
        end=lease['stop'] if end is None else end
        return (client or self.a).call('commit',job=self.job,region=lease['region'],epoch=lease['epoch'],
            start=start,cursor=end,hashes=self.store.geometry(self.job).count(start,end),hits=hits or [],seconds=.1)

    def test_concurrent_claims_never_overlap(self):
        with ThreadPoolExecutor(8) as pool:
            leases=list(pool.map(lambda i:self.claim(LocalClient(self.store,'N'+str(i))),range(8)))
        intervals=sorted((x['start'],x['stop']) for x in leases if x)
        self.assertTrue(all(x[1]<=y[0] for x,y in zip(intervals,intervals[1:])))
        self.assertEqual(sum(y-x for x,y in intervals),128)

    def test_expired_lease_reclaims_only_unfinished_prefix(self):
        lease=self.claim();mid=lease['start']+3
        self.commit(lease,end=mid)
        self.now[0]+=16;self.store.pulse(self.job)
        newer=self.claim(self.b)
        self.assertEqual(newer['start'],mid)
        with self.assertRaisesRegex(Rejected,'stale_lease'):self.commit(lease,start=mid)
        self.assertEqual(self.store.stats()['hashed'],3)

    def test_restart_preserves_progress_and_fences_previous_owner(self):
        lease=self.claim();self.commit(lease,end=lease['start']+5)
        self.store.close();self.store=Store(self.path,initial_region=16,max_region=64,clock=self.clock)
        self.store.activate(self.spec,root_end=128);self.b=LocalClient(self.store,'B')
        newer=self.claim(self.b)
        self.assertEqual(newer['start'],5)
        with self.assertRaisesRegex(Rejected,'stale_lease'):
            LocalClient(self.store,'A').call('heartbeat',job=self.job,region=lease['region'],epoch=lease['epoch'])

    def test_exact_retry_and_conflicting_retry(self):
        req=dict(action='claim',op='same',implementation=implementation())
        first=self.store.operation('A',req)
        self.assertEqual(first,self.store.operation('A',req))
        with self.assertRaisesRegex(Rejected,'operation_conflict'):
            self.store.operation('A',dict(action='status',op='same'))

    def test_wrong_owner_and_wrong_generation_rejected(self):
        lease=self.claim()
        with self.assertRaisesRegex(Rejected,'stale_lease'):self.commit(lease,client=self.b)
        replacement=dict(self.spec);replacement['target']='1'
        from btcminer.distribution.geometry import canonical
        replacement['id']=hashlib.sha256(canonical({k:v for k,v in replacement.items() if k!='id'}).encode()).hexdigest()
        self.store.activate(replacement,root_end=128)
        with self.assertRaisesRegex(Rejected,'stale_job'):self.commit(lease)

    def test_coordinator_heartbeat_expiry_stops_assignment(self):
        self.now[0]+=4
        self.assertIsNone(self.claim())

    def test_bad_hash_or_outside_region_does_not_commit_progress(self):
        lease=self.claim();g=self.store.geometry(self.job)
        for nonce in (g.nonce(lease['start']),g.nonce(lease['stop']+1)):
            with self.assertRaises(Rejected):self.commit(lease,hits=[nonce])
        self.assertEqual(self.store.stats()['hashed'],0)

    def test_exclusions_split_region_and_preserve_all_unresolved_candidates(self):
        region=self.store.proof_region(self.job,8);g=self.store.geometry(self.job)
        removed=[g.nonce(region['start']),g.nonce(region['stop']-1)]
        self.assertEqual(self.store.exclude(self.job,region['id'],removed),2)
        seen=[]
        class RecordingHasher(Hasher):
            def scan(inner,header,target,**kwargs):
                seen.extend(kwargs['nonces']);return len(kwargs['nonces']),None
        worker=Worker(self.a,hasher=RecordingHasher(False),batch_size=7)
        while not self.store.stats()['complete']:worker.step()
        self.assertEqual(set(seen),{g.nonce(i) for i in range(128)}-set(removed))
        self.assertEqual(len(seen),126)
        self.assertEqual(self.store.stats()['excluded'],2)

    def test_false_exclusion_rolls_back_whole_proposal(self):
        high=job_spec(Work(GENESIS,(1<<256)-1,0,0,'','test',2),self.plan)
        self.job=self.store.activate(high,root_end=128)
        region=self.store.proof_region(self.job,8);g=self.store.geometry(self.job)
        with self.assertRaisesRegex(Rejected,'exclusion_contains_winner'):
            self.store.exclude(self.job,region['id'],[g.nonce(region['start'])])
        self.assertEqual(self.store.stats()['excluded'],0)

    def test_full_hit_sequence_preserves_tail_and_outbox(self):
        self.job=self.store.activate(job_spec(Work(GENESIS,(1<<256)-1,0,0,'','test',2),self.plan),root_end=7)
        worker=Worker(self.a,hasher=Hasher(False),batch_size=7)
        while not self.store.stats()['complete']:worker.step()
        seen=[]
        while True:
            n=self.store.take_hit(self.job)
            if n is None:break
            seen.append(n);self.store.finish_hit(self.job,n,{'accepted':True})
        self.assertEqual(len(seen),7)
        self.assertEqual(self.store.stats()['hashed'],7)

    def test_ambiguous_submission_is_not_replayed_after_restart(self):
        self.store.db.execute("INSERT INTO hits VALUES(?,1,'0','sending',NULL)",(self.job,))
        self.store.activate(self.spec,root_end=128)
        self.assertIsNone(self.store.take_hit(self.job))
        self.assertEqual(self.store.db.execute('SELECT status FROM hits').fetchone()[0],'unknown')

    def test_observed_node_speed_changes_region_size(self):
        first=self.claim();self.commit(first)
        self.store.db.execute("INSERT OR REPLACE INTO nodes VALUES('A',100000)")
        fast=self.claim();self.assertGreater(fast['stop']-fast['start'],first['stop']-first['start'])

    def test_progress_cannot_skip_or_invent_hash_count(self):
        lease=self.claim()
        with self.assertRaisesRegex(Rejected,'progress_conflict'):self.commit(lease,start=lease['start']+1)
        with self.assertRaisesRegex(Rejected,'invalid_count'):
            self.a.call('commit',job=self.job,region=lease['region'],epoch=lease['epoch'],
                        start=lease['start'],cursor=lease['stop'],hashes=999,hits=[],seconds=1)


class BufferTests(unittest.TestCase):
    def setUp(self):
        LedgerTests.setUp(self)
        for client in (self.a,self.b):client.call('model.publish',model=MODEL,provenance={'backend':'test'})

    def send(self,client,receiver,payload=b'hello'):
        return client.call('buffer.send',receiver=receiver,model_id=MODEL_ID,payload=base64.b64encode(payload).decode())

    def test_full_duplex_has_independent_credit_and_ack(self):
        for _ in range(16):self.send(self.a,'B')
        with self.assertRaisesRegex(Rejected,'no_credit'):self.send(self.a,'B')
        self.send(self.b,'A',b'reply')
        self.assertEqual(len(self.a.call('buffer.read',sender='B',after=0)['frames']),1)
        frames=self.b.call('buffer.read',sender='A',after=0)['frames']
        self.assertEqual(len(frames),16)
        self.b.call('buffer.ack',sender='A',sequence=1)
        receipt=self.send(self.a,'B',b'reused-slot')
        self.assertEqual((receipt['sequence'],receipt['slot']),(17,0))
        self.assertEqual(len(self.b.call('buffer.read',sender='A',after=0)['frames']),16)

    def test_ack_loss_retry_never_recreates_consumed_frame(self):
        request=dict(action='buffer.send',op='send-once',receiver='B',model_id=MODEL_ID,
                     payload=base64.b64encode(b'immutable').decode())
        first=self.store.operation('A',request)
        self.b.call('buffer.ack',sender='A',sequence=1)
        self.assertEqual(self.store.operation('A',request),first)
        self.assertEqual(self.b.call('buffer.read',sender='A',after=0)['frames'],[])

    def test_wrong_model_and_unknown_receiver_rejected(self):
        with self.assertRaisesRegex(Rejected,'model_mismatch'):
            self.a.call('model.publish',model=dict(MODEL,slots=17),provenance={})
        with self.assertRaisesRegex(Rejected,'peer_model_unavailable'):self.send(self.a,'C')

    def test_frame_survives_restart_with_identical_bytes(self):
        self.send(self.a,'B',b'\x00\xffopaque')
        before=self.b.call('buffer.read',sender='A',after=0)
        self.store.close();self.store=Store(self.path,clock=self.clock)
        after=LocalClient(self.store,'B').call('buffer.read',sender='A',after=0)
        self.assertEqual(before,after)

    def test_all_buffer_bytes_have_unique_exact_rod_addresses(self):
        from math import prod
        self.assertEqual(prod(MODEL['rods']),MODEL['rod_capacity'])
        seen=set()
        for address in range(MODEL['byte_capacity']):
            residues=tuple(address%r for r in MODEL['rods'])
            self.assertNotIn(residues,seen);seen.add(residues)
            self.assertEqual(sum(r*w for r,w in zip(residues,(122625,64000,101376)))%144000,address)
        self.assertNotEqual(frame_geometry('A','B',1,1)['lane'],frame_geometry('B','A',1,1)['lane'])

    def test_receiver_cannot_ack_another_receivers_lane(self):
        self.send(self.a,'B')
        with self.assertRaisesRegex(Rejected,'invalid_cursor'):
            LocalClient(self.store,'C').call('buffer.ack',sender='A',sequence=1)
        self.assertEqual(len(self.b.call('buffer.read',sender='A',after=0)['frames']),1)

    def test_peer_validates_node_id_and_retains_received_frame_before_ack(self):
        with self.assertRaisesRegex(ValueError,'peer ID'):
            Peer(self.a,'A',self.folder.name,peers=['../escape'])
        self.send(self.a,'B',b'hello')
        peer=Peer(self.b,'B',Path(self.folder.name)/'peer',peers=['A'],provider=False)
        peer.initialize();peer.tick({'state':'test'})
        self.assertTrue((peer.folder/'received/A/1.json').exists())
        self.assertEqual(self.b.call('buffer.read',sender='A',after=0)['frames'],[])


class TransportTests(unittest.TestCase):
    def test_authenticated_real_http_worker_and_retry_journal(self):
        with tempfile.TemporaryDirectory() as folder, ExitStack() as cleanup:
            store=Store(Path(folder)/'db'); cleanup.callback(store.close)
            server,thread=serve(store,'127.0.0.1',0,{'A':'a'*64})
            cleanup.callback(lambda:(server.shutdown(),server.server_close(),thread.join()))
            url='http://127.0.0.1:'+str(server.server_port)
            client=Client(url,'a'*64,Path(folder)/'journal.json')
            reply=client.call('model.publish',model=MODEL,provenance={})
            self.assertEqual(reply['node_id'],'A');self.assertFalse(client.journal.exists())
            bad=Client(url,'b'*64,Path(folder)/'bad.json')
            with self.assertRaisesRegex(Rejected,'unauthenticated'):bad.call('status')
            self.assertFalse(bad.journal.exists())
            request=dict(action='status',op='uncertain')
            from btcminer.settings import atomic_json
            atomic_json(client.journal,{'binding':client.binding,'request':request})
            self.assertEqual(client.recover(),{'active':False})
            self.assertFalse(client.journal.exists())

    def test_remote_plaintext_and_malformed_json_rejected(self):
        with self.assertRaisesRegex(ValueError,'HTTPS'):Client('http://example.com','a'*64,'unused')
        for raw in ('{"x":1,"x":2}','{"x":NaN}','['*2000):
            with self.assertRaises(ValueError):strict_json(raw)

    def test_malformed_http_framing_cannot_publish(self):
        import socket
        with tempfile.TemporaryDirectory() as folder, ExitStack() as cleanup:
            store=Store(Path(folder)/'db');cleanup.callback(store.close)
            server,thread=serve(store,'127.0.0.1',0,{'A':'a'*64})
            cleanup.callback(lambda:(server.shutdown(),server.server_close(),thread.join()))
            for framing in ('Content-Length: 2\r\nContent-Length: 2\r\n',
                            'Content-Length: 2\r\nTransfer-Encoding: chunked\r\n'):
                with socket.create_connection(('127.0.0.1',server.server_port),timeout=3) as stream:
                    stream.sendall(('POST /v1/work HTTP/1.1\r\nHost: localhost\r\nAuthorization: Bearer '+
                        'a'*64+'\r\n'+framing+'\r\n{}').encode())
                    self.assertIn(b'400',stream.recv(4096).split(b'\r\n')[0])
            self.assertEqual(store.db.execute('SELECT count(*) FROM receipts').fetchone()[0],0)


class EngineDistributionTests(unittest.TestCase):
    def test_production_adapter_stops_after_first_simulated_accepted_block(self):
        from btcminer.engine import Engine
        from btcminer.settings import DEFAULTS
        with tempfile.TemporaryDirectory() as folder, patch.dict(os.environ):
            config=dict(DEFAULTS,native_hasher=False,pause_on_active=0,supt_log=False,nonce_log=False,
                        keep_awake=False,stop_after_block=True,workers=2,pruning_enabled=False,
                        distribution_enabled=True,distribution_port=0,provider_enabled=False)
            engine=Engine(config,logs=Path(folder))
            engine.connection=Mock(label='local fixture',connected=True);engine.connection.valid.return_value=True
            engine.connection.submit.return_value=(True,'simulated accepted block',True)
            work=Work(GENESIS,(1<<256)-1,(1<<256)-1,0,'','fixture',1)
            try:
                # Exercise status serialization even when the first batch wins
                # before the coordinator's normal periodic tick.
                engine.tick()
                with ThreadPoolExecutor(2) as executor:engine.round(executor,work)
                self.assertEqual(engine.state['blocks_accepted'],1)
                self.assertEqual(engine.connection.submit.call_count,1)
                self.assertTrue(engine.stop.is_set())
                self.assertGreaterEqual(engine.state['distribution']['hashed'],1)
            finally:
                if engine.distributor:engine.distributor.close()
                engine.model_telemetry.close();engine.pruner.close()
