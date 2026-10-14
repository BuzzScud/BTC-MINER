import json
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock,patch

from btcminer.resources import Governor,Policy,ResourceController,PeerGate,History
from btcminer.provider_telemetry import TelemetryState,calculation,server_metrics
from btcminer.settings import DEFAULTS,validate
from btcminer.distribution.worker import Worker


def sample(cpu=30,**kwargs):
    return dict(host_cpu_percent=cpu,pressure=1,swap_mib=100,owned_rss_mib=100,peer_rss_mib=40,**kwargs)


class GovernorTests(unittest.TestCase):
    def test_pressure_and_each_memory_cap_latch_stop(self):
        for key,value in [('pressure',2),('owned_rss_mib',4097),('peer_rss_mib',257),('swap_mib',229)]:
            g=Governor(Policy(),now=0);g.update(sample(),0,0)
            s=sample();s[key]=value;g.update(s,10,2)
            self.assertTrue(g.halt,key)
            g.update(sample(),20,1000);self.assertTrue(g.halt)

    def test_missing_cpu_and_missing_local_data_deny_admission(self):
        g=Governor(Policy(),now=0)
        g.update(sample(None),0,0);self.assertFalse(g.available)
        g.update(sample(),1,2);self.assertTrue(g.available)
        g.update(None,2,4);self.assertFalse(g.available);self.assertFalse(g.halt)

    def test_staged_increase_and_failed_throughput_probe_rolls_back(self):
        g=Governor(Policy(),now=0)
        for t in range(0,61,2):g.update(sample(),t*100, t)
        self.assertEqual(g.workers,3)
        for t in range(62,121,2):g.update(sample(),6000+(t-60)*90,t)
        self.assertEqual(g.workers,2);self.assertEqual(g.ceiling,2)
        for t in range(122,300,2):g.update(sample(),t*100,t)
        self.assertEqual(g.workers,2)

    def test_cpu_backoff_and_pause_when_other_load_persists(self):
        g=Governor(Policy(),now=0)
        for t in range(0,100,2):g.update(sample(99),t,t)
        self.assertEqual(g.workers,1);self.assertEqual(g.duty,10)
        self.assertFalse(g.available);self.assertFalse(g.halt)
        g.update(sample(10),101,101);self.assertTrue(g.available)

    def test_clock_gap_resets_probe_window(self):
        g=Governor(Policy(),now=0)
        g.update(sample(),0,0);g.update(sample(),100,1000)
        self.assertEqual(g.workers,2);self.assertEqual(len(g.rate_window),1)

    def test_configuration_rejects_inverted_limits_and_external_overbooking(self):
        for change in [dict(resource_cpu_target=95,resource_cpu_backoff=90),
                       dict(resource_min_workers=6,resource_max_workers=2),
                       dict(resource_external_workers=6),dict(resource_peer_rss_mib=5000),
                       dict(provider_metrics_path='http://other/metrics')]:
            with self.assertRaises(ValueError):validate(dict(DEFAULTS,**change))

    def test_closed_or_stopped_controller_never_readmits_workers(self):
        with tempfile.TemporaryDirectory() as d:
            stop=threading.Event();c=ResourceController(dict(DEFAULTS,resource_control=True),d,stop,lambda:0)
            c.governor.update(sample(),0,time.monotonic());self.assertTrue(c.admission(0)[0])
            stop.set();self.assertFalse(c.admission(0)[0]);c.close()
            stop.clear();self.assertFalse(c.admission(0)[0])

    def test_runtime_manual_ceiling_never_changes_saved_config(self):
        with tempfile.TemporaryDirectory() as d:
            config=dict(DEFAULTS,resource_control=True)
            c=ResourceController(config,d,threading.Event(),lambda:0)
            c.set_worker_ceiling(1);self.assertEqual(c.governor.workers,1)
            self.assertEqual(config['workers'],2)
            with self.assertRaises(ValueError):c.set_worker_ceiling(7)

    def test_peer_gate_rejects_stale_wrong_session_and_halted_state(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'control.json';gate=PeerGate(path,'run','peer')
            self.assertFalse(gate()[0])
            row=dict(schema=1,session='run',updated_at=time.time(),halt=False,slots={'peer':dict(active=True,duty=85)})
            path.write_text(json.dumps(row));self.assertEqual(gate(),(True,85))
            for changes in [dict(session='other'),dict(halt=True),dict(updated_at=time.time()-20)]:
                path.write_text(json.dumps(dict(row,**changes)));self.assertFalse(gate()[0])

    def test_history_rotation_is_bounded(self):
        with tempfile.TemporaryDirectory() as d:
            h=History(Path(d)/'history',max_bytes=90,backups=3)
            for i in range(200):h.append(dict(i=i,value='sample'))
            self.assertLessEqual(len(list(Path(d).iterdir())),4)
            self.assertEqual(h.errors,0)

    def test_denied_worker_recovers_before_releasing_lease_without_scanning(self):
        events=[];client=Mock();client.recover.side_effect=lambda:events.append('recover')
        client.call.side_effect=lambda *a,**k:events.append(a[0])
        w=Worker(client,hasher=Mock(),admission=lambda:(False,50))
        w.assignment=dict(job='job',region=1,epoch=2)
        self.assertFalse(w.step());self.assertEqual(events,['recover','release'])
        w.hasher.scan.assert_not_called();self.assertIsNone(w.assignment)


class ProviderTelemetryTests(unittest.TestCase):
    def value(self,seq=4):
        return dict(requestId='ws-secret-token-1',sequence=seq,timestamp='2026-10-13T21:37:00Z',
                    cost=dict(cpuMs=25,cpuShare=.2,samples=3),progress=dict(percent=100),metrics={})

    def test_no_token_or_false_host_cpu_claim_in_normalized_calculation(self):
        row=calculation(self.value(),source='websocket')
        self.assertNotIn('secret-token',json.dumps(row))
        self.assertEqual(row['scope'],'calculation');self.assertNotIn('host_cpu_percent',row)
        self.assertEqual(row['cpu_ms'],25)

    def test_repeated_rest_ids_are_distinct_observations(self):
        s=TelemetryState()
        a=s.observe_calculation(self.value(),'rest');b=s.observe_calculation(self.value(),'rest')
        self.assertNotEqual(a['observation'],b['observation']);self.assertEqual(s.duplicates,0)

    def test_websocket_duplicates_ordering_and_reconnection(self):
        s=TelemetryState();s.connected();s.observe_calculation(self.value(),'websocket')
        self.assertIsNone(s.observe_calculation(self.value(),'websocket'))
        self.assertIsNone(s.observe_calculation(self.value(3),'websocket'))
        self.assertEqual((s.duplicates,s.out_of_order),(1,1))
        s.connected();self.assertIsNotNone(s.observe_calculation(self.value(1),'websocket'))

    def test_absent_server_data_is_unavailable_and_old_cost_is_stale(self):
        s=TelemetryState();s.observe_calculation(self.value(),'rest',now=0)
        snap=s.snapshot(now=40)
        self.assertEqual(snap['server']['availability'],'unavailable')
        self.assertEqual(snap['calculations']['rest']['availability'],'stale')

    def test_untyped_cost_cannot_be_promoted_to_server_resource(self):
        with self.assertRaises(ValueError):server_metrics(self.value())
        row=calculation(dict(self.value(),cost=dict(cpuMs=float('nan'),cpuShare=200)),source='rest')
        self.assertIsNone(row['cpu_ms']);self.assertIsNone(row['cpu_share'])

    def test_real_server_samples_deduplicate_and_preserve_unknown_queue(self):
        s=TelemetryState()
        row=dict(schema='provider-system-metrics/v1',scope='host',measurement='os-sampled',
            sample_id='one',instance_id='host',sampled_at=100,cpu=dict(percent=20,cores=8,window_seconds=2),
            memory=dict(total_bytes=8192,used_bytes=4096),process={})
        self.assertIsNotNone(s.observe_server(row,now=100))
        self.assertIsNone(s.observe_server(row,now=101))
        self.assertIsNone(s.server['queue_depth'])
        self.assertEqual(s.snapshot(now=140)['server']['availability'],'stale')


if __name__=='__main__':unittest.main()

class ServerMetricsAdapterTests(unittest.IsolatedAsyncioTestCase):
    async def test_authenticated_rest_and_websocket_share_os_sample_identity(self):
        try:
            import aiohttp
            from aiohttp import web
        except ImportError:self.skipTest('optional aiohttp unavailable')
        from btcminer.system_metrics import create_app
        class FixtureCollector:
            latest=None
            def sample(self):
                self.latest=dict(schema='provider-system-metrics/v1',measurement='os-sampled',scope='host',
                    instance_id='fixture',sample_id='fixture:1',sampled_at=time.time(),
                    cpu=dict(percent=35,cores=8,window_seconds=2),memory=dict(total_bytes=8192),process={})
        collector=FixtureCollector();token='fixture-only-not-a-real-secret-123456'
        runner=web.AppRunner(create_app(token,collector));await runner.setup()
        site=web.TCPSite(runner,'127.0.0.1',0);await site.start()
        port=site._server.sockets[0].getsockname()[1];base=f'http://127.0.0.1:{port}'
        try:
            async with aiohttp.ClientSession() as client:
                async with client.get(base+'/api/system/metrics') as response:self.assertEqual(response.status,401)
                headers={'Authorization':'Bearer '+token}
                async with client.get(base+'/api/system/metrics',headers=headers) as response:
                    self.assertEqual(response.status,200);rest=(await response.json())['metrics']
                async with client.ws_connect(base+'/ws/system-metrics',headers=headers) as ws:
                    event=await ws.receive_json(timeout=3)
                    self.assertEqual(event['type'],'systemTelemetry')
                    self.assertEqual(event['metrics']['sample_id'],rest['sample_id'])
                    normalized=server_metrics(event['metrics']);self.assertEqual(normalized['cpu_percent'],35)
        finally:await runner.cleanup()


class WorkerGateIntegrationTests(unittest.TestCase):
    def test_draining_a_worker_returns_unfinished_region_without_overlap(self):
        from btcminer.distribution.store import Store
        from btcminer.distribution.transport import LocalClient
        from btcminer.distribution.geometry import job_spec
        from btcminer.protocol import Work
        from btcminer.diagnostics import GENESIS
        from btcminer.thesis2 import Traversal
        from btcminer.native import Hasher
        with tempfile.TemporaryDirectory() as directory:
            store=Store(Path(directory)/'db',initial_region=64,max_region=64)
            try:
                work=Work(GENESIS,0,0,0,'','offline-gate-fixture',1)
                job=store.activate(job_spec(work,Traversal(GENESIS,order='flower')),root_end=64)
                permit=[True];worker=Worker(LocalClient(store,'A'),hasher=Hasher(False),batch_size=16,
                    admission=lambda:(permit[0],100))
                worker.step();first=store.stats(job)['hashed'];self.assertEqual(first,16)
                permit[0]=False;self.assertFalse(worker.step());self.assertIsNone(worker.assignment)
                replacement=Worker(LocalClient(store,'B'),hasher=Hasher(False),batch_size=16)
                while not store.stats(job)['complete']:replacement.step()
                self.assertEqual(store.stats(job)['hashed'],64)
                rows=store.db.execute('SELECT start,stop FROM progress ORDER BY start').fetchall()
                self.assertTrue(all(a['stop']<=b['start'] for a,b in zip(rows,rows[1:])))
            finally:store.close()
