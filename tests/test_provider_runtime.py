import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

from btcminer.provider_runtime import ProviderRuntime, check_job, job_descriptor
from btcminer.provider import save_snapshot
from btcminer.protocol import Work
from btcminer.diagnostics import GENESIS
from btcminer.thesis2 import Traversal


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.runtime = ProviderRuntime({'provider_enabled': True}, temp.name)
        self.work = Work(GENESIS, 1, 1, 900000, '207fffff', 'fixture', 1)
        self.plan = Traversal(GENESIS, order='flower')

    def test_job_math_exact_match_and_mismatch(self):
        job = job_descriptor(self.work, self.plan, 'session')
        client = Mock()
        client.calculate.return_value = {'evaluation': {'ok': True, 'value': str(job['offset'])}}
        self.assertTrue(check_job(client, job)['matched'])
        client.calculate.return_value = {'evaluation': {'ok': True, 'value': str(job['offset']+1), 'certified': True}}
        self.assertFalse(check_job(client, job)['matched'])

    def test_descriptor_rejects_invalid_inputs_before_request(self):
        client = Mock()
        for change in ({'cell': -1}, {'label': '2+evil'}, {'phase': 144000}, {'offset': -1}):
            job = dict(job_descriptor(self.work, self.plan, 'session'), **change)
            with self.assertRaises(ValueError):
                check_job(client, job)
        client.calculate.assert_not_called()

    def test_disabled_runtime_never_spawns_or_writes(self):
        self.runtime.enabled = False
        with patch('btcminer.provider_runtime.subprocess.Popen') as spawn:
            self.runtime.start()
            self.runtime.observe(self.work, self.plan)
            self.runtime.close()
            spawn.assert_not_called()
        self.assertEqual(self.runtime.snapshot()['state'], 'disabled')
        self.assertFalse(self.runtime.folder.exists())

    def test_previous_session_or_job_cannot_be_marked_matched(self):
        runtime = self.runtime
        runtime.process = Mock()
        runtime.process.poll.return_value = None
        runtime.observe(self.work, self.plan)
        row = {'session': 'older', 'updated_at': time.time(), 'last_check': {'job_id': runtime.current_job, 'matched': True}}
        save_snapshot(runtime.folder/'status.json', row)
        self.assertEqual(runtime.snapshot()['math_check'], 'pending')
        row.update(session=runtime.session, state='online')
        row['last_check']['job_id'] = 'different'
        save_snapshot(runtime.folder/'status.json', row)
        runtime.last_read = -float("inf")
        self.assertEqual(runtime.snapshot()['math_check'], 'pending')
        row['last_check']['job_id'] = runtime.current_job
        save_snapshot(runtime.folder/'status.json', row)
        runtime.last_read = -float("inf")
        self.assertEqual(runtime.snapshot()['math_check'], 'matched')
        row['updated_at'] = 0
        save_snapshot(runtime.folder/'status.json', row)
        runtime.last_read = -float("inf")
        self.assertEqual(runtime.snapshot()['state'], 'stale')

    def test_job_handoff_excludes_header_wallet_and_duplicate_writes(self):
        runtime = self.runtime
        runtime.process = Mock()
        runtime.observe(self.work, self.plan)
        text = (runtime.folder/'job.json').read_text()
        self.assertNotIn(GENESIS.hex(), text)
        self.assertNotIn('address', text)
        with patch('btcminer.provider_runtime.save_snapshot') as save:
            runtime.observe(self.work, self.plan)
            save.assert_not_called()

    def test_shutdown_terminates_only_owned_process(self):
        from subprocess import TimeoutExpired
        process = self.runtime.process = Mock()
        process.poll.return_value = None
        process.wait.side_effect = [TimeoutExpired('fixture', 2), 0]
        self.runtime.close()
        process.terminate.assert_called_once_with()
        process.kill.assert_called_once_with()

    def test_engine_supplies_real_plan_and_exposes_provider_status(self):
        from btcminer.engine import Engine
        from btcminer.settings import DEFAULTS
        with patch.dict('os.environ'):
            engine = Engine(dict(DEFAULTS, strategy='thesis2', native_hasher=False, nonce_log=False,
                                 observatory_telemetry=False), logs=self.runtime.folder)
            self.addCleanup(engine.model_telemetry.close)
            engine.provider = Mock()
            engine.provider.snapshot.return_value = {'enabled': True, 'state': 'online'}
            generator = engine.unfiltered_tasks(self.work)
            next(generator)
            generator.close()
            engine.provider.observe.assert_called_once()
            observed_work, plan = engine.provider.observe.call_args.args
            self.assertIs(observed_work, self.work)
            self.assertEqual(plan.phase, Traversal(GENESIS).phase)
            self.assertEqual(engine.snapshot()['provider']['state'], 'online')
