import os
import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import Mock, patch

from btcminer.diagnostics import GENESIS
from btcminer.engine import Engine
from btcminer.protocol import Work
from btcminer.settings import DEFAULTS


class EngineTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory(prefix="btc-engine-test-")
        self.addCleanup(folder.cleanup)
        env = patch.dict(os.environ)
        env.start(); self.addCleanup(env.stop)
        logs = patch("btcminer.engine.LOGS", Path(folder.name))
        logs.start(); self.addCleanup(logs.stop)
        self.engine = Engine(dict(DEFAULTS, native_hasher=False, pause_on_active=0,
                                  supt_log=False, nonce_log=False, keep_awake=False,
                                  strategy="linear", workers=2))
        # Direct round() tests bypass run(), which normally owns telemetry
        # shutdown. Drain its writer before removing the temporary log directory.
        self.addCleanup(lambda:self.assertTrue(self.engine.model_telemetry.close(),
            'Telemetry must finish before temporary logs are removed'))
        self.engine.connection = Mock()
        self.engine.connection.label = "offline fixture"
        self.engine.connection.connected = True
        self.engine.connection.valid.return_value = True
        self.work = Work(GENESIS, (1 << 256)-1, 1, 900000, "207fffff", "test", 1)

    def test_resumes_after_every_share_without_losing_batch_tail(self):
        for task, expected in (({"start":0xfffffffe,"count":4}, [0xfffffffe,0xffffffff,0,1]),
                               ({"nonces":[55,7,999,1]}, [55,7,999,1])):
            with self.subTest(task=task):
                total = 0; nonces = []
                while task:
                    tried, hits, task, _ = self.engine.scan_task(self.work, task)
                    total += tried; nonces.extend(hits)
                self.assertEqual(total, 4)
                self.assertEqual(nonces, expected)

    def test_stopped_or_stale_work_attempts_no_hashes(self):
        self.engine.connection.valid.return_value = False
        self.assertEqual(self.engine.scan_task(self.work, {"start":0,"count":8})[:3],
                         (0, [], None))
        self.engine.connection.valid.return_value = True
        self.engine.stop.set()
        self.assertEqual(self.engine.scan_task(self.work, {"start":0,"count":8})[:3],
                         (0, [], None))

    def test_round_counts_acceptance_rejection_and_unknown_separately(self):
        self.engine.tasks = lambda work: iter([{"nonces":[101,102,103]}])
        self.engine.connection.submit.side_effect = [(True,"accepted",False),
                                                     (False,"rejected",False),
                                                     (None,"unknown",False)]
        with ThreadPoolExecutor(max_workers=2) as executor:
            self.engine.round(executor, self.work)
        state = self.engine.state
        self.assertEqual(state["hashes"], 3)
        self.assertEqual((state["shares_accepted"], state["shares_rejected"], state["shares_unknown"]),
                         (1, 1, 1))
        self.assertEqual(state["blocks_accepted"], 0)
        submitted = [call.args[1] for call in self.engine.connection.submit.call_args_list]
        self.assertEqual(submitted, [101,102,103])

    def test_invalid_hash_is_never_submitted(self):
        self.work.target = 1
        self.engine.tasks = lambda work: iter([{"start":0,"count":1}])
        self.engine.hasher = Mock()
        self.engine.hasher.scan.return_value = (1, 0)
        with ThreadPoolExecutor(max_workers=2) as executor:
            with self.assertRaisesRegex(RuntimeError, "independent SHA256d"):
                self.engine.round(executor, self.work)
        self.engine.connection.submit.assert_not_called()

    def test_zero_hash_difficulty_is_explicit_and_survives_later_shares(self):
        self.engine.tasks = lambda work: iter([{"nonces":[101,102]}])
        self.engine.scan_task = lambda work,task: (2,[101,102],None,0)
        self.engine.connection.submit.return_value = (True,"accepted",False)
        with patch("btcminer.engine.hash256", side_effect=[bytes(32),(1).to_bytes(32,"little")]):
            with ThreadPoolExecutor(max_workers=2) as executor:
                self.engine.round(executor,self.work)
        self.assertIsNone(self.engine.state["best_difficulty"])
        self.assertTrue(self.engine.state["best_difficulty_unbounded"])
        json.dumps(self.engine.state,allow_nan=False)

    def test_stop_after_block_only_triggers_for_an_accepted_block(self):
        self.engine.c['stop_after_block'] = True
        self.engine.tasks = lambda work: iter([{'nonces':[101]}])
        for accepted,block in ((False,False),(None,False),(True,False),(True,True)):
            with self.subTest(accepted=accepted,block=block):
                self.engine.stop.clear()
                self.engine.connection.submit.return_value = (accepted,'fixture result',block)
                with ThreadPoolExecutor(max_workers=2) as executor:
                    self.engine.round(executor,self.work)
                self.assertEqual(self.engine.stop.is_set(),bool(accepted and block))

    def test_manual_pause_is_independent_of_activity_policy(self):
        self.assertFalse(self.engine.paused())
        self.engine.manual_pause.set()
        self.assertTrue(self.engine.paused())
        self.assertEqual(self.engine.state["paused_reason"], "manual")
        self.engine.manual_pause.clear()
        self.assertFalse(self.engine.paused())

    def test_legacy_seed_version_reaches_state_and_nonce_log(self):
        self.engine.c['single_nonce_only'] = True
        with patch('nonce_logger.log_nonce_round') as logger:
            values = self.engine.candidates(self.work)
        self.assertTrue(values)
        self.assertEqual(self.engine.state['math_version'], 'exact-tower-v2')
        self.assertIn('python:exact-tower-v2', self.engine.state['math_source'])
        self.assertEqual(logger.call_args.kwargs['base_nonce_source'], 'python:exact-tower-v2')
