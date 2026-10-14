"""Quiet Core chains must retain work and leave RPC workers available."""
import copy
import threading
import unittest
from unittest.mock import Mock

from btcminer.connections import CoreConnection
from btcminer.rpc import RPCError
from btcminer.settings import DEFAULTS
from test_protocol import ADDRESS, template


class CorePollingTests(unittest.TestCase):
    def connection(self, **options):
        c = CoreConnection(dict(DEFAULTS, address=ADDRESS, template_refresh=0,
                                retry_seconds=0, **options), Mock())
        c.rpc = Mock()
        # These tests isolate polling lifecycle; real readback is tested in
        # test_block_validation.py and the isolated Core integration.
        c.verify_accepted = Mock(return_value={})
        return c

    def test_quiet_polls_keep_inflight_work_and_refresh_future_timestamps(self):
        c = self.connection()
        original = template()
        works, states, requests = [], [], []
        def call(method, params):
            requests.append((method, params))
            if len(requests) > 1:
                states.append((c.valid(works[0]), c.generation, c.template['curtime']))
            if len(requests) == 5:
                c.close()
            return dict(original, curtime=original['curtime'] + len(requests),
                        longpollid='marker-' + str(len(requests)))
        c.rpc.call.side_effect = call
        c.emit = lambda *a, **k: works.append(c.work())
        c.run()
        self.assertEqual(len(works), 1)
        self.assertTrue(all(valid for valid, _, _ in states))
        self.assertEqual({gen for _, gen, _ in states}, {works[0].generation})
        self.assertEqual(states[-1][2], original['curtime'] + 4)
        self.assertEqual(int.from_bytes(works[0].header[68:72], 'little'), original['curtime'] + 1)
        self.assertTrue(all(method == 'getblocktemplate' and params == [{'rules': ['segwit']}]
                            for method, params in requests))

    def test_substantive_template_changes_retire_old_work(self):
        changes = [dict(previousblockhash='ab' * 32), dict(bits='207ffffe'),
                   dict(version=0x20000002), dict(mintime=1700000001),
                   dict(transactions=[{'txid': 'ab' * 32, 'data': '00'}])]
        for change in changes:
            with self.subTest(change=change):
                c = self.connection()
                first = template()
                second = dict(copy.deepcopy(first), **change)
                c.rpc.call.side_effect = [first, second]
                captured = []
                validity = []
                def emit(*a, **k):
                    captured.append(c.work())
                    if len(captured) == 2:
                        validity.extend([c.valid(captured[0]), c.valid(captured[1])])
                        c.close()
                c.emit = emit
                c.run()
                self.assertEqual(validity, [False, True])
                self.assertNotEqual(captured[0].generation, captured[1].generation)

    def test_response_started_before_acceptance_cannot_restore_old_parent(self):
        c = self.connection()
        first = template()
        c.template, c.connected, c.generation = first, True, 1
        work = c.work()
        polls, submissions, jobs = [], [], []
        def call(method, params):
            if method == 'submitblock':
                submissions.append(params)
                return None
            polls.append(params)
            if len(polls) == 1:
                c.submit(work, 0)
                return first
            return dict(first, previousblockhash='ab' * 32)
        def emit(*a, **k):
            if a[0] != 'job': return
            jobs.append(c.template['previousblockhash'])
            c.close()
        c.rpc.call.side_effect = call
        c.emit = emit
        c.run()
        self.assertEqual(len(submissions), 1)
        self.assertEqual(len(polls), 2)
        self.assertEqual(jobs, ['ab' * 32])
        self.assertNotEqual(c.generation, work.generation)

    def test_rpc_failure_invalidates_work_then_recovers(self):
        c = self.connection()
        old = template()
        c.template, c.connected, c.generation = old, True, 1
        work = c.work()
        failure = RPCError('getblocktemplate', 'timeout', .1, .1)
        c.rpc.call.side_effect = [failure, old]
        state = []
        def emit(kind, message, **fields):
            state.append((kind, c.valid(work), c.template is None))
            if kind == 'job':
                c.close()
        c.emit = emit
        c.run()
        self.assertEqual(state, [('connection', False, True), ('job', False, False)])
        c.rpc.check.assert_called_once()

    def test_close_interrupts_idle_poll_wait(self):
        c = self.connection()
        c.c['template_refresh'] = 300
        ready = threading.Event()
        c.rpc.call.return_value = template()
        c.emit = lambda *a, **k: ready.set()
        c.start()
        try:
            self.assertTrue(ready.wait(1))
        finally:
            c.close()
            c.thread.join(1)
        self.assertFalse(c.thread.is_alive())
        self.assertFalse(c.connected)

    def test_acceptance_wakes_idle_poll_for_new_parent(self):
        c = self.connection()
        c.c['template_refresh'] = 300
        ready, next_tip = threading.Event(), threading.Event()
        first = template()
        polls = []
        def call(method, params):
            if method == 'submitblock':
                return None
            polls.append(params)
            return first if len(polls) == 1 else dict(first, previousblockhash='ab' * 32)
        def emit(*a, **k):
            if a[0] != 'job': return
            (ready if len(polls) == 1 else next_tip).set()
        c.rpc.call.side_effect = call
        c.emit = emit
        c.start()
        try:
            self.assertTrue(ready.wait(1))
            work = c.work()
            self.assertEqual(c.submit(work, 0), (True, 'block accepted', True))
            self.assertTrue(next_tip.wait(1))
            self.assertFalse(c.valid(work))
            self.assertEqual(c.template['previousblockhash'], 'ab' * 32)
        finally:
            c.close()
            c.thread.join(1)
        self.assertFalse(c.thread.is_alive())
