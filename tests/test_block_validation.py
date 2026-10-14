import copy
import json
from pathlib import Path
import unittest
from unittest.mock import Mock, patch

from btcminer.block_validation import verify_accepted_block
from btcminer.connections import CoreConnection
from btcminer.protocol import Work, target_from_bits
from btcminer.settings import DEFAULTS

FIXTURE = Path(__file__).parent / 'fixtures/core-accepted-block'


class BlockValidationTests(unittest.TestCase):
    def setUp(self):
        self.raw = bytes.fromhex((FIXTURE / 'raw.hex').read_text())
        self.block = json.loads((FIXTURE / 'decoded.json').read_text())
        target = target_from_bits('207fffff')
        self.work = Work(self.raw[:80], target // 100_000_000, target,
                         102, '207fffff', 'fixture', 1, {'body': self.raw[80:]})
        self.nonce = int.from_bytes(self.raw[76:80], 'little')
        self.rpc = Mock()
        self.rpc.call.side_effect = lambda method, params: self.raw.hex() if params[1] == 0 else self.block

    def test_actual_core_block_has_matching_hash_merkle_and_witness(self):
        receipt = verify_accepted_block(self.rpc, self.work, self.nonce)
        self.assertEqual(receipt['block_hash'], self.block['hash'])
        self.assertTrue(receipt['witness_commitment_verified'])
        self.assertTrue(receipt['exact_block_readback'])

    def test_target_and_exact_bytes_fail_closed(self):
        self.work.target = 1
        with self.assertRaisesRegex(ValueError, 'target'):
            verify_accepted_block(self.rpc, self.work, self.nonce)
        self.rpc.call.assert_not_called()
        self.work.target = self.work.network_target
        self.work.data['body'] += b'\x00'
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            verify_accepted_block(self.rpc, self.work, self.nonce)

    def test_inconsistent_core_metadata_and_commitments_are_rejected(self):
        changes = [
            lambda b: b.update(confirmations=-1),
            lambda b: b.update(height=103),
            lambda b: b.update(hash='00' * 32),
            lambda b: b['tx'][1].update(txid='00' * 32),
            lambda b: b['tx'][1].update(hash='00' * 32),
            lambda b: b['tx'][0]['vin'][0].update(txinwitness=['01' * 32]),
            lambda b: b['tx'][0]['vin'][0].update(txinwitness=[]),
        ]
        original = copy.deepcopy(self.block)
        for change in changes:
            with self.subTest(change=change):
                self.block = copy.deepcopy(original)
                change(self.block)
                with self.assertRaises(ValueError):
                    verify_accepted_block(self.rpc, self.work, self.nonce)

    def connection(self):
        c = CoreConnection(dict(DEFAULTS), Mock())
        c.connected = True
        c.generation = 1
        c.template = {'fixture': True}
        c.rpc = self.rpc
        readback = self.rpc.call.side_effect
        self.rpc.call.side_effect = lambda method, params: None if method == 'submitblock' else readback(method, params)
        return c

    def test_success_is_countable_only_after_readback(self):
        c = self.connection()
        self.assertEqual(c.submit(self.work, self.nonce), (True, 'block accepted', True))
        self.assertFalse(c.valid(self.work))
        self.assertEqual(c.emit.call_args.args[0], 'block_verified')
        self.assertEqual(c.emit.call_args.kwargs['block_hash'], self.block['hash'])

    def test_missing_readback_is_unknown_and_retires_work(self):
        c = self.connection()
        self.rpc.call.side_effect = [None, TimeoutError('readback unavailable')]
        result = c.submit(self.work, self.nonce)
        self.assertIsNone(result[0])
        self.assertFalse(result[2])
        self.assertIn('verification incomplete', result[1])
        self.assertFalse(c.valid(self.work))
        c.emit.assert_not_called()
        self.assertEqual(c.submit(self.work, self.nonce), (False, 'stale template', False))
        self.assertEqual(self.rpc.call.call_count, 2)

    def test_core_rejection_does_not_trigger_success_readback(self):
        c = self.connection()
        self.rpc.call.side_effect = None
        self.rpc.call.return_value = 'high-hash'
        self.assertEqual(c.submit(self.work, self.nonce), (False, 'high-hash', False))
        self.rpc.call.assert_called_once()
        c.emit.assert_not_called()

    def test_service_does_not_construct_engine_when_startup_checks_fail(self):
        from btcminer import service
        with patch.object(service, 'load', return_value=dict(DEFAULTS)), \
             patch.object(service, 'validate_start'), \
             patch('btcminer.diagnostics.self_test', return_value={'ok': False}) as check, \
             patch('btcminer.engine.Engine') as engine:
            with self.assertRaisesRegex(RuntimeError, 'startup hash/scanner validation failed'):
                service.serve()
            check.assert_called_once_with(DEFAULTS, require_native=True)
            engine.assert_not_called()
