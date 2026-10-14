"""Provider transport failure controls; all network/account access is mocked."""
import asyncio
import hashlib
import io
import json
import os
from pathlib import Path
import random
import struct
import tempfile
import unittest
from unittest.mock import patch, Mock

from btcminer import provider, tcmp


class CodecTests(unittest.TestCase):
    def test_matches_live_provider_golden_frames(self):
        # Byte equality was checked against /api/compression/compress, 2026-10-12.
        hashes = {
            'network': '71a45eed31fe726c214f0a5698a508915db2148e3a1e9f1dcb07939d9cb156a0',
            'file': 'f0922e2f544fa4e1c8a336e18aa7b6daaaa7d3449f89bd30c67403cc2a299418',
            'progressive': '269d418239d9ba419bb65ca1a44fe1f2940c27d339e8725deb4c96063ad9bb7e',
            'constellation': '76b393c3f0de6e40326f311d16af9fa6eacdb6f2a0e69f83c6c8c3a4df8b0082',
            'auto': 'e1f2642b4a9b48efa324af7331efcb4f326ed622f5a3717918399ac6d258a186'}
        for mode, digest in hashes.items():
            frame = tcmp.encode(bytes(1024), mode)
            self.assertEqual(hashlib.sha256(frame).hexdigest(), digest)
            self.assertEqual(tcmp.decode(frame), bytes(1024))

    def test_seeded_binary_roundtrips_and_block_boundaries(self):
        rng = random.Random(2718)
        for n in (0, 1, 2, 3, 4, 5, 6, 7, 8, 29, 255, 256, 1025):
            for mode in tcmp.MODES:
                raw = bytes(rng.randrange(256) for _ in range(n))
                self.assertEqual(tcmp.decode(tcmp.encode(raw, mode)), raw)

    def legacy(self, payload, expected, transform):
        frame = struct.pack('<4sBBBBQQ', b'TCMP', 1, 5, transform, 0,
                            len(expected), tcmp.checksum(expected)) + payload
        self.assertEqual(tcmp.decode(frame), expected)
        return frame

    def test_legacy_stored_rle_lz_blocks_and_delta(self):
        self.legacy(b'hello', b'hello', 0)
        self.legacy(bytes([0xff, 65, 0xff, 65, 0xa5, 65]), b'A' * 300, 1)
        lz = bytes([0, 65, 0x80 | 96, 0, 0])  # A + 100-byte overlapping match.
        self.legacy(lz, b'A' * 101, 2)
        self.legacy(b'\x01' + struct.pack('<I', len(lz)) + lz, b'A' * 101, 3)
        self.legacy(bytes([0xff, 1]), bytes(range(1, 131)), 4)

    def test_malformed_legacy_backreference_is_rejected(self):
        frame = struct.pack('<4sBBBBQQ', b'TCMP', 1, 5, 2, 0, 100, 0) + b'\xff\x00\x00'
        with self.assertRaises(tcmp.CodecError):
            tcmp.decode(frame)

    def test_all_truncations_and_trailing_bytes_rejected(self):
        frame = tcmp.encode(bytes(range(40)))
        for end in range(len(frame)):
            with self.assertRaises(tcmp.CodecError):
                tcmp.decode(frame[:end])
        with self.assertRaises(tcmp.CodecError):
            tcmp.decode(frame + b'\0')

    def test_checksum_corruption_and_unbounded_size_rejected(self):
        frame = bytearray(tcmp.encode(b'abc'))
        frame[16] ^= 1
        with self.assertRaisesRegex(tcmp.CodecError, 'checksum'):
            tcmp.decode(frame)
        frame[8:16] = (2**63).to_bytes(8, 'little')
        with self.assertRaisesRegex(tcmp.CodecError, 'limit'):
            tcmp.decode(frame)
        with self.assertRaisesRegex(tcmp.CodecError, 'limit'):
            tcmp.decode(tcmp.encode(b'abc'), max_output=2)

    def test_crt_block_count_flags_and_residue_corruption(self):
        original = tcmp.encode(bytes(100))
        for offset, value in [(24, 255), (28, 100), (32, 255), (36, 128), (40, 0)]:
            frame = bytearray(original)
            frame[offset] = value
            with self.assertRaises(tcmp.CodecError, msg=str(offset)):
                tcmp.decode(frame)

    def test_frame_marker_and_input_caps(self):
        for offset, value in [(0, 0), (4, 2), (5, 6), (6, 9), (7, 8)]:
            frame = bytearray(tcmp.encode(b'abc'))
            frame[offset] = value
            with self.assertRaises(tcmp.CodecError):
                tcmp.decode(frame)
        with self.assertRaises(tcmp.CodecError):
            tcmp.encode(b'abc', max_input=2)
        with self.assertRaises(tcmp.CodecError):
            tcmp.encode(b'abc', 'unknown')


class Response(io.BytesIO):
    def __init__(self, raw, headers=None, code=200):
        super().__init__(raw)
        self.headers, self.code = headers or {}, code


@patch.object(provider, 'BASE_URL', 'https://provider.test')
class ClientTests(unittest.TestCase):
    def client(self, raw=b'{"ok":true}', headers=None, code=200, **kwargs):
        client = provider.ProviderClient(token='secret/token', **kwargs)
        client.opener = Mock()
        client.opener.open.return_value = Response(raw, headers, code)
        return client

    def test_json_and_negotiated_tcmp(self):
        raw = b'{"ok":true,"value":123}'
        for encoded in (False, True):
            client = self.client(tcmp.encode(raw) if encoded else raw,
                {'x-app-encoding': 'tcmp', 'x-app-original-size': str(len(raw))} if encoded else {})
            self.assertEqual(client.json('GET', '/api/example')['value'], 123)
            request = client.opener.open.call_args.args[0]
            self.assertEqual(request.get_header('Authorization'), 'Bearer secret/token')
            self.assertEqual(client.metrics[0]['decoded_bytes'], len(raw))
            self.assertNotIn('secret/token', json.dumps(client.metrics))

    def test_rejects_size_mismatch_unknown_encoding_and_invalid_json(self):
        raw = b'{"ok":true}'
        for wire, headers in [(tcmp.encode(raw), {'x-app-encoding': 'tcmp', 'x-app-original-size': '1'}),
                              (raw, {'x-app-encoding': 'future'}), (b'html', {}), (b'[]', {}),
                              (b'{"ok":false}', {})]:
            with self.assertRaises(provider.ProviderError):
                self.client(wire, headers).json('GET', '/api/example')

    def test_http_errors_do_not_expose_response_or_secret(self):
        client = self.client(b'secret/token', code=401)
        with self.assertRaises(provider.ProviderError) as caught:
            client.json('GET', '/api/example')
        self.assertEqual(caught.exception.status, 401)
        self.assertNotIn('secret', str(caught.exception))

    def test_response_limit_enforced(self):
        with self.assertRaisesRegex(provider.ProviderError, 'limit'):
            self.client(b'x' * 65, limit=64).json('GET', '/api/example')

    def test_redirect_refused(self):
        with self.assertRaises(provider.ProviderError):
            provider.NoRedirect().redirect_request(None, None, None, None, None, 'https://example.com')

    def test_custom_origin_cannot_read_saved_credentials(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(provider, 'keychain') as lookup:
            with self.assertRaises(provider.ProviderError):
                provider.ProviderClient('https://example.com').authenticate()
            lookup.assert_not_called()

    def test_token_401_cannot_trigger_password_login(self):
        client = self.client(code=401)
        with patch.object(provider, 'keychain') as lookup:
            with self.assertRaises(provider.ProviderError):
                client.authenticate()
            lookup.assert_not_called()

    def test_expired_saved_session_renews_in_memory(self):
        client = provider.ProviderClient()
        client.formulas = Mock(side_effect=[provider.ProviderError('expired', 401), {}])
        client.json = Mock(return_value={'ok': True, 'sessionId': 'new'})
        with patch.dict(os.environ, {}, clear=True), patch.object(provider, 'keychain', side_effect=['old', 'password']):
            client.authenticate()
        self.assertEqual(client.token, 'new')
        self.assertEqual(client.formulas.call_count, 2)

    def test_account_mismatch_is_rejected(self):
        client = self.client(b'{"ok":true,"userName":"someone_else","formulas":[]}')
        with self.assertRaisesRegex(provider.ProviderError, 'account'):
            client.formulas()

    def test_rejects_credential_urls_and_cross_origin_paths(self):
        for url in ('file:///tmp/foo', 'https://u:p@example.com', 'https://example.com/?token=x', 'https://example.com/api'):
            with self.assertRaises(ValueError):
                provider.ProviderClient(url)
        for path in ('https://example.com', '//example.com', '/foo#secret'):
            with self.assertRaises(ValueError):
                self.client().request('GET', path)

    def test_outgoing_json_falls_back_when_crt_expands(self):
        client = self.client()
        client.json('POST', '/api/calculate', {'expression': '123+' * 100 + '1'})
        request = client.opener.open.call_args.args[0]
        self.assertIsNone(request.get_header('X-app-encoding'))
        self.assertEqual(json.loads(request.data)['expression'], '123+' * 100 + '1')

    def test_oversized_and_non_object_variables_rejected(self):
        with self.assertRaises(ValueError):
            self.client().calculate('1', [])
        with self.assertRaises(ValueError):
            self.client().calculate('x' * (1024 * 1024))

    def test_nested_calculation_failure_is_not_success(self):
        client = self.client(b'{"ok":true,"evaluation":{"ok":false}}')
        with self.assertRaisesRegex(provider.ProviderError, 'evaluate'):
            client.calculate('sqrt(-1)')

    def test_incorrect_calculator_value_fails_independent_check(self):
        client = Mock()
        client.calculate.return_value = {'evaluation': {'ok': True, 'value': '0', 'certified': True}}
        result = provider.calculation_check(client)
        self.assertFalse(result['ok'])
        self.assertTrue(all(not row['passed'] for row in result['cases']))

    def test_snapshot_redaction_including_embedded_url_token(self):
        raw = {'sessionId': 'other', 'url': 'ws://example.com?sessionId=secret%2Ftoken',
               'nested': [{'text': 'secret/token', 'password': 'password'}]}
        clean = provider.scrub(raw, ('secret/token',))
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'snapshot.json'
            provider.save_snapshot(path, clean)
            text = path.read_text()
            self.assertNotIn('secret', text)
            self.assertEqual(json.loads(text)['sessionId'], '[redacted]')

    def test_provider_cli_bypasses_miner_configuration_and_control(self):
        from btcminer import cli
        with patch.object(provider, 'run_command', return_value={'ok': True}), patch.object(cli, 'load') as load, \
                patch.object(cli, 'print_result'), patch.object(cli.service, 'start') as start:
            self.assertEqual(cli.main(['provider', 'capabilities']), 0)
            load.assert_not_called()
            start.assert_not_called()

    def test_provider_failed_check_returns_nonzero_cli_exit(self):
        from btcminer import cli
        with patch.object(provider, 'run_command', return_value={'ok': False}), patch.object(cli, 'print_result'):
            self.assertEqual(cli.main(['provider', 'check']), 1)


@patch.object(provider, 'BASE_URL', 'https://provider.test')
class StreamTests(unittest.IsolatedAsyncioTestCase):
    async def stream(self, messages, cap=2):
        try:
            import aiohttp
        except ImportError:
            self.skipTest('optional aiohttp is not installed')
        from types import SimpleNamespace
        class Socket:
            async def __aenter__(self):
                return self
            async def __aexit__(self, *args):
                self.closed = True
            async def receive(self):
                if messages:
                    return messages.pop(0)
                await asyncio.sleep(1)
        socket = Socket()
        class Session:
            async def __aenter__(self):
                return self
            async def __aexit__(self, *args):
                pass
            def ws_connect(self, *args, **kwargs):
                return socket
        with patch.object(aiohttp, 'ClientSession', return_value=Session()):
            client = provider.ProviderClient(token='hidden')
            events = [e async for e in client.updates(seconds=.02, max_events=cap)]
        self.assertTrue(socket.closed)
        return events

    async def test_text_and_binary_messages_redacted_and_bounded(self):
        try:
            import aiohttp
        except ImportError:
            self.skipTest('optional aiohttp is not installed')
        from types import SimpleNamespace as Msg
        messages = [Msg(type=aiohttp.WSMsgType.TEXT, data='{"type":"sessionReady","sessionId":"hidden"}'),
                    Msg(type=aiohttp.WSMsgType.BINARY, data=tcmp.encode(b'{"type":"calculationTelemetry","requestId":"one"}'))]
        events = await self.stream(messages)
        self.assertEqual(events[1]['message']['requestId'], 'one')
        self.assertNotIn('hidden', json.dumps(events))

    async def test_missing_ready_and_remote_errors_are_failures(self):
        try:
            import aiohttp
        except ImportError:
            self.skipTest('optional aiohttp is not installed')
        from types import SimpleNamespace as Msg
        with self.assertRaisesRegex(provider.ProviderError, 'sessionReady'):
            await self.stream([])
        with self.assertRaises(provider.ProviderError):
            await self.stream([Msg(type=aiohttp.WSMsgType.TEXT, data='{"type":"error","message":"hidden"}')])
