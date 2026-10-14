"""Local HTTP failures must be classified without exposing upstream secrets."""
import http.server
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from btcminer.rpc import RPC, RPCError
from btcminer.connections import CoreConnection
from btcminer.settings import DEFAULTS


class RPCDiagnosticsTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        cookie = Path(folder.name)/'cookie'
        cookie.write_text('test:SECRET-CREDENTIAL')
        self.reply = {'status': 200, 'body': {'result': 7, 'error': None, 'id': 'btc-miner'}}
        reply = self.reply
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *args): pass
            def do_POST(self):
                self.rfile.read(int(self.headers['Content-Length']))
                if reply.get('reset'):
                    self.connection.shutdown(2)
                    self.connection.close()
                    return
                time.sleep(reply.get('delay', 0))
                body = reply.get('raw', json.dumps(reply['body']).encode())
                try:
                    self.send_response(reply['status'])
                    self.send_header('Content-Length', str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except (BrokenPipeError, ConnectionResetError): pass
        server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), Handler)
        server.daemon_threads = True
        threading.Thread(target=server.serve_forever, daemon=True).start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        self.config = dict(DEFAULTS, rpc_cookie=str(cookie), rpc_port=server.server_port, rpc_timeout=.08)
        self.rpc = RPC(self.config)

    def failure(self, kind):
        with self.assertRaises(RPCError) as result:
            self.rpc.call('getblocktemplate', ['SECRET-PARAMETER'])
        error = result.exception
        self.assertEqual(error.kind, kind)
        self.assertEqual(error.method, 'getblocktemplate')
        self.assertGreaterEqual(error.elapsed_seconds, 0)
        self.assertEqual(error.timeout_seconds, .08)
        self.assertNotIn('SECRET', str(error) + json.dumps(error.diagnostics()))
        return error

    def test_timeout_is_typed_and_measured(self):
        self.reply['delay'] = .3
        error = self.failure('timeout')
        self.assertGreaterEqual(error.elapsed_seconds, .06)

    def test_reset_is_connection_failure(self):
        self.reply['reset'] = True
        self.assertIn(self.failure('connection_error').kind, ('connection_error',))

    def test_invalid_json(self):
        self.reply['raw'] = b'SECRET-response'
        self.failure('invalid_json')

    def test_invalid_schemas_and_wrong_request_id(self):
        for body in ([], None, {'result': 1}, {'error': None}, {'result': 1, 'error': None, 'id': 'other'}):
            with self.subTest(body=body):
                self.reply['body'] = body
                self.failure('invalid_response')

    def test_http_errors_cannot_be_success_even_with_success_shaped_body(self):
        for status in (401, 403, 404, 500):
            with self.subTest(status=status):
                self.reply['status'] = status
                error = self.failure('authentication' if status in (401, 403) else 'http_error')
                self.assertEqual(error.http_status, status)

    def test_server_timeout_text_is_not_transport_timeout(self):
        self.reply.update(status=500, body={'result': None, 'error': {'code': -28, 'message': 'SECRET timed out'}})
        error = self.failure('rpc_error')
        self.assertEqual(error.rpc_code, -28)
        c = CoreConnection(dict(self.config, template_refresh=0), lambda *args, **kwargs: None)
        calls = []
        def call(method, params=None, timeout=None):
            calls.append(params)
            if len(calls) == 1: return {'height': 1, 'longpollid': 'test'}
            raise error
        def emit(kind, message, **fields):
            if kind == 'connection':
                self.assertEqual(fields['rpc_error_kind'], 'rpc_error')
                c.stop.set()
        c.emit = emit
        with patch.object(c.rpc, 'check'), patch.object(c.rpc, 'call', side_effect=call):
            c.run()
        self.assertEqual(len(calls), 2)  # No misleading short-poll fallback.

    def test_valid_result_and_null_submit_result(self):
        self.assertEqual(self.rpc.call('getnetworkinfo'), 7)
        self.reply['body']['result'] = None
        self.assertIsNone(self.rpc.call('submitblock', ['fixture-only']))

    def test_unsafe_method_and_rpc_code_are_not_logged(self):
        error = RPCError('SECRET url', 'rpc_error', 1, 15, 500, 'SECRET-code')
        self.assertEqual(error.method, 'unknown')
        self.assertIsNone(error.rpc_code)
        self.assertNotIn('SECRET', str(error))
