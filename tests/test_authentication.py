"""Credential-boundary regressions using dummy secrets and disposable services."""
from contextlib import ExitStack, nullcontext, redirect_stdout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import io
import json
import os
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import Mock, patch

from btcminer import onboarding, platform_support, provider, settings
from btcminer.rpc import RPC
from btcminer.distribution import cli as cluster
from btcminer.distribution.transport import read_tokens


class RPCBoundaryTests(unittest.TestCase):
    def test_remote_http_is_rejected_before_credentials_or_network(self):
        for extra in ({}, {'rpc_user': 'fixture'}, {'rpc_cookie': '/explicit-cookie'}):
            rpc = RPC(dict(settings.DEFAULTS, rpc_host='remote.example', **extra))
            with patch.object(rpc, 'cookie') as cookie, patch.object(rpc.opener, 'open') as opened:
                with self.assertRaisesRegex(ValueError, 'requires rpc_tls'):
                    rpc.call('getblockchaininfo')
                cookie.assert_not_called(); opened.assert_not_called()

    def test_remote_https_never_discovers_local_cookie(self):
        rpc = RPC(dict(settings.DEFAULTS, rpc_host='remote.example', rpc_tls=True))
        with patch.object(rpc, 'cookie') as cookie, patch.object(rpc.opener, 'open') as opened:
            with self.assertRaisesRegex(ValueError, 'explicit'):
                rpc.call('getblockchaininfo')
            cookie.assert_not_called(); opened.assert_not_called()

    def test_remote_https_accepts_explicit_environment_credentials(self):
        rpc = RPC(dict(settings.DEFAULTS, rpc_host='remote.example', rpc_tls=True, rpc_user='fixture'))
        response = io.BytesIO(b'{"result":{},"error":null}')
        with patch.dict(os.environ, BTC_RPC_PASSWORD='dummy-password'), patch.object(rpc.opener, 'open', return_value=response) as opened:
            self.assertEqual(rpc.call('getblockchaininfo'), {})
        request = opened.call_args.args[0]
        self.assertEqual(request.full_url, 'https://remote.example:8332/')
        self.assertTrue(request.has_header('Authorization'))

    def test_real_redirects_never_reach_another_endpoint(self):
        received = []
        class Sink(BaseHTTPRequestHandler):
            def log_message(self, *args): pass
            def do_GET(self):
                received.append(self.headers.get('Authorization'))
                self.send_response(200); self.end_headers()
            do_POST = do_GET
        with tempfile.TemporaryDirectory() as folder, ExitStack() as cleanup:
            def server(handler):
                instance = ThreadingHTTPServer(('127.0.0.1', 0), handler)
                thread = threading.Thread(target=instance.serve_forever, daemon=True); thread.start()
                cleanup.callback(lambda: (instance.shutdown(), instance.server_close(), thread.join()))
                return instance
            sink = server(Sink)
            class Redirect(BaseHTTPRequestHandler):
                code = 302
                def log_message(self, *args): pass
                def do_POST(self):
                    self.rfile.read(int(self.headers['Content-Length']))
                    self.send_response(self.code)
                    self.send_header('Location', 'http://127.0.0.1:%d/' % sink.server_port)
                    self.send_header('Content-Length', '0'); self.end_headers()
            origin = server(Redirect)
            (Path(folder)/'.cookie').write_text('fixture:dummy-cookie')
            rpc = RPC(dict(settings.DEFAULTS, rpc_datadir=folder, rpc_port=origin.server_port))
            for code in (301, 302, 303, 307, 308):
                Redirect.code = code
                with self.subTest(code=code), self.assertRaises((ValueError, RuntimeError)):
                    rpc.call('getblockchaininfo')
            self.assertEqual(received, [])


class ProviderBoundaryTests(unittest.TestCase):
    def test_remote_plaintext_rejected_before_secret_lookup(self):
        with patch.object(provider, 'keychain') as keychain:
            for origin in ('http://provider.example', 'http://192.0.2.1', 'http://[2001:db8::1]'):
                with self.subTest(origin=origin), self.assertRaisesRegex(ValueError, 'HTTPS'):
                    provider.ProviderClient(origin)
            keychain.assert_not_called()
        for origin in ('https://provider.example', 'http://127.0.0.1:1234', 'http://[::1]:1234', 'http://localhost:1234'):
            provider.ProviderClient(origin)

    def test_login_validates_account_and_discards_bad_session(self):
        client = provider.ProviderClient('https://provider.example', user='fixture')
        client.json = Mock(return_value={'ok': True, 'sessionId': 'dummy-token'})
        client.formulas = Mock(side_effect=provider.ProviderError('account mismatch'))
        with self.assertRaises(provider.ProviderError): client.login('dummy-password')
        self.assertIsNone(client.token)
        for token in ('', False, 123, 'bad\nheader'):
            client.json.return_value = {'ok': True, 'sessionId': token}
            with self.assertRaises(provider.ProviderError): client.login('dummy-password')

    def test_runtime_uses_saved_origin_without_putting_secrets_in_argv(self):
        from btcminer.provider_runtime import ProviderRuntime
        with tempfile.TemporaryDirectory() as folder, patch.dict(os.environ, {}, clear=True), patch('btcminer.provider_runtime.subprocess.Popen') as spawn:
            runtime = ProviderRuntime(dict(settings.DEFAULTS, provider_enabled=True, provider_url='https://provider.example'), folder)
            runtime.start()
            self.assertEqual(spawn.call_args.kwargs['env']['BTC_PROVIDER_URL'], 'https://provider.example')
            self.assertNotIn('password', ' '.join(spawn.call_args.args[0]))


class CredentialFileTests(unittest.TestCase):
    def test_cluster_protects_empty_file_before_writing_and_rejects_failure(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'tokens.json'
            def protect(file):
                self.assertEqual(Path(file).read_bytes(), b'')
                platform_support.private_file(file)
            with patch.object(cluster, 'private_file', side_effect=protect), redirect_stdout(io.StringIO()):
                cluster.main(['init', '--auth', str(path), '--node', 'fixture'])
            self.assertEqual(set(read_tokens(path)), {'fixture'})
            path.unlink()
            with patch.object(cluster, 'private_file', side_effect=OSError('ACL denied')):
                with self.assertRaises(OSError): cluster.main(['init', '--auth', str(path), '--node', 'fixture'])
            self.assertFalse(path.exists())

    def test_reader_checks_permissions_before_parsing_tokens(self):
        with patch('btcminer.distribution.transport.check_private_file', side_effect=ValueError('shared')), patch.object(Path, 'read_bytes') as read:
            with self.assertRaisesRegex(ValueError, 'shared'): read_tokens('dummy.json')
            read.assert_not_called()

    def test_windows_acl_replaces_explicit_grants_and_checks_owner(self):
        with patch.object(platform_support, 'WINDOWS', True), patch.object(platform_support.subprocess, 'run') as run:
            platform_support.private_file('fixture path with spaces')
        self.assertEqual(run.call_count, 2)
        setter, verifier = [call.args[0][-1] for call in run.call_args_list]
        self.assertIn('New-Object System.Security.AccessControl.FileSecurity', setter)
        self.assertIn('SetAccessRuleProtection($true, $false)', setter)
        self.assertIn('Wrong owner', verifier)
        self.assertIn('Shared credential file', verifier)
        self.assertEqual(run.call_args.kwargs['env']['BTC_PRIVATE_ACL_PATH'], 'fixture path with spaces')

    def test_real_private_file_roundtrip_on_current_platform(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'private.json'
            path.touch()
            platform_support.private_file(path)
            platform_support.check_private_file(path)
            if os.name != 'nt':
                path.chmod(0o644)
                with self.assertRaises(ValueError): platform_support.check_private_file(path)


class GuidedLoginTests(unittest.TestCase):
    def fixture(self, stack):
        stack.enter_context(patch.object(onboarding.sys.stdin, 'isatty', return_value=True))
        stack.enter_context(patch.object(onboarding.service, 'status', return_value={}))
        stack.enter_context(patch.object(onboarding.service, 'lifecycle_lock', return_value=nullcontext()))
        stack.enter_context(patch.object(onboarding, 'load', return_value=dict(settings.DEFAULTS)))
        stack.enter_context(patch('builtins.input', side_effect=['https://provider.example', 'fixture']))
        stack.enter_context(patch('getpass.getpass', return_value='dummy-password'))
        save = stack.enter_context(patch.object(onboarding, 'save'))
        login = stack.enter_context(patch.object(provider.ProviderClient, 'login'))
        ui = stack.enter_context(patch('btcminer.tui.run', return_value=0))
        return save, login, ui

    def test_login_saves_only_nonsecrets_and_scopes_environment(self):
        with ExitStack() as stack:
            stack.enter_context(patch.dict(os.environ, {'BTC_PROVIDER_SESSION':'previous-token'}, clear=True))
            save, login, ui = self.fixture(stack)
            def dashboard():
                self.assertEqual(os.environ['BTC_PROVIDER_PASSWORD'], 'dummy-password')
                self.assertEqual(os.environ['BTC_PROVIDER_URL'], 'https://provider.example')
                self.assertNotIn('BTC_PROVIDER_SESSION', os.environ)
                return 0
            ui.side_effect = dashboard
            output = io.StringIO()
            with redirect_stdout(output): self.assertEqual(onboarding.provider_login(), 0)
            saved = save.call_args.args[0]
            self.assertTrue(saved['provider_enabled'])
            self.assertEqual(saved['provider_user'], 'fixture')
            self.assertNotIn('dummy-password', json.dumps(saved)+output.getvalue())
            self.assertEqual(os.environ['BTC_PROVIDER_SESSION'], 'previous-token')
            self.assertNotIn('BTC_PROVIDER_PASSWORD', os.environ)
            login.assert_called_once_with('dummy-password')

    def test_failed_login_never_saves_or_opens_dashboard_or_echoes_secret(self):
        with ExitStack() as stack:
            save, login, ui = self.fixture(stack)
            login.side_effect = RuntimeError('dummy-password untrusted response')
            with redirect_stdout(io.StringIO()), self.assertRaises(provider.ProviderError) as caught:
                onboarding.provider_login()
            self.assertNotIn('dummy-password', str(caught.exception))
            save.assert_not_called(); ui.assert_not_called()

    def test_cancelled_password_prompt_leaves_settings_untouched(self):
        with ExitStack() as stack:
            save, login, ui = self.fixture(stack)
            stack.enter_context(patch('getpass.getpass', side_effect=KeyboardInterrupt))
            with redirect_stdout(io.StringIO()), self.assertRaises(KeyboardInterrupt): onboarding.provider_login()
            save.assert_not_called(); login.assert_not_called(); ui.assert_not_called()
