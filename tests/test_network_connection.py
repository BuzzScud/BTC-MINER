import base64
from http.server import BaseHTTPRequestHandler, HTTPServer
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

from btcminer.networks import check_connection
from btcminer.rpc import RPC
from btcminer.settings import DEFAULTS


class NetworkConnectionTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.root = Path(self.folder.name)
        self.config = dict(DEFAULTS, rpc_datadir=str(self.root))

    def test_existing_local_core_credentials_and_explicit_auth_precedence(self):
        path = self.root/'bitcoin.conf'
        path.write_text('rpcuser=example\nrpcpassword=private\n[main]\nrpcport=8332\n[testnet4]\nrpcport=48332\nrpcuser=test\nrpcpassword=test-secret\n')
        self.assertEqual(RPC(self.config).local_config_auth(),'example:private')
        self.assertEqual(RPC(dict(self.config, network='testnet4')).local_config_auth(),'test:test-secret')
        for changes in ({'rpc_host':'remote.example'}, {'rpc_port':9999}, {'rpc_cookie':'/explicit/cookie'}):
            self.assertIsNone(RPC(dict(self.config, **changes)).local_config_auth())
        path.write_text(path.read_text()+'\nincludeconf=another.conf\n')
        self.assertIsNone(RPC(self.config).local_config_auth())

    def test_real_http_rpc_handshake_without_mining_or_secret_output(self):
        calls = []
        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args): pass
            def do_POST(self):
                if self.headers.get('Authorization') != 'Basic '+base64.b64encode(b'example:private').decode():
                    self.send_error(401); return
                request=json.loads(self.rfile.read(int(self.headers['Content-Length'])))
                calls.append(request['method'])
                values={'getblockchaininfo':{'chain':'main','blocks':100,'headers':100,'initialblockdownload':False},
                        'getnetworkinfo':{'networkactive':True,'connections':8}}
                body=json.dumps({'result':values[request['method']], 'error':None}).encode()
                self.send_response(200);self.send_header('Content-Length',str(len(body)));self.end_headers();self.wfile.write(body)
        server=HTTPServer(('127.0.0.1',0),Handler)
        worker=threading.Thread(target=server.serve_forever,daemon=True);worker.start()
        self.addCleanup(server.server_close);self.addCleanup(server.shutdown)
        port=server.server_port
        (self.root/'bitcoin.conf').write_text(f'rpcuser=example\nrpcpassword=private\nrpcport={port}\n')
        result=check_connection(dict(self.config,rpc_port=port))
        self.assertTrue(result['ok']);self.assertTrue(result['network_match']);self.assertTrue(result['node_ready'])
        self.assertFalse(result['mining_started']);self.assertNotIn('private',json.dumps(result))
        self.assertEqual(calls,['getblockchaininfo','getnetworkinfo'])

    def test_wrong_chain_syncing_and_missing_auth_are_distinct(self):
        with patch.object(RPC,'call',return_value={'chain':'testnet4'}):
            result=check_connection(self.config)
        self.assertFalse(result['ok']);self.assertTrue(result['connected']);self.assertFalse(result['network_match'])
        with patch.object(RPC,'call',side_effect=[{'chain':'main','initialblockdownload':True,'blocks':1,'headers':100},
                                                {'networkactive':True,'connections':4}]):
            result=check_connection(self.config)
        self.assertTrue(result['ok']);self.assertTrue(result['syncing']);self.assertFalse(result['node_ready'])
        result=check_connection(self.config)
        self.assertFalse(result['ok']);self.assertFalse(result['connected']);self.assertIn('authentication',result['message'])
