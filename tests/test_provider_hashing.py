"""Remote SHA256d binding, byte-order, mismatch and no-local-fallback checks."""
import hashlib
import unittest
from unittest.mock import Mock, patch

from btcminer import provider, tcmp
from btcminer.diagnostics import GENESIS


class HashingTests(unittest.TestCase):
    def client(self):
        client = Mock()
        def response(method, path, *, data, headers):
            frame = tcmp.encode(data)
            return {'x-compression-codec':'coprime', 'x-original-size':str(len(data)),
                    'x-compressed-size':str(len(frame)),
                    'x-original-sha256':hashlib.sha256(data).hexdigest()}, frame
        client.request.side_effect = response
        return client

    def test_genesis_exact_two_raw_inputs_and_display_byte_order(self):
        client = self.client()
        result = provider.hash_header(client, GENESIS)
        self.assertTrue(result['ok'])
        self.assertEqual(result['hash_hex'], '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f')
        calls = client.request.call_args_list
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0].kwargs['data'], GENESIS)
        self.assertEqual(calls[1].kwargs['data'], hashlib.sha256(GENESIS).digest())
        self.assertFalse(result['block_submitted'])

    def test_remote_only_never_calls_local_sha_or_falls_back(self):
        client = self.client()
        replies = [client.request('POST','/',data=data,headers={})
                   for data in (GENESIS, hashlib.sha256(GENESIS).digest())]
        client.request = Mock(side_effect=replies)
        with patch.object(provider.hashlib, 'sha256', side_effect=AssertionError('local SHA called')):
            result = provider.hash_header(client, GENESIS, 'remote')
        self.assertEqual(result['local_verification'], 'not_performed')
        self.assertNotIn('local_hash_hex', result)

    def test_wrong_well_formed_digest_fails_comparison(self):
        client = self.client()
        original = client.request.side_effect
        def wrong(*args, **kwargs):
            headers, frame = original(*args, **kwargs)
            headers['x-original-sha256'] = '00'*32
            return headers, frame
        client.request.side_effect = wrong
        result = provider.hash_header(client, GENESIS)
        self.assertFalse(result['ok'])
        self.assertEqual(result['local_verification'], 'mismatch')

    def test_metadata_and_digest_corruption_rejected(self):
        for field,value in [('x-original-sha256','ab'),('x-original-sha256','z'*64),
                            ('x-original-sha256',None),('x-original-size','79'),
                            ('x-compressed-size','1'),('x-compression-codec','gzip')]:
            client = self.client()
            h,f = client.request('POST','/',data=GENESIS,headers={})
            h[field]=value;client.request=Mock(return_value=(h,f))
            with self.assertRaises(provider.ProviderError):provider.hash_header(client,GENESIS)
            self.assertEqual(client.request.call_count,1)

    def test_wrong_input_and_broken_frame_rejected(self):
        for frame in (tcmp.encode(b'\0'*80), b'bad frame'):
            headers={'x-compression-codec':'coprime','x-original-size':'80',
                     'x-compressed-size':str(len(frame)),'x-original-sha256':'00'*32}
            client=Mock();client.request.return_value=(headers,frame)
            with self.assertRaises(provider.ProviderError):provider.hash_header(client,GENESIS)

    def test_invalid_input_has_no_network_side_effects(self):
        client=Mock()
        for header in (b'',b'\0'*79,b'\0'*81,GENESIS.hex()):
            with self.assertRaises(ValueError):provider.hash_header(client,header)
        with self.assertRaises(ValueError):provider.hash_header(client,GENESIS,'invalid')
        client.request.assert_not_called()

    def test_remote_failure_propagates_without_local_fallback(self):
        client=Mock();client.request.side_effect=provider.ProviderError('offline')
        with patch.object(provider.hashlib,'sha256',side_effect=AssertionError('local fallback')):
            with self.assertRaises(provider.ProviderError):provider.hash_header(client,GENESIS,'remote')

    def test_cli_validates_before_authentication_and_does_not_start_miner(self):
        from btcminer import cli
        with patch.object(provider.ProviderClient,'authenticate') as auth, \
                patch.object(cli,'load') as load, patch.object(cli.service,'start') as start, \
                patch.object(cli,'print_result'):
            self.assertNotEqual(cli.main(['provider','hash','--header-hex','00']),0)
            auth.assert_not_called();load.assert_not_called();start.assert_not_called()

    def test_cli_compare_returns_nonzero_on_mismatch(self):
        from btcminer import cli
        with patch.object(provider.ProviderClient,'authenticate'), \
                patch.object(provider,'hash_header',return_value={'ok':False}), \
                patch.object(cli,'print_result'), patch.object(cli.service,'start') as start:
            self.assertEqual(cli.main(['provider','hash','--header-hex',GENESIS.hex()]),1)
            start.assert_not_called()


if __name__ == '__main__':unittest.main()
