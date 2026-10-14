import unittest
from unittest.mock import Mock, patch

from btcminer.diagnostics import doctor
from btcminer.protocol import target_from_bits
from btcminer.rpc import RPC
from btcminer.settings import DEFAULTS
from test_protocol import ADDRESS, SCRIPT, template


class ReadinessTests(unittest.TestCase):
    def test_public_node_rejects_wrong_chain_sync_lag_and_missing_peers(self):
        cases = [({'chain':'testnet4'}, {}, 'Network mismatch'),
                 ({'chain':'main','initialblockdownload':True}, {}, 'still syncing'),
                 ({'chain':'main','blocks':9,'headers':10}, {}, 'known headers'),
                 ({'chain':'main'}, {'networkactive':True,'connections':0}, 'peer connection'),
                 ({'chain':'main'}, {'networkactive':False,'connections':2}, 'peer connection')]
        for chain, network, message in cases:
            rpc = RPC(dict(DEFAULTS))
            rpc.call = Mock(side_effect=[chain,network])
            with self.subTest(message=message), self.assertRaisesRegex(ValueError,message):
                rpc.check()

    def test_regtest_does_not_require_public_peers(self):
        rpc = RPC(dict(DEFAULTS,network='regtest'))
        rpc.call = Mock(return_value={'chain':'regtest','blocks':10,'headers':10})
        self.assertEqual(rpc.check()['chain'],'regtest')
        rpc.call.assert_called_once_with('getblockchaininfo')

    def run_doctor(self, address=None, job=None, proposal=None):
        rpc = Mock()
        rpc.cookie.return_value.is_file.return_value = True
        rpc.check.return_value = {'chain':'main','blocks':10,'headers':10}
        job = template() if job is None else job
        job.setdefault('target',f'{target_from_bits(job["bits"]):064x}')
        rpc.call.side_effect = [address if address is not None else
                               {'isvalid':True,'scriptPubKey':SCRIPT.hex()}, job, proposal]
        with patch('btcminer.diagnostics.RPC',return_value=rpc):
            result = doctor(dict(DEFAULTS,address=ADDRESS),connect=True)
        return result,rpc

    def test_candidate_is_checked_without_submitblock_or_mining(self):
        result,rpc = self.run_doctor()
        self.assertTrue(result['core_ready'])
        self.assertFalse(result['mining_started'])
        self.assertEqual(result['proposal'],{'valid':True,'pow_checked':False,'broadcast':False})
        self.assertEqual([x.args[0] for x in rpc.call.call_args_list],
                         ['validateaddress','getblocktemplate','getblocktemplate'])
        self.assertEqual(rpc.call.call_args.args[1][0]['mode'],'proposal')

    def test_payout_script_disagreement_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'payout address script'):
            self.run_doctor(address={'isvalid':True,'scriptPubKey':'51'})

    def test_template_target_disagreement_is_rejected(self):
        job = template(); job['target'] = '01'
        with self.assertRaisesRegex(ValueError,'compact bits'):
            self.run_doctor(job=job)

    def test_proposal_rejection_is_not_reported_as_ready(self):
        for reason in ['bad-txnmrklroot','bad-witness-merkle-match','inconclusive-not-best-prevblk']:
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError,'did not validate'):
                self.run_doctor(proposal=reason)
