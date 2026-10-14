import struct
import unittest
from decimal import Decimal, localcontext

from btcminer.native import hash256
from btcminer.protocol import (DIFF1, core_work, pool_work, script_for_address,
                               target_from_bits, target_from_difficulty)
from btcminer.serialization import _build_coinbase, _coinbase_add_witness

# Public BIP173 test vector, never used as a runtime payout default.
# https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki
ADDRESS = "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4"
SCRIPT = bytes.fromhex("0014751e76e8199196d454941c45d1b3a323f1433bd6")


def template():
    return {"height":900000, "bits":"207fffff", "previousblockhash":"01234567"*8,
            "coinbasevalue":5000000000, "curtime":1700000000, "version":0x20000000,
            "transactions":[]}


class ProtocolTests(unittest.TestCase):
    def test_difficulty_conversion_is_exact_independent_of_decimal_context(self):
        with localcontext() as ctx:
            ctx.prec = 6
            for value, expected in ((1, DIFF1), (2, DIFF1//2),
                                    (Decimal("0.125"), DIFF1*8),
                                    (Decimal("3.7"), DIFF1*10//37)):
                self.assertEqual(target_from_difficulty(value), expected)

    def test_difficulty_extremes_and_invalid_inputs(self):
        self.assertEqual(target_from_difficulty("1e-999999"), (1 << 256)-1)
        self.assertEqual(target_from_difficulty("1e999999"), 0)
        for value in (0, -1, "NaN", "Infinity", "-Infinity", "garbage", None):
            with self.subTest(value=value), self.assertRaises(ValueError):
                target_from_difficulty(value)

    def test_compact_target_consensus_vectors(self):
        self.assertEqual(target_from_bits("1d00ffff"), DIFF1)
        self.assertEqual(target_from_bits("207fffff"), 0x7fffff << 232)
        self.assertEqual(target_from_bits("01123456"), 0x12)
        for bits in ("00000000", "1d80ffff", "2300ffff", "01000001"):
            with self.assertRaises(ValueError):
                target_from_bits(bits)

    def test_payout_address_checksum_case_and_network(self):
        self.assertEqual(script_for_address(ADDRESS, "mainnet"), SCRIPT)
        self.assertEqual(script_for_address(ADDRESS.lower(), "mainnet"), SCRIPT)
        for address, network in ((ADDRESS, "regtest"), (ADDRESS[:-1]+"5", "mainnet"),
                                 ("b"+ADDRESS[1:], "mainnet"), (ADDRESS+" ", "mainnet")):
            with self.assertRaises(ValueError):
                script_for_address(address, network)

    def test_core_serialization_and_witness_commitment(self):
        job = template()
        commitment = "6a24aa21a9ed" + hash256(bytes(64)).hex()
        job["default_witness_commitment"] = commitment
        extra = bytes.fromhex("0102030405060708")
        work = core_work(job, ADDRESS, "mainnet", extra, 7)
        stripped = _build_coinbase(job["height"], job["coinbasevalue"], SCRIPT,
                                   witness_commitment_hex=commitment, extra_nonce=extra)
        self.assertEqual(len(work.header), 80)
        self.assertEqual(work.header[4:36], bytes.fromhex(job["previousblockhash"])[::-1])
        self.assertEqual(work.header[36:68], hash256(stripped))
        self.assertEqual(work.data["body"], b"\x01"+_coinbase_add_witness(stripped))
        self.assertEqual(struct.unpack_from("<III", work.header, 68), (1700000000, 0x207fffff, 0))
        second = core_work(job, ADDRESS, "mainnet", b"different", 7)
        self.assertNotEqual(second.header, work.header)

    def test_core_merkle_root_uses_txid_not_witness_transaction_hash(self):
        job = template()
        job["transactions"] = [{"txid":"ab"*32, "hash":"cd"*32, "data":"010203"}]
        work = core_work(job, ADDRESS, "mainnet", bytes(8), 1)
        coinbase = _build_coinbase(job["height"], job["coinbasevalue"], SCRIPT, extra_nonce=bytes(8))
        self.assertEqual(work.header[36:68], hash256(hash256(coinbase)+bytes.fromhex("ab"*32)))
        self.assertTrue(work.data["body"].endswith(bytes.fromhex("010203")))

    def test_pool_header_matches_core_header_for_equivalent_work(self):
        job = template()
        extra = b"\x11\x22\x33\x44\x55\x66\x77\x88"
        work = core_work(job, ADDRESS, "mainnet", extra, 1)
        coinbase = _build_coinbase(job["height"], job["coinbasevalue"], SCRIPT, extra_nonce=extra)
        cb1, cb2 = coinbase.split(extra)
        internal = bytes.fromhex(job["previousblockhash"])[::-1]
        wire = b"".join(internal[i:i+4][::-1] for i in range(0, 32, 4)).hex()
        params = ["job-1",wire,cb1.hex(),cb2.hex(),[],"20000000","207fffff",
                  f"{job['curtime']:08x}",True]
        pool = pool_work(params, extra[:4].hex(), extra[4:].hex(), DIFF1, 1)
        self.assertEqual(pool.header, work.header)
        self.assertEqual(pool.height, job["height"])
        self.assertEqual(pool.target, DIFF1)
