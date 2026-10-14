"""Independent oracles and regressions from the October 2026 strict audit."""
import contextlib
import hashlib
import importlib.util
import io
import json
import random
import struct
import sys
import tempfile
import unittest
from decimal import Decimal, localcontext
from fractions import Fraction
from math import gcd, isqrt, lcm
from pathlib import Path
from unittest.mock import patch

from btcminer.diagnostics import GENESIS
from btcminer.native import Hasher, hash256
from btcminer.protocol import DIFF1, Work, core_work, target_from_bits, target_from_difficulty
from btcminer.serialization import _bits_to_target, _build_coinbase_script_sig, _height_to_script_push
from btcminer.pruning import Pruner, MODEL
from btcminer.settings import DEFAULTS


class TargetAuditTests(unittest.TestCase):
    def test_difficulty_floor_including_zero(self):
        values = ['0.1', '0.125', '3.7', '1e-100', '1e100', str(DIFF1),
                  str(DIFF1+1), str(2*DIFF1)]
        rng = random.Random(256)
        values += [str(Decimal(rng.randrange(1, 10**30)).scaleb(-12)) for _ in range(100)]
        with localcontext() as ctx:
            ctx.prec = 3
            for value in values:
                d = Fraction(value)
                expected = min((1 << 256)-1, (DIFF1*d.denominator)//d.numerator)
                self.assertEqual(target_from_difficulty(value), expected, value)

    def test_compact_decoders_match_core_setcompact_flags(self):
        # Independent port of Bitcoin Core v31 arith_uint256::SetCompact.
        rng = random.Random(32)
        values = [rng.getrandbits(32) for _ in range(3000)]
        values += [(e << 24) | m for e in range(36)
                   for m in (0, 1, 0xff, 0x100, 0xffff, 0x10000, 0x7fffff, 0x800001)]
        for bits in values:
            size, word = bits >> 24, bits & 0x7fffff
            if size <= 3:
                word >>= 8*(3-size)
                value = word
            else:
                value = word << (8*(size-3))
            negative = word != 0 and bool(bits & 0x800000)
            overflow = word != 0 and (size > 34 or (word > 0xff and size > 33)
                                      or (word > 0xffff and size > 32))
            for decode in (_bits_to_target, target_from_bits):
                if negative or overflow or value == 0:
                    with self.assertRaises(ValueError): decode(f'{bits:08x}')
                else:
                    self.assertEqual(decode(f'{bits:08x}'), value)
                    self.assertEqual(decode(bits), value)

    def test_compact_rejects_malformed_width_before_shifting(self):
        for bits in (-1, 1 << 32, True, 1.0, None, '0x1d00ffff', ' 1d00ffff',
                     '1d00fff', '001d00ffff', 'zzzzzzzz', 1 << 1000):
            with self.subTest(bits=bits), self.assertRaises(ValueError): target_from_bits(bits)

    def test_zero_target_and_nonce_domains_match_native_and_python(self):
        for enabled in (False, True):
            h = Hasher(enabled)
            self.assertEqual(h.scan(GENESIS, 0, start=0, count=20), (20, None))
            for bad in (-1, 1 << 32, True, 1.5):
                with self.assertRaises(ValueError): h.scan(GENESIS, 1, nonces=[bad])
                with self.assertRaises(ValueError): h.scan(GENESIS, 1, start=bad, count=1)

    def test_template_disagreement_rejected_on_work_path(self):
        with self.assertRaisesRegex(ValueError, 'disagrees'):
            core_work({'bits':'207fffff', 'target':'01'}, '', 'regtest', bytes(8), 1)

    def test_height_and_aux_script_boundaries(self):
        for bad in (-1, 1 << 31, True, 1.5):
            with self.assertRaises(ValueError): _height_to_script_push(bad)
        for h, encoded in ((0,'00'), (1,'51'), (16,'60'), (17,'0111'),
                           (127,'017f'), (128,'028000'), (32768,'03008000')):
            self.assertEqual(_height_to_script_push(h).hex(), encoded)
        for size in (0, 1, 75, 76, 80):
            raw = bytes([0xac])*size
            push = bytes([size]) if size < 76 else b'\x4c'+bytes([size])
            self.assertEqual(_build_coinbase_script_sig(900000, {'flags':raw}),
                             _height_to_script_push(900000)+push+raw)


class PruningAuditTests(unittest.TestCase):
    def test_correctly_tagged_false_exclusion_cannot_discard_a_winner(self):
        p = Pruner(DEFAULTS); self.addCleanup(p.close)
        winner = int.from_bytes(GENESIS[76:], 'little')
        target = int.from_bytes(hash256(GENESIS), 'little')
        work = Work(GENESIS, target, target, 0, '1d00ffff', 'fixture', 1)
        candidates = [winner-1, winner, winner+1]
        def reply(r):
            key = hashlib.sha256(json.dumps([r['header'], r['target'], r['nonces']],
                                           separators=(',', ':')).encode()).hexdigest()
            return {'model':MODEL, 'key':key, 'keep':[], 'excluded':3, 'unknown':False}
        with patch.object(p, 'query', side_effect=reply):
            self.assertEqual(p.filter_task(work, {'nonces':candidates}), {'nonces':[winner]})
        self.assertEqual(p.state['verification_hashes'], 3)
        self.assertEqual(p.state['contradictions'], 1)
        self.assertEqual(p.state['candidates_excluded'], 2)


class ArithmeticOracleTests(unittest.TestCase):
    def test_native_bigints_against_python_signed_oracles(self):
        from btcminer.archive_math import integer_operation as op
        rng = random.Random(8192)
        for bits in (1, 31, 32, 63, 64, 65, 127, 256, 1024, 4096):
            for _ in range(5):
                a, b = rng.getrandbits(bits), rng.getrandbits(bits) | 1
                for x, y in ((a,b), (-a,b), (a,-b), (-a,-b)):
                    for name, expected in (('add',x+y), ('sub',x-y), ('mul',x*y),
                                           ('gcd',gcd(x,y)), ('lcm',lcm(x,y))):
                        self.assertEqual(op(name,x,y), expected, (name,bits))
                self.assertEqual(op('sqrt',a*a+1), isqrt(a*a+1))
                self.assertEqual(op('powmod',-a,33,b), pow(-a,33,b))
                if b > 1 and gcd(a,b) == 1:
                    self.assertEqual(op('invmod',a,b), pow(a,-1,b))

    def test_square_hex_shell_counts_against_lattice_enumeration(self):
        from btcminer.coreprimes import circle_count
        from btcminer.rodmath import shell_count
        for n in range(1, 151):
            remaining = n; factors = {}; d = 2
            while d*d <= remaining:
                while remaining % d == 0:
                    factors[d] = factors.get(d,0)+1; remaining //= d
                d += 1
            if remaining > 1: factors[remaining] = 1
            radius = isqrt(4*n//3)+1
            square = sum(x*x+y*y == n for x in range(-radius,radius+1)
                         for y in range(-radius,radius+1))
            hexagonal = sum(x*x-x*y+y*y == n for x in range(-radius,radius+1)
                            for y in range(-radius,radius+1))
            self.assertEqual(circle_count(factors,'square'), square)
            self.assertEqual(circle_count(factors,'hexagonal'), hexagonal)
            self.assertEqual(shell_count(2,n), square)

    def test_conditional_factor_density_exhausts_all_bases(self):
        from btcminer.rodmath import split_with, split_probability_lower_bound
        primes = [2,3,5,7,11,13,17,19]
        for i,p in enumerate(primes):
            for q in primes[i+1:]:
                n, E = p*q, lcm(p-1,q-1)
                factors = [r for r in primes if E % r == 0]
                count = 0
                for base in range(n):
                    f = split_with(n,base,E,factors)
                    if f is not None:
                        self.assertTrue(1 < f < n and n % f == 0); count += 1
                self.assertGreaterEqual(Fraction(count,n), split_probability_lower_bound(p,q,E))

    def test_ellipse_recovery_and_fermat_bound(self):
        from btcminer.pqmath import PQEllipse, fermat_factor
        for p in range(3,30,2):
            for q in range(p+2,60,2):
                e = PQEllipse(p,q)
                self.assertEqual(PQEllipse.from_area_squared(e.n,e.area_over_pi_squared), e)
                self.assertEqual(PQEllipse.from_eccentricity(e.n,e.eccentricity), e)
                self.assertLessEqual(e.fermat_steps(),e.fermat_step_bound())
                result = fermat_factor(e.n,e.fermat_steps())
                self.assertEqual(result.factors[0]*result.factors[1], e.n)


class MaintenanceAuditTests(unittest.TestCase):
    def test_failed_audit_preserves_initial_stopped_state(self):
        scripts = Path(__file__).resolve().parents[1]/'scripts'
        with patch.object(sys, 'path', [str(scripts)]+sys.path):
            spec = importlib.util.spec_from_file_location('bounded_audit_fixture', scripts/'bounded_miner_proof_audit.py')
            mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); (root/'validation').mkdir(); (root/'monitor').mkdir()
            with patch.object(mod,'ROOT',root), patch.object(mod,'LOGS',root/'logs'), \
                 patch.object(mod.m,'OUT',root/'monitor'), \
                 patch.object(mod.service,'status',return_value={'running':False}), \
                 patch.object(mod.service,'start') as start, patch.object(mod.service,'stop') as stop, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(mod.main(),1)  # Deliberately missing prior proof revision.
            start.assert_not_called(); stop.assert_not_called()
            report = json.loads((root/'validation/miner-full-rebuild/report.json').read_text())
            self.assertIn('left stopped',report['mining_restoration'])


if __name__ == '__main__': unittest.main()
