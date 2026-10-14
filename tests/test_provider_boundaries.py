"""Adversarial input, exact numeric parsing and byte-preserving codec tests."""
import hashlib
import math
import random
import struct
import unittest
from fractions import Fraction
from unittest.mock import Mock
from btcminer import provider, tcmp


class ProviderBoundaries(unittest.TestCase):
    def test_numeric_fraction_sentinel_uses_actual_value(self):
        self.assertEqual(provider.evaluation_number({'ok':True,'value':'1.25','daemon':{'fraction':'none'}}),Fraction(5,4))
        self.assertEqual(provider.evaluation_number({'ok':True,'value':'0.333','daemon':{'fraction':'1/3'}}),Fraction(1,3))
        for value in ('NaN','Infinity',None,True):
            with self.assertRaises(provider.ProviderError):provider.evaluation_number({'ok':True,'value':value})
    def test_failed_or_malformed_fraction_cannot_be_hidden_by_display(self):
        for row in ({'ok':False,'value':'7'}, {'ok':True,'value':'7','daemon':{'fraction':'garbage'}},
                    {'ok':True,'value':'7','daemon':{'fraction':'1/0'}}, {'ok':True,'daemon':[]}):
            with self.assertRaises(provider.ProviderError):provider.evaluation_number(row)
    def test_all_bit_mutations_are_rejected_or_preserve_exact_payload(self):
        # Metadata alternatives may be valid encodings. What must never pass
        # is a different payload with an unchanged original integrity checksum.
        data=bytes(range(31));frames=[tcmp.encode(data,m) for m in ('network','auto')]
        for original in frames:
            for index in range(len(original)):
                for bit in range(8):
                    mutated=bytearray(original);mutated[index]^=1<<bit
                    try:actual=tcmp.decode(mutated,max_output=len(data))
                    except tcmp.CodecError:continue
                    self.assertEqual(actual,data,(index,bit))
    def test_all_mode_truncations_and_trailing_junk(self):
        for mode in tcmp.MODES:
            frame=tcmp.encode(bytes(range(41)),mode)
            for n in range(len(frame)):
                with self.assertRaises(tcmp.CodecError):tcmp.decode(frame[:n])
            with self.assertRaises(tcmp.CodecError):tcmp.decode(frame+b'\x00')
    def test_seeded_larger_roundtrip_and_limit_boundaries(self):
        rng=random.Random(20261013)
        for n in (55,56,63,64,65,255,256,257,65535,65536,65537):
            data=bytes(rng.randrange(256) for _ in range(n))
            for mode in ('network','auto'):
                frame=tcmp.encode(data,mode,max_input=n)
                self.assertEqual(tcmp.decode(frame,max_output=n),data)
                with self.assertRaises(tcmp.CodecError):tcmp.decode(frame,max_output=n-1)
                with self.assertRaises(tcmp.CodecError):tcmp.encode(data,mode,max_input=n-1)
    def test_tiny_malformed_frames_cannot_claim_large_allocations(self):
        for length in (2**32,2**63,2**64-1):
            frame=tcmp.HEADER.pack(b'TCMP',1,5,0,5,length,0)+bytes(16)
            with self.assertRaisesRegex(tcmp.CodecError,'limit'):tcmp.decode(frame,max_output=65536)

    def test_aristotle_crt_capacity_hypotheses_at_adaptive_transitions(self):
        # DynamicRods.extendEquiv requires coprimality. An integer lift also
        # requires a declared capacity interval; residues alone give a class.
        for algorithm in range(1,6):
            primes,width,_=tcmp.parameters(algorithm);capacity=math.prod(primes)
            self.assertGreaterEqual(capacity,256**width)
            for i,p in enumerate(primes):
                for q in primes[:i]:self.assertEqual(math.gcd(p,q),1)
            values={0,1,256**width-1}
            for i in range(1,len(primes)+1):
                boundary=math.prod(primes[:i])
                values.update(v for v in (boundary-1,boundary,boundary+1) if 0<=v<256**width)
            for value in values:
                # Independent direct CRT sum, separate from decoder's Garner recurrence.
                reconstructed=sum((value%p)*(capacity//p)*pow(capacity//p,-1,p) for p in primes)%capacity
                self.assertEqual(reconstructed,value)
                raw=value.to_bytes(width,'little')
                mode=('network','file','progressive','constellation','auto')[algorithm-1]
                self.assertEqual(tcmp.decode(tcmp.encode(raw,mode)),raw)

if __name__=='__main__':unittest.main()
