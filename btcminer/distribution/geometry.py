"""Exact bounded regions in tile/cell/label coordinates, including padding.

Raw positions are not nonce ranks: the final tile contains invalid positions.
Refinement never drops those silently; valid cardinality is computed separately.
"""
from array import array
from bisect import bisect_left
import ctypes as C
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from ..thesis2 import Traversal
from . import PROTOCOL

WIDTH = 144000
TILES = 29827
END = WIDTH * TILES
NONCES = 1 << 32


def integer(value, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError('Integer outside permitted domain')
    return value


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


@lru_cache(maxsize=1)
def implementation():
    # Architecture-independent source binding; ARM and portable binaries differ.
    from .. import ROOT
    files = ['src/workers/thesis2.py', 'src/backends/native.py',
             'src/backends/hasher_fast.c', 'math-library/python/archive_math.py',
             'math-library/python/scale_graph.py']
    files += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT/'btcminer/distribution').glob('*.py'))]
    return hashlib.sha256(canonical({p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                                    for p in files}).encode()).hexdigest()


def job_spec(work, plan):
    spec = dict(protocol=PROTOCOL, implementation=implementation(),
                header=(work.header[:76]+bytes(4)).hex(), target=str(work.target),
                network_target=str(work.network_target), revision=str(work.generation),
                key=work.key, step=plan.step, prime=plan.prime, order=plan.order,
                descriptor=plan.descriptor.packed().hex(), first_tile=plan.first_tile)
    spec['id'] = hashlib.sha256(canonical(spec).encode()).hexdigest()
    return spec


class Geometry:
    def __init__(self, plan):
        self.plan = plan
        self.partial_start = ((TILES-1-plan.first_tile) % TILES)*WIDTH
        # Only 23296 positions are retained; no full-domain allocation.
        self.partial = array('I', (i for i, n in enumerate(plan.iter_offsets())
                                   if n < NONCES-(TILES-1)*WIDTH))
        self.labels_inverse = {n: k for k, n in enumerate(plan.residues)}
        self.prime_inverse = pow(plan.prime, -1, 400)

    @classmethod
    def from_spec(cls, spec):
        required = {'protocol','implementation','header','target','network_target',
                    'revision','key','step','prime','order','descriptor','first_tile','id'}
        if not isinstance(spec, dict) or set(spec) != required:
            raise ValueError('Invalid job descriptor')
        if spec['protocol'] != PROTOCOL or spec['implementation'] != implementation():
            raise ValueError('Worker implementation mismatch')
        for key in ('target', 'network_target'):
            if not isinstance(spec[key], str) or not spec[key].isascii() or not spec[key].isdecimal():
                raise ValueError('Target must be a decimal uint256')
            integer(int(spec[key]), 0, (1 << 256)-1)
        if not isinstance(spec['revision'], str) or not isinstance(spec['key'], str):
            raise ValueError('Invalid work revision')
        header = bytes.fromhex(spec['header'])
        if len(header) != 80 or header[76:] != bytes(4):
            raise ValueError('Invalid header binding')
        body = {k:v for k,v in spec.items() if k != 'id'}
        if hashlib.sha256(canonical(body).encode()).hexdigest() != spec['id']:
            raise ValueError('Job identity mismatch')
        plan = Traversal(header, spec['step'], spec['prime'], order=spec['order'])
        if plan.descriptor.packed().hex() != spec['descriptor'] or plan.first_tile != spec['first_tile']:
            raise ValueError('Traversal does not match job')
        return cls(plan)

    def count(self, start, stop):
        integer(start, 0, END); integer(stop, start, END)
        a = max(start, self.partial_start)
        b = min(stop, self.partial_start+WIDTH)
        if a >= b:
            return stop-start
        valid = bisect_left(self.partial, b-self.partial_start)-bisect_left(self.partial, a-self.partial_start)
        return stop-start-(b-a)+valid

    def nonce(self, raw):
        integer(raw, 0, END-1)
        turn, index = divmod(raw, WIDTH)
        cell, k = divmod(index, 360)
        offset = (360*((self.plan.cell_phase+cell*self.plan.prime) % 400)
                  +self.plan.phase+self.plan.residues[k]) % WIDTH
        value = ((self.plan.first_tile+turn) % TILES)*WIDTH+offset
        return value if value < NONCES else None

    def raw_index(self, nonce):
        integer(nonce, 0, NONCES-1)
        tile, offset = divmod(nonce, WIDTH)
        cell, label = divmod((offset-self.plan.phase) % WIDTH, 360)
        i = ((cell-self.plan.cell_phase)*self.prime_inverse) % 400
        return ((tile-self.plan.first_tile) % TILES)*WIDTH+i*360+self.labels_inverse[label]

    def batch(self, hasher, start, stop, capacity):
        integer(capacity, 1, 1000000)
        count = min(capacity, self.count(start, stop))
        if not count:
            return array('I'), stop
        plan = self.plan
        if hasher.fill_factored is not None:
            values = array('I', [0])*count
            labels = (C.c_uint16*360).from_buffer(plan.residues)
            output = (C.c_uint32*count).from_buffer(values)
            cursor = C.c_uint64(start)
            actual = hasher.fill_factored(labels, plan.phase, plan.cell_phase,
                plan.prime, plan.first_tile, C.byref(cursor), count, output)
            if actual != count or cursor.value > stop:
                raise ArithmeticError('Native generator crossed partition')
            end = cursor.value
        else:
            values = array('I'); end = start
            while end < stop and len(values) < count:
                nonce = self.nonce(end); end += 1
                if nonce is not None: values.append(nonce)
        # Advance over trailing padding without falsely counting it as hashed.
        if self.count(end, stop) == 0: end = stop
        return values, end


def children(start, stop):
    """Refine aligned tile ranges, then the 400-cell and 360-label towers.

    Residual intervals from progress/exclusion use balanced subdivision. All
    returned children are contiguous, disjoint and exactly cover their parent.
    """
    integer(start, 0, END-1); integer(stop, start+1, END)
    size = stop-start
    if size == 1: return []
    if start % WIDTH == stop % WIDTH == 0 and size > WIDTH:
        mid = start+(size//WIDTH//2)*WIDTH
        return [(start, mid), (mid, stop)]
    if start//WIDTH == (stop-1)//WIDTH and start % 360 == stop % 360 == 0 and size > 360:
        units = size//360
        base = next((b for b in (2, 5) if units % b == 0), 2)
        if units % base == 0:
            step = size//base
            return [(a, a+step) for a in range(start, stop, step)]
    if start//360 == (stop-1)//360:
        base = next((b for b in (2, 3, 5) if size % b == 0), None)
        if base:
            step = size//base
            return [(a, a+step) for a in range(start, stop, step)]
    mid = start+size//2
    return [(start, mid), (mid, stop)]
