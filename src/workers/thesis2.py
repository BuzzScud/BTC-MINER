"""Math port of reference/thesis2-math-in-pictures.html, 29 September 2026.

Integer operations use exact Python integers. The original picture geometry uses
floating point; the EllipseSearch/DynamicRods port in pqmath uses exact rationals.
The source describes these primitives, not a Bitcoin mining algorithm; the separate
Traversal class below is this application's nonce-ordering integration.
"""
from array import array
from functools import lru_cache
from itertools import combinations, product
from math import cos, sin, pi, sqrt, hypot, gcd, isqrt, prod
from hashlib import sha256
import struct
from . import ROOT
from .native import hash256
from .pqmath import is_prime as rods_is_prime, runtime_rod_state
from .prime_structure import unit_coordinates

SOURCE = ROOT / "reference/thesis2-math-in-pictures.html"
VERSION = "thesis2-field+flower-descriptors-2026-10-11"
SMALL_CLOCK = 360
BIG_CLOCK = 144000
WHEELS = (8, 9, 5)
BIG_WHEELS = (128, 9, 125)
FIELD_PRIME = 19
FIELD_GENERATOR = (1, 3)
NONCE_SPACE = 1 << 32

def dial_loop(modulus, step):
    if modulus <= 0:
        raise ValueError("Dial size must be positive")
    common = gcd(modulus, step)
    return {"loop": modulus // common, "every_mark": common == 1, "gcd": common}

def multiply_board(u, v):
    a,b = u; c,d = v
    return ((a*c-b*d) % FIELD_PRIME, (a*d+b*c) % FIELD_PRIME)

def centered19(value):
    value %= FIELD_PRIME
    return value - FIELD_PRIME if value > 9 else value

@lru_cache(maxsize=1)
def board_loop():
    point = (1, 0); points = []
    for _ in range(SMALL_CLOCK):
        points.append(point)
        point = multiply_board(point, FIELD_GENERATOR)
    return tuple(points)

def square_norm(x, y):
    return x*x+y*y

def hex_norm(x, y):
    return x*x-x*y+y*y

def lattice_points(norm, limit):
    if not 0 <= limit <= 1000000:
        raise ValueError("Lattice limit must be 0–1,000,000")
    # x²-xy+y² >= 3x²/4 and >= 3y²/4: integer-complete bound for both grids.
    radius = isqrt((4*limit+2)//3)+1
    return [(x,y,norm(x,y)) for x in range(-radius,radius+1)
            for y in range(-radius,radius+1) if norm(x,y) <= limit]

def prime_grid(prime):
    if not is_prime(prime) or prime <= 3:
        raise ValueError("Grid classification is for primes greater than 3")
    radius = isqrt((4*prime+2)//3)+1
    square = []; honeycomb = []
    for x in range(-radius,radius+1):
        for y in range(-radius,radius+1):
            if square_norm(x,y) == prime:
                square.append((x,y))
            if hex_norm(x,y) == prime:
                honeycomb.append((x,y))
    return {"prime":prime,"mod12":prime % 12,"square":square,"honeycomb":honeycomb}

def reading(value, wheels=WHEELS):
    return tuple(value % m for m in wheels)

@lru_cache(maxsize=8)
def crt_weights(wheels):
    if any(m < 2 for m in wheels) or any(gcd(a,b) != 1 for a,b in combinations(wheels,2)):
        raise ValueError("CRT wheels must be pairwise coprime and at least 2")
    modulus = prod(wheels)
    return modulus, tuple((modulus//m)*pow(modulus//m,-1,m) for m in wheels)

def from_reading(residues, wheels=WHEELS):
    wheels = tuple(wheels)
    if len(residues) != len(wheels):
        raise ValueError("One reading is required per CRT wheel")
    modulus,weights = crt_weights(wheels)
    return sum((r % m)*w for r,m,w in zip(residues,wheels,weights)) % modulus

def expand(denominator, base=60, max_digits=100000):
    if denominator < 2 or base < 2 or max_digits < 1:
        raise ValueError("Use denominator >= 2, base >= 2, max_digits >= 1")
    digits = []; remainders = []; seen = {1:0}; remainder = 1
    ends = False; cycle_start = -1
    while len(digits) < max_digits:
        digit,remainder = divmod(remainder*base,denominator)
        digits.append(digit); remainders.append(remainder)
        if remainder == 0:
            ends = True; break
        if remainder in seen:
            cycle_start = seen[remainder]; break
        seen[remainder] = len(digits)
    return {"digits":digits,"remainders":remainders,"ends":ends,"cycle_start":cycle_start,
            "truncated":not ends and cycle_start == -1}

def fraction_terminates(denominator, base=60):
    if denominator < 1 or base < 2:
        raise ValueError("Use a positive denominator and a base >= 2")
    while denominator != 1:
        common = gcd(denominator,base)
        if common == 1:
            return False
        denominator //= common
    return True

def is_prime(value):
    return rods_is_prime(value)

@lru_cache(maxsize=8)
def qualifying_primes(modulus=BIG_CLOCK):
    if modulus < 1:
        raise ValueError("Clock size must be positive")
    divisors = set()
    for d in range(1,isqrt(modulus)+1):
        if modulus % d == 0:
            divisors.update((d,modulus//d))
    return tuple(sorted(d+1 for d in divisors if d+1 >= 7 and is_prime(d+1)))

def gaussian_weights(count):
    if not 0 <= count <= 4096:
        raise ValueError("Use 0–4096 Gaussian places")
    out = []; a,b = 1,0
    for _ in range(count):
        out.append((a,b)); a,b = -a-b,a-b
    return out

def bits_value(bits):
    bits = tuple(bits)
    if any(d not in (0,1) for d in bits):
        raise ValueError("Gaussian digits must be 0 or 1, least significant first")
    weights = gaussian_weights(len(bits))
    return tuple(sum(d*w[axis] for d,w in zip(bits,weights)) for axis in (0,1))

def encode_gaussian(x, y):
    if not isinstance(x,int) or not isinstance(y,int):
        raise ValueError("Gaussian coordinates must be integers")
    digits = []
    while x or y:
        digit = (x+y) % 2; digits.append(digit); x -= digit
        x,y = (-x+y)//2,(-x-y)//2
        if len(digits) > 4096:
            raise ValueError("Gaussian encoding exceeded 4096 places")
    return digits

def signed_product(a, b):
    value = a*b
    return {"value":value,"magnitude":abs(value),"sign":(value>0)-(value<0)}

def vector_sum(u, v):
    if len(u) != len(v):
        raise ValueError("Vectors must have matching dimensions")
    return tuple(a+b for a,b in zip(u,v))

def mirror_vector(vector, axis=0):
    if not 0 <= axis < len(vector):
        raise ValueError("Mirror axis must name an existing coordinate")
    return tuple(-value if i == axis else value for i,value in enumerate(vector))

def unit_vector_sum(theta_degrees):
    if not 0 <= theta_degrees <= 180:
        raise ValueError("The source's angle is between 0 and 180 degrees")
    return 2*cos(theta_degrees*pi/360)

def neighbors_honeycomb_pair():
    return [(cos(k*pi/3),sin(k*pi/3),0,0) for k in range(6)] + [
        (0,0,cos(k*pi/3),sin(k*pi/3)) for k in range(6)]

def neighbors_24cell():
    out = []; scale = 1/sqrt(2)
    for i,j in combinations(range(4),2):
        for a,b in product((-1,1),repeat=2):
            value = [0,0,0,0]; value[i] = a*scale; value[j] = b*scale
            out.append(tuple(value))
    return out

def circle_gap(dx, dy):
    return hypot(dx,dy)-2/sqrt(pi)

def square_roots_of_one():
    # The four roots modulo 128, two modulo 9, and two modulo 125 combine independently.
    return sorted(from_reading(r,BIG_WHEELS) for r in product((1,63,65,127),(1,8),(1,124)))

@lru_cache(maxsize=2)
def traversal_labels(order='field'):
    if order=='field': return tuple(a+19*b-1 for a,b in board_loop())
    if order=='flower':
        from .archive_math import flower_nonce_labels
        return flower_nonce_labels()
    raise ValueError('Traversal order must be field or flower')


class OffsetDescriptor:
    """Versioned 24-byte exact offset program; shared decoder is excluded.

    Version 1 preserves THESIS2's field order. Version 2 uses flower addresses.
    Header, first tile and in-flight work are separate; this is not a checkpoint.
    """
    def __init__(self,phase,exponent_phase,cell_phase,step,prime,order='field'):
        values=(phase,exponent_phase,cell_phase,step,prime)
        if any(type(v) is not int for v in values): raise ValueError('Descriptor fields must be integers')
        if not (0<=phase<144000 and 0<=exponent_phase<360 and 0<=cell_phase<400
                and 0<step<360 and gcd(step,360)==1 and 0<prime<2**32 and gcd(prime,400)==1):
            raise ValueError('Invalid traversal descriptor')
        traversal_labels(order)
        self.phase,self.exponent_phase,self.cell_phase,self.step,self.prime=values
        self.order=order

    def packed(self):
        return struct.pack('<6I',1 if self.order=='field' else 2,self.phase,self.exponent_phase,self.cell_phase,self.step,self.prime)

    @classmethod
    def from_packed(cls,data):
        if len(data)!=24: raise ValueError('Traversal descriptor must contain 24 bytes')
        version,*values=struct.unpack('<6I',data)
        if version not in (1,2): raise ValueError('Unknown traversal descriptor version')
        return cls(*values,order='field' if version==1 else 'flower')

    def residues(self):
        labels=traversal_labels(self.order)
        return array('H',(labels[(self.exponent_phase+k*self.step)%360] for k in range(360)))

    def offset(self,index):
        if type(index) is not int or not 0<=index<144000: raise ValueError('Offset index must be 0..143999')
        cell,k=divmod(index,360)
        label=traversal_labels(self.order)[(self.exponent_phase+k*self.step)%360]
        return (360*((self.cell_phase+cell*self.prime)%400)+self.phase+label)%144000


class Traversal:
    """Application-defined full-domain traversal composed from the source primitives.

    Every full 144000 tile is a permutation of 400 cells × 360 residues.
    The final partial tile excludes out-of-range values; it never wraps them.
    The native descriptor path stores 360 labels, materializing no offset table.
    Older native libraries and explicit offset inspection use a lazy table.
    """
    def __init__(self, header, step=7, prime=19, workspace=None, order='field'):
        if len(header) != 80:
            raise ValueError("Mining headers must have 80 bytes")
        self.step_coordinates=unit_coordinates(step)
        if type(prime) is not int or prime not in qualifying_primes():
            raise ValueError("THESIS2 prime must be one of the 35 qualifying primes")
        self.step,self.prime = step,prime
        # Domain separator makes the application mapping explicit; not a theorem or predictor.
        self.seed = int.from_bytes(hash256(b"BTC-MINER/THESIS2/v1\0"+header[:76])[:8],"little")
        self.phase = self.seed % BIG_CLOCK
        self.exponent_phase = (self.seed//BIG_CLOCK) % SMALL_CLOCK
        self.cell_phase = (self.seed//(BIG_CLOCK*SMALL_CLOCK)) % 400
        self.tile_count = (NONCE_SPACE+BIG_CLOCK-1)//BIG_CLOCK
        self.first_tile = (self.seed//(BIG_CLOCK*SMALL_CLOCK*400)) % self.tile_count
        self.order=order
        self.descriptor=OffsetDescriptor(self.phase,self.exponent_phase,self.cell_phase,step,prime,order)
        self._offsets=None
        self.workspace=workspace
        if workspace is not None and order=='field':
            self.residues=workspace.residues(self.exponent_phase,step)
        else:
            self.residues=self.descriptor.residues()
        if list(self.residues)!=list(self.descriptor.residues()) or sorted(self.residues)!=list(range(360)):
            raise ArithmeticError('Traversal labels disagree with the exact descriptor')
        from .scale_graph import traversal_trace
        self.scale_trace=traversal_trace(self.phase,self.cell_phase,self.prime,self.residues)
        if self.scale_trace['offset']!=self.descriptor.offset(0):
            raise ArithmeticError('Rod tower and traversal formula disagree')

    @property
    def offsets(self):
        if self._offsets is None:
            self._offsets=self.workspace.offsets if self.workspace is not None else array('I',[0])*BIG_CLOCK
            if self.workspace is not None and self.workspace.hasher.project_offsets(self.residues,self.phase,self.cell_phase,self.prime,self._offsets):
                return self._offsets
            for i in range(400):
                base=360*((self.cell_phase+i*self.prime)%400)+self.phase
                for k,residue in enumerate(self.residues): self._offsets[i*360+k]=(base+residue)%BIG_CLOCK
        return self._offsets

    def iter_offsets(self):
        for i in range(400):
            base=360*((self.cell_phase+i*self.prime)%400)+self.phase
            for residue in self.residues: yield (base+residue)%BIG_CLOCK

    def nonces(self):
        for turn in range(self.tile_count):
            tile = (self.first_tile+turn) % self.tile_count
            base = tile*BIG_CLOCK
            limit = min(BIG_CLOCK,NONCE_SPACE-base)
            for offset in self.iter_offsets():
                if offset < limit:
                    yield base+offset

    def batches(self, size, single=False):
        batch = []
        for nonce in self.nonces():
            batch.append(nonce)
            if single:
                yield {"nonces":batch}; return
            if len(batch) == size:
                yield {"nonces":batch}; batch = []
        if batch:
            yield {"nonces":batch}

    def rank(self, nonce):
        if not 0 <= nonce < NONCE_SPACE:
            raise ValueError("Nonce must be a uint32")
        tile,offset = divmod(nonce,BIG_CLOCK)
        turns = (tile-self.first_tile) % self.tile_count
        before = turns*BIG_CLOCK
        partial_turn = (self.tile_count-1-self.first_tile) % self.tile_count
        if partial_turn < turns:
            before -= self.tile_count*BIG_CLOCK-NONCE_SPACE
        index = self.offsets.index(offset)
        if tile == self.tile_count-1:
            remainder = NONCE_SPACE-tile*BIG_CLOCK
            index = sum(n < remainder for n in self.offsets[:index])
        return before+index

    def description(self):
        return {"strategy_version":VERSION,"mapping_version":"btc-traversal-v1" if self.order=='field' else 'btc-flower-traversal-v1',
                "order":self.order,"descriptor_hex":self.descriptor.packed().hex(),"descriptor_payload_bytes":24,
                "label_buffer_bytes":len(self.residues)*2,
                "scale_graph":self.scale_trace,
                "label_carrier":"GF(19^2) nonzero points" if self.order=='field' else 'Eisenstein two-digit flower addresses modulo (5+2*omega)^2; Z/361 nonzero classes',
                "step":self.step,"qualifying_prime":self.prime,"clock":SMALL_CLOCK,"big_clock":BIG_CLOCK,
                "step_basis":{"primes":[11,19,73,109],"periods":[6,2,4,2],
                              "coordinates":list(self.step_coordinates),"carrier":"multiplicative units modulo 360"},
                "phase":self.phase,"field_exponent_phase":self.exponent_phase,
                "cell_phase":self.cell_phase,"first_tile":self.first_tile,"tile_count":self.tile_count,
                "nonce_space":NONCE_SPACE,"offset_table_bytes":0 if self._offsets is None else len(self._offsets)*self._offsets.itemsize,
                "prime_selection":"DynamicRods certified-window primality",
                "mapping_note":"New miner integration of source math; not supplied or proof-checked by the HTML."}

def report(header, step=7, prime=19, order='field'):
    from itertools import islice
    from .pqmath import report as ellipse_rods_report
    from .coreprimes import report as core_primes_report
    from .rodmath import report as rod_math_report
    plan = Traversal(header,step,prime,order=order)
    field = board_loop(); roots = square_roots_of_one(); primes = qualifying_primes()
    point = tuple(centered19(v) for v in field[plan.exponent_phase])
    encoded = encode_gaussian(*point)
    return {**plan.description(),"source_file":str(SOURCE),"source_sha256":sha256(SOURCE.read_bytes()).hexdigest(),
            "first_20_nonces":list(islice(plan.nonces(),20)),
            "clock":{"360_step":dial_loop(360,step),"144000_step":dial_loop(144000,step)},
            "field19":{"generator":FIELD_GENERATOR,"points":len(field),"quarter_turn":field[90],
                       "point":point,"after_360":multiply_board(field[-1],FIELD_GENERATOR)},
            "grids":{str(p):prime_grid(p) for p in (7,19)},
            "crt":{"360_wheels":WHEELS,"144000_wheels":BIG_WHEELS,
                   "19_reading":reading(19),"361_small_reading":reading(361),
                   "reconstructed19":from_reading(reading(19))},
            "base60":{"one_third":expand(3,60),"one_seventh":expand(7,60),
                      "one_third_base10":expand(3,10)},
            "qualifying_primes":{"rule":"p >= 7 prime and (p - 1) divides 144000","count":len(primes),"values":primes},
            "ellipse_and_rods":ellipse_rods_report(),
            "core_primes":core_primes_report(BIG_CLOCK),
            "rods_flowers_towers":rod_math_report(),
            "runtime_prime_rods":runtime_rod_state(),
            "signs":{"3_times_minus4":signed_product(3,-4),
                     "same_direction_sum":vector_sum((1,0),(1,0)),
                     "opposite_direction_sum":vector_sum((1,0),(-1,0)),
                     "global_mirror_sum":vector_sum(mirror_vector((1,0)),mirror_vector((0,1))),
                     "unit_sum_by_angle":{str(a):unit_vector_sum(a) for a in (0,90,180)}},
            "gaussian_bits":{"base":[-1,1],"place_weights":gaussian_weights(8),
                             "fourth_power":gaussian_weights(9)[4],"eighth_power":gaussian_weights(9)[8],
                             "point":point,"digits_lsb_first":encoded,"decoded":bits_value(encoded),
                             "byte_states":1<<8,"bits_for_60_by_60_cell":(3600-1).bit_length()},
            "fix_19_squared":{"mod360":pow(19,2,360),"mod144000":pow(19,2,144000),
                              "roots_mod144000":roots,"smallest_above_one":roots[1],
                              "qualifying_roots":[p for p in primes if pow(p,2,144000)==1]},
            "packing4d":{"honeycomb_neighbors":neighbors_honeycomb_pair(),"cell24_neighbors":neighbors_24cell(),
                         "honeycomb_fill":pi*pi/24,"cell24_fill":pi*pi/16,"ratio":1.5,
                         "scope":"Diagnostic geometry; not a 500D packing claim or a nonce exclusion rule."},
            "circles":{"equal_area_radius":1/sqrt(pi),"shift":[.5,.5],"gap":circle_gap(.5,.5),
                       "tangent_center_distance":2/sqrt(pi),"distance_scale_to_tangency":2*sqrt(2/pi)},
            "source_status":{"source_reports_theorems":2028,"source_reports_files":145,"included_through_run":37,
                             "run38_included":False,"lean_artifacts_in_package":False,
                             "mining_speedup_claimed":False,"implementation_tests_run":True,
                             "test_scope":"Offline traversal and selected math regression checks; no Lean proof or live mining validation"}}
