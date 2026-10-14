"""Versioned symbolic candidate transport for the BTC pruning connection.

Three exact grammars: additive orbits in Z/(2^32), bounded CRT offset points,
and supported Q=(k, within-k index) references. Frames and their ordering are
shared, fingerprinted constants. Fingerprints identify models; they are not
proofs or authentication. Decode validates reconstruction bounds. The sender
checks exact replay and compares complete JSON wire sizes before selection.

The general ResidueFrame uses Python arbitrary-precision integers. The nonce
protocol intentionally admits only 0..2^32-1, at most 64 per worker request.
No rule changes candidate membership or supplies SHA256d exclusion authority.
"""
import base64
import hashlib
import json
import struct
from dataclasses import dataclass, field
from functools import lru_cache
from types import MappingProxyType
from .product_tree_crt import ProductTreeCRT

MAGIC = b'NG1'
LIMIT = 1 << 32
MAX_COUNT = 64
# Existing core clock rods plus flower127; these are transport coordinates,
# not a claim that this rod set has special SHA256d behavior.
MODULI = (11, 19, 71, 97, 109, 127)
RAW_ID = hashlib.sha256(b'btc-geometry/v1;raw;uint32;big-endian;ordered').digest()
ORBIT_ID = hashlib.sha256(b'btc-geometry/v1;orbit;Z/4294967296;start+i*step;ordered').digest()


def integer(value, name, low=0, high=None):
    if type(value) is not int or value < low or (high is not None and value > high):
        raise ValueError(name+' outside the exact integer domain')
    return value


def pack_fields(fields):
    out = bytearray(); acc = used = 0
    for value, width in fields:
        integer(width, 'bit width')
        integer(value, 'field', 0, (1 << width)-1)
        acc |= value << used; used += width
        while used >= 8:
            out.append(acc & 255); acc >>= 8; used -= 8
    if used:
        out.append(acc)
    return bytes(out)


class Bits:
    def __init__(self, data):
        self.data = data; self.pos = self.acc = self.used = 0

    def take(self, width):
        integer(width, 'bit width')
        while self.used < width:
            if self.pos == len(self.data):
                raise ValueError('Truncated bit stream')
            self.acc |= self.data[self.pos] << self.used
            self.pos += 1; self.used += 8
        value = self.acc & ((1 << width)-1)
        self.acc >>= width; self.used -= width
        return value

    def finish(self):
        if self.pos != len(self.data) or self.acc:
            raise ValueError('Trailing bytes or nonzero padding')


@dataclass(frozen=True)
class ResidueFrame:
    moduli: tuple
    tree: ProductTreeCRT = field(init=False, repr=False)
    fingerprint: bytes = field(init=False)
    widths: tuple = field(init=False)

    def __post_init__(self):
        tree = ProductTreeCRT(tuple(self.moduli))
        if not tree.moduli:
            raise ValueError('A transport frame must have at least one rod')
        object.__setattr__(self, 'moduli', tree.moduli)
        object.__setattr__(self, 'tree', tree)
        object.__setattr__(self, 'widths', tuple((m-1).bit_length() for m in tree.moduli))
        # Binary length prefixes avoid decimal-conversion limits on huge rods.
        identity = bytearray(b'btc-geometry/v1;CRT;standard-residue-basis;ordered;')
        for m in tree.moduli:
            raw = m.to_bytes((m.bit_length()+7)//8, 'big')
            identity += len(raw).to_bytes(8, 'big')+raw
        object.__setattr__(self, 'fingerprint', hashlib.sha256(identity).digest())

    @property
    def capacity(self):
        return self.tree.capacity

    def pack(self, values, bound):
        integer(bound, 'bound', 0, self.capacity-1)
        fields = []
        for value in values:
            integer(value, 'point', 0, bound)
            fields.extend(zip(self.tree.encode(value), self.widths))
        return pack_fields(fields)

    def unpack(self, data, count, bound):
        integer(count, 'count'); integer(bound, 'bound', 0, self.capacity-1)
        if len(data) != (count*sum(self.widths)+7)//8:
            raise ValueError('Incorrect residue payload size')
        bits = Bits(data); out = []
        for _ in range(count):
            residues = tuple(bits.take(w) for w in self.widths)
            if any(r >= m for r,m in zip(residues,self.moduli)):
                raise ValueError('Noncanonical residue')
            value = self.tree.decode(residues)
            if value > bound:
                raise ValueError('Reconstruction contradicts the bound')
            out.append(value)
        bits.finish()
        return out


@lru_cache(maxsize=1)
def frames():
    return tuple(ResidueFrame(MODULI[:i]) for i in range(1,len(MODULI)+1))


@dataclass(frozen=True)
class QFrame:
    scale: int
    clocks: tuple
    groups: tuple
    routes: object = field(repr=False)
    factors: object = field(repr=False)
    fingerprint: bytes
    source_array_bytes: int

    def coordinates(self, value):
        ci,index = self.routes[value]
        p,q = self.factors[value]
        return {'k':self.clocks[ci], 'index':index, 'p':p, 'q':q}


@lru_cache(maxsize=3)
def q_model(scale):
    from .scaled_abacus import q_codec, SCALES
    integer(scale, 'Q scale')
    if scale not in SCALES:
        raise ValueError('Unrecognized Q scale')
    codec = q_codec(scale)
    clocks = tuple(sorted(codec.groups))
    groups = tuple(tuple(codec.decode(code) for code in codec.groups[k]) for k in clocks)
    routes = {value:(i,j) for i,group in enumerate(groups) for j,value in enumerate(group)}
    factors = {value:(int(p),value//p) for value,p in zip(codec.values,codec.small_factors)}
    identity = hashlib.sha256(b'btc-geometry/v1;Q;k-sorted;within-k-by-Q;'+str(scale).encode())
    for k,group in zip(clocks,groups):
        identity.update(struct.pack('>QQ',k,len(group)))
        for value in group:
            identity.update(struct.pack('>Q',value))
    # Snapshot numeric arrays/groups rather than retaining mutable resident tables.
    return QFrame(scale,clocks,groups,MappingProxyType(routes),MappingProxyType(factors),
                  identity.digest(),codec.description()['table_payload_bytes'])


def envelope(mode, count, identity, body):
    return base64.b64encode(MAGIC+bytes([mode,count])+identity+body).decode('ascii')


def encode_points(values, mode):
    values = list(values)
    integer(len(values), 'count', 1, MAX_COUNT)
    for value in values:
        integer(value, 'nonce', 0, LIMIT-1)
    from .geometry_predictive import NAMES, identity, encode_body
    if mode in NAMES:
        code=NAMES.index(mode)
        raw=b'NG2'+bytes([code,len(values)])+identity(code)+encode_body(values,code)
        return base64.b64encode(raw).decode('ascii')
    if mode == 'raw32':
        return envelope(3,len(values),RAW_ID,struct.pack('>'+str(len(values))+'I',*values))
    if mode == 'orbit':
        start = values[0]
        step = (values[1]-start) % LIMIT if len(values)>1 else 0
        if any(value != (start+i*step) % LIMIT for i,value in enumerate(values)):
            raise ValueError('Points are not one additive orbit')
        return envelope(0,len(values),ORBIT_ID,struct.pack('>II',start,step))
    if mode == 'residue':
        origin = min(values); bound = max(values)-origin
        selected = next(f for f in frames() if f.capacity > bound)
        body = bytes([len(selected.moduli)])+struct.pack('>II',origin,bound)
        body += selected.pack([v-origin for v in values],bound)
        return envelope(1,len(values),frames()[-1].fingerprint,body)
    if mode == 'q-route':
        # Fixed reviewed scale in v1. No receiver-selected arbitrary dictionary.
        model = q_model(33264000)
        clocks, routes, identity = model.clocks, model.routes, model.fingerprint
        fields = []
        for value in values:
            if value not in routes:
                raise ValueError('Point outside Q family')
            ci, index = routes[value]
            fields.extend(((ci,(len(clocks)-1).bit_length()),
                           (index,(len(model.groups[ci])-1).bit_length())))
        return envelope(2,len(values),identity,pack_fields(fields))
    raise ValueError('Unknown point grammar')


def decode_points(encoded):
    if not isinstance(encoded,str) or len(encoded)>4096:
        raise ValueError('Invalid or oversized geometry envelope')
    try:
        raw = base64.b64decode(encoded,validate=True)
    except (ValueError, UnicodeError) as error:
        raise ValueError('Invalid base64 envelope') from error
    if base64.b64encode(raw).decode('ascii') != encoded or len(raw)<37 or raw[:3] not in (MAGIC,b'NG2'):
        raise ValueError('Noncanonical or unknown geometry envelope')
    mode,count = raw[3:5]; identity=raw[5:37];body=raw[37:]
    integer(count,'count',1,MAX_COUNT)
    if raw[:3]==b'NG2':
        from .geometry_predictive import identity as expected_identity, decode_body
        if identity!=expected_identity(mode):
            raise ValueError('NG2 model fingerprint mismatch')
        return decode_body(body,count,mode)
    if mode == 0:
        if identity!=ORBIT_ID or len(body)!=8:
            raise ValueError('Wrong orbit frame or payload size')
        start,step=struct.unpack('>II',body)
        if count==1 and step!=0:
            raise ValueError('Noncanonical singleton orbit')
        return [(start+i*step)%LIMIT for i in range(count)]
    if mode == 1:
        if identity!=frames()[-1].fingerprint or len(body)<9:
            raise ValueError('Wrong CRT frame or truncated bound')
        prefix=body[0];integer(prefix,'rod prefix',1,len(MODULI))
        origin,bound=struct.unpack('>II',body[1:9]); selected=frames()[prefix-1]
        if origin+bound>=LIMIT or bound>=selected.capacity or (prefix>1 and frames()[prefix-2].capacity>bound):
            raise ValueError('Invalid or nonminimal capacity certificate')
        offsets=selected.unpack(body[9:],count,bound)
        if min(offsets)!=0 or max(offsets)!=bound:
            raise ValueError('Noncanonical segment bounds')
        return [origin+n for n in offsets]
    if mode == 2:
        model=q_model(33264000)
        clocks,expected=model.clocks,model.fingerprint
        if identity!=expected:
            raise ValueError('Q dictionary fingerprint mismatch')
        bits=Bits(body);out=[]
        for _ in range(count):
            ci=bits.take((len(clocks)-1).bit_length())
            if ci>=len(clocks):
                raise ValueError('Invalid clock route')
            index=bits.take((len(model.groups[ci])-1).bit_length())
            if index>=len(model.groups[ci]):
                raise ValueError('Invalid within-k index')
            value=model.groups[ci][index]
            integer(value,'decoded nonce',0,LIMIT-1)
            out.append(value)
        bits.finish()
        return out
    if mode == 3:
        if identity!=RAW_ID or len(body)!=count*4:
            raise ValueError('Wrong raw32 frame or payload size')
        return list(struct.unpack('>'+str(count)+'I',body))
    raise ValueError('Unknown point grammar')


def wire_size(request):
    return len((json.dumps(request)+'\n').encode())


def compact_request(request, *, allow_predictive=False):
    """Choose only a strictly smaller complete message; preserve raw on failure."""
    values=request['nonces'];best=request;size=wire_size(request);mode='raw'
    from .geometry_predictive import NAMES
    modes=('orbit','residue','q-route','raw32')+(NAMES if allow_predictive else ())
    for candidate in modes:
        try:
            encoded=encode_points(values,candidate)
            if decode_points(encoded)!=values:
                continue
            message={k:v for k,v in request.items() if k!='nonces'}
            message['nonce_geometry']=encoded
            cost=wire_size(message)
            if cost<size:
                best,size,mode=message,cost,candidate
        except (ValueError,OverflowError,ArithmeticError):
            continue
    return best, {'mode':mode,'raw_wire_bytes':wire_size(request),'wire_bytes':size,
                  'saved_bytes':wire_size(request)-size}


def describe_points(encoded):
    values=decode_points(encoded)
    raw=base64.b64decode(encoded)
    if raw[:3]==b'NG2':
        from .geometry_predictive import metadata
        return {'version':2,'count':len(values),'values':values,**metadata(values,raw[3])}
    mode=('orbit','residue','q-route','raw32')[raw[3]]
    result={'version':1,'mode':mode,'count':len(values),'frame_fingerprint':raw[5:37].hex(),
            'values':values,'proof_scope':'Validated exact replay; not a formal proof of the implementation'}
    if mode=='orbit':
        start,step=struct.unpack('>II',raw[37:]);result.update(start=start,step=step,modulus=LIMIT)
    elif mode=='residue':
        origin,bound=struct.unpack('>II',raw[38:46]);frame=frames()[raw[37]-1]
        result.update(origin=origin,bound=bound,moduli=list(frame.moduli),capacity=frame.capacity)
    elif mode=='q-route':
        model=q_model(33264000)
        result.update(scale=model.scale,routes=[model.coordinates(v) for v in values])
    return result


def transport_check():
    from random import Random
    rng=Random(19)
    model=q_model(33264000)
    cases={'small_raw':[1,2,3], 'wrapped_orbit':[(LIMIT-30+7*i)%LIMIT for i in range(64)],
           'bounded_points':[3000000000+rng.randrange(11) for _ in range(64)],
           'Q_family':[n for n in sorted(model.routes) if n<LIMIT][-64:],
           'unstructured':[rng.randrange(LIMIT) for _ in range(64)]}
    cases.update(correlated_jitter=[3000000000+i*i for i in range(64)],
                 low_shell_region=[rng.randrange(60) for _ in range(64)],
                 adaptive_runs=[0]*16+[300]*16+[20000]*16+[3000000000]*16)
    f=frames()[4]
    anchors=[0,f.capacity-1]+[f.tree.decode([rng.choice((0,1,m-1)) for m in f.moduli]) for _ in range(62)]
    cases['anchor_clusters']=[3000000000+x for x in anchors]
    cases['mixed_continuity']=[3000000000]*24+[3000000000+rng.randrange(100000000) for _ in range(16)]+[3010000000]*24
    rows=[]
    for name,values in cases.items():
        request={'model':'bitcoin-sha256d-v1','header':'00'*80,'target':str((1<<256)-1),'nonces':values,'budget_ms':1}
        packed,stats=compact_request(request,allow_predictive=True)
        decoded=decode_points(packed['nonce_geometry']) if 'nonce_geometry' in packed else packed['nonces']
        from .geometry_predictive import NAMES
        costs={}
        for mode in ('orbit','residue','q-route','raw32')+NAMES:
            try:
                candidate=encode_points(values,mode)
                costs[mode]=wire_size({**{k:v for k,v in request.items() if k!='nonces'},'nonce_geometry':candidate})
            except ValueError:
                costs[mode]=None
        rows.append({'case':name,'mode_wire_bytes':costs,**stats,'packed_raw_nonce_bytes':4*len(values),'ok':decoded==values and stats['wire_bytes']<=stats['raw_wire_bytes']})
    from .geometry_predictive import capability
    startup=(wire_size({'x':0,'geometry_offer':True})-wire_size({'x':0})
             +wire_size({'x':0,'geometry_capability':capability()})-wire_size({'x':0}))
    return {'ok':all(row['ok'] for row in rows),'cases':rows,'negotiation_startup_bytes':startup,
            'cost_scope':'Cases compare candidate request bytes after negotiation; each new worker adds the separately reported one-time offer/response overhead. First request uses NG1.','scope':'Synthetic worker-request transport only; no hashrate or arbitrary-file compression claim',
            'shared_frame':{'moduli':list(MODULI),'fingerprint':frames()[-1].fingerprint.hex()},
            'Q_dictionary_array_bytes':model.source_array_bytes,
            'memory_note':'Source array bytes only; immutable geometry snapshot and Python object overhead are additional'}
