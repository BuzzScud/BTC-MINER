"""Resident exact arithmetic/packing model and per-engine reusable workspace.

The model is immutable by convention; workspaces belong to one coordinator and
may be rebound only after that job's worker futures have drained. Geometry and
Golay addresses describe constrained sets, not compression of arbitrary hashes.
"""
from array import array
from functools import lru_cache
from itertools import combinations, product
import struct
import time
from .pqmath import RodAbacus
from .coreprimes import CORE, RADICAL


class ResidentModel:
    def __init__(self):
        from .thesis2 import board_loop
        begin=time.perf_counter()
        self.core=RodAbacus(CORE)
        self.core_squares=RodAbacus(tuple(p*p for p in CORE))
        self.binary=RodAbacus((2047,2048,2049))
        self.field=board_loop()
        # Exactly PackingLimits.golayRow: twelve linear generators, not a
        # probabilistic code generator. Store one 24-bit word per pair.
        words=[]
        for m in range(2048):
            v=0
            for i in range(11):
                if (m>>i)&1:v^=(0xC75<<i)^(1<<23)
            words.append(v.to_bytes(3,'little'))
        self.golay_pairs=b''.join(words)
        # Twice the coordinates of the 240 E8 roots; signed int8 is exact.
        roots=array('b')
        for i,j in combinations(range(8),2):
            for a,b in product((-2,2),repeat=2):
                row=[0]*8;row[i]=a;row[j]=b;roots.extend(row)
        for row in product((-1,1),repeat=8):
            if sum(x<0 for x in row)%2==0:roots.extend(row)
        self.e8_roots=roots.tobytes()
        self.core_geometry=tuple((p,p%4==1,p%3==1,p*p%360) for p in CORE)
        from .scaled_abacus import SCALES, q_codec
        from .recurrence import published_certificates
        self.q_codecs=tuple(q_codec(m) for m in SCALES)
        self.recurrence_certificates=published_certificates()
        from .shared_abacus import shared_pool
        self.shared_pool=shared_pool()
        self.shared_frame=self.shared_pool.frame(8192)
        self.header_frame=self.shared_pool.frame(640)
        self.word_frame=self.shared_pool.frame(64)
        self.label_frame=self.shared_pool.frame(16)
        from .research_system import claims
        self.claim_registry=claims()
        # The calculator class creates per-caller mutable slots on this pool.
        from .claim_calculus import ClaimCalculator
        self.claim_calculator_type=ClaimCalculator
        from .archive_math import Flower, clock_tables, clock_geometry, clock_flags, CircleModel
        self.flower19=Flower(2)
        self.clock_tables=clock_tables()
        self.clock_geometry=clock_geometry()
        self.clock_flags=clock_flags()
        self.circle_model=CircleModel
        self.load_seconds=time.perf_counter()-begin

    def golay(self,message):
        if not isinstance(message,int) or not 0<=message<4096:
            raise ValueError('Golay message must fit 12 bits')
        # golay(0xAE3) is all ones. Remove bit 11 by complementing its pair.
        polarity=message>>11
        representative=message^(0xAE3 if polarity else 0)
        offset=3*representative
        word=int.from_bytes(self.golay_pairs[offset:offset+3],'little')
        return word^(0xffffff if polarity else 0)

    def pack_word(self,value):
        if not isinstance(value,int) or not 0<=value<1<<32:
            raise ValueError('Word must be uint32')
        a,b,c=self.binary.reading(value)
        return a|(b<<11)|(c<<22)  # 11 + 11 + 12 = 34 independent residue bits.

    def unpack_word(self,packed):
        if not isinstance(packed,int) or not 0<=packed<1<<34:
            raise ValueError('Packed rods must fit 34 bits')
        residues=(packed&2047,(packed>>11)&2047,packed>>22)
        if any(r>=m for r,m in zip(residues,self.binary.rods)):
            raise ValueError('Noncanonical rod residue')
        value=self.binary.reconstruct(residues)
        if value>=1<<32:raise ValueError('Rod reading is outside the uint32 domain')
        return value

    def description(self):
        return {'core_primes':list(CORE),'core_radical':RADICAL,'core_exponent':30240,
                'binary_rods':list(self.binary.rods),'binary_capacity':self.binary.capacity,
                'binary_capacity_bits':self.binary.capacity.bit_length(),
                'independent_residue_bits':34,'golay_pair_count':2048,
                'golay_codeword_count':4096,'golay_table_bytes':len(self.golay_pairs),
                'e8_root_count':240,'e8_table_bytes':len(self.e8_roots),
                'flower19_digit_count':self.flower19.base.N,
                'flower19_boundary':self.flower19.boundary(),
                'clock_period':len(self.clock_tables),
                'clock_symmetries':len(self.clock_flags[1])//24,
                'clock_flags_packed_bytes':sum(len(x) for x in self.clock_flags[1:]),
                'clock_geometry':{'vertices':len(self.clock_geometry[0]),'cells':len(self.clock_geometry[1])},
                'q_compression':[c.description() for c in self.q_codecs],
                'recurrence_certificates':self.recurrence_certificates,
                'shared_abacus':{**self.shared_frame.description(),
                    'root_builds':self.shared_pool.builds,
                    'use':'Header columns, core word residues and THESIS2 board formula; views share inverse tables'},
                'research_registry':{'claims':len(self.claim_registry['claims']),
                    'claim_calculus':'Integer equality, divisibility, order, Boolean combinations; reusable shared rods',
                    'path':'research/claims.json','inspect_command':'/abacus claims',
                    'study_command':'/abacus study --precision-bits 16384'},
                'load_seconds':self.load_seconds,
                'scope':'Exact resident arithmetic and geometric tables; no proved hash prediction.'}


@lru_cache(maxsize=1)
def resident_model():
    return ResidentModel()


class Workspace:
    def __init__(self,hasher,step):
        from .prime_structure import unit_coordinates
        self.step_coordinates=unit_coordinates(step)
        self.model=resident_model();self.hasher=hasher;self.step=step
        self.header_column=self.model.header_frame.column()
        self.word_column=self.model.word_frame.column()
        self.label_columns=[self.model.label_frame.column() for _ in range(4)]
        labels=[]
        for a,b in self.model.field:
            self.label_columns[0].load(a);self.label_columns[1].load(b)
            self.model.label_frame.program([
                ('mulc',2,1,0,19),('add',3,0,2),('addc',3,3,0,-1)],self.label_columns)
            labels.append(self.label_columns[3].value())
        self.residue_rows=array('H',(labels[(phase+k*step)%360] for phase in range(360) for k in range(360)))
        self._offsets=None
        self.header_rods=bytearray(85)  # Twenty densely packed 34-bit rod readings.
        self.core_readings=array('H',[0])*100  # Twenty words on five core square rods.
        self.jobs=0;self.tip_changes=0;self.previous_hash=None;self.generation=None

    def bind(self,work):
        if len(work.header)!=80:raise ValueError('Expected an 80-byte header')
        previous=work.header[4:36]
        if self.previous_hash is not None and previous!=self.previous_hash:self.tip_changes+=1
        self.previous_hash=previous;self.generation=work.generation;self.jobs+=1
        self.header_column.load(int.from_bytes(work.header,'big'))
        if self.header_column.value()!=int.from_bytes(work.header,'big'):
            raise ArithmeticError('Header abacus round-trip failed')
        packed=0
        for i,value in enumerate(struct.unpack('>20I',work.header)):
            packed|=self.model.pack_word(value)<<(34*i)
            self.word_column.load(value)
            for j,r in enumerate(self.word_column.residues[:5]):
                self.core_readings[5*i+j]=r
        self.header_rods[:]=packed.to_bytes(85,'little')

    def residues(self,phase,step):
        if step!=self.step:raise ValueError('Workspace step mismatch')
        return memoryview(self.residue_rows)[phase*360:(phase+1)*360]

    @property
    def offsets(self):
        if self._offsets is None: self._offsets=array('I',[0])*144000
        return self._offsets

    def description(self):
        return {**self.model.description(),'resident':True,'jobs_bound':self.jobs,
                'chain_tip_changes':self.tip_changes,'generation':self.generation,
                'previous_block_hash':self.previous_hash[::-1].hex() if self.previous_hash else None,
                'workspace_payload_bytes':(0 if self._offsets is None else len(self._offsets)*4)+len(self.residue_rows)*2+85+200,
                'offset_table_allocated':self._offsets is not None,
                'precision':self.model.shared_frame.description(),
                'shared_header_column_bytes':len(self.header_column.residues)*4,
                'board_labels_evaluated_on_rods':True,
                'native_projection':self.hasher.fill_offsets is not None}
