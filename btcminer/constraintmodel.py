"""Shared concrete and symbolic SHA arithmetic for lossless candidate filtering."""
import struct
try:
    import z3
except ImportError:
    z3 = None

K = [int(x, 16) for x in '''428a2f98 71374491 b5c0fbcf e9b5dba5
3956c25b 59f111f1 923f82a4 ab1c5ed5 d807aa98 12835b01 243185be 550c7dc3
72be5d74 80deb1fe 9bdc06a7 c19bf174 e49b69c1 efbe4786 0fc19dc6 240ca1cc
2de92c6f 4a7484aa 5cb0a9dc 76f988da 983e5152 a831c66d b00327c8 bf597fc7
c6e00bf3 d5a79147 06ca6351 14292967 27b70a85 2e1b2138 4d2c6dfc 53380d13
650a7354 766a0abb 81c2c92e 92722c85 a2bfe8a1 a81a664b c24b8b70 c76c51a3
d192e819 d6990624 f40e3585 106aa070 19a4c116 1e376c08 2748774c 34b0bcb5
391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3 748f82ee 78a5636f 84c87814 8cc70208
90befffa a4506ceb bef9a3f7 c67178f2'''.split()]

IV = [int(x, 16) for x in '6a09e667 bb67ae85 3c6ef372 a54ff53a 510e527f 9b05688c 1f83d9ab 5be0cd19'.split()]

def rotr(x, n, w=32):
    n %= w
    return ((x >> n) | (x << ((w - n) % w))) & ((1 << w) - 1)

def carry_chain(operands,w):
    carries=[0]
    for bit in range(w):
        carries.append((sum((x>>bit)&1 for x in operands)+carries[-1])//2)
    assert carries[-1] == sum(operands)>>w
    return carries

def compress(words, initial, w=32, rounds=64, trace=False):
    """Exact SHA compression at w=32, rounds=64; otherwise a defined toy."""
    mask = (1 << w) - 1
    sigma0 = lambda x: rotr(x, 7, w) ^ rotr(x, 18, w) ^ (x >> 3)
    sigma1 = lambda x: rotr(x, 17, w) ^ rotr(x, 19, w) ^ (x >> 10)
    schedule = [v & mask for v in words]
    expansion = []
    for t in range(16, 64):
        s0, s1 = sigma0(schedule[t-15]), sigma1(schedule[t-2])
        raw = schedule[t-16] + s0 + schedule[t-7] + s1
        schedule.append(raw & mask)
        if trace:
            expansion.append({'t': t, 'sigma0': s0, 'sigma1': s1,
                              'sum': raw, 'carry': raw >> w, 'W': raw & mask,
                              'bit_carries':carry_chain([schedule[t-16],s0,schedule[t-7],s1],w)})
    state = [x & mask for x in initial]
    rows = []
    for t in range(rounds):
        a,b,c,d,e,f,g,h = state
        S0 = rotr(a,2,w) ^ rotr(a,13,w) ^ rotr(a,22,w)
        S1 = rotr(e,6,w) ^ rotr(e,11,w) ^ rotr(e,25,w)
        ch = (e & f) ^ ((~e & mask) & g)
        maj = (a & b) ^ (a & c) ^ (b & c)
        raw1 = h + S1 + ch + (K[t] & mask) + schedule[t]
        raw2 = S0 + maj
        T1, T2 = raw1 & mask, raw2 & mask
        state = [(T1+T2)&mask,a,b,c,(d+T1)&mask,e,f,g]
        if trace:
            rows.append({'round':t,'before':dict(zip('abcdefgh',(a,b,c,d,e,f,g,h))),
                         'W':schedule[t],'K':K[t]&mask,'Sigma0':S0,'Sigma1':S1,
                         'Ch':ch,'Maj':maj,'T1':T1,'T2':T2,
                         'T1_unreduced':raw1,'T2_unreduced':raw2,
                         'Sigma0_rotations':[rotr(a,n,w) for n in (2,13,22)],
                         'Sigma1_rotations':[rotr(e,n,w) for n in (6,11,25)],
                         'Ch_terms':[e&f,(~e&mask)&g],
                         'Maj_terms':[a&b,a&c,b&c],
                         'carries':{'T1':raw1>>w,'T2':raw2>>w,'a':(T1+T2)>>w,'e':(d+T1)>>w},
                         'bit_carries':{'T1':carry_chain([h,S1,ch,K[t]&mask,schedule[t]],w),
                                        'T2':carry_chain([S0,maj],w),'a':carry_chain([T1,T2],w),
                                        'e':carry_chain([d,T1],w)},
                         'after':dict(zip('abcdefgh',state))})
    output = [(x+y)&mask for x,y in zip(initial,state)]
    return output, {'initial':initial,'schedule':schedule,'expansion':expansion,
                    'rounds':rows,'output':output,
                    'feedforward_carries':[(x+y)>>w for x,y in zip(initial,state)]}

class Arithmetic:
    def __init__(self,w,solver=None):
        self.w=w;self.mask=(1<<w)-1;self.solver=solver;self.count=0
    def constant(self,x):
        return (x&self.mask) if self.solver is None else z3.BitVecVal(x,self.w)
    def add(self,*values):
        if self.solver is None:return sum(values)&self.mask
        total=z3.simplify(sum(z3.ZeroExt(3,x) for x in values))
        if z3.is_bv_value(total):return self.constant(total.as_long())
        name=str(self.count);self.count+=1
        result=z3.BitVec('sum_'+name,self.w)
        carry=z3.BitVec('carry_'+name,3)
        # Carry and result together are the exact unreduced addition.
        self.solver.add(z3.Concat(carry,result)==total)
        return result
    def rotate(self,x,n):
        return rotr(x,n,self.w) if self.solver is None else z3.RotateRight(x,n%self.w)
    def shift(self,x,n):
        return x>>n if self.solver is None else z3.LShR(x,n)

def execute(words,initial,rounds,ops):
    W=words[:];R=ops.rotate;S=ops.shift;A=ops.add
    for t in range(16,rounds):
        x,y=W[t-15],W[t-2]
        W.append(A(W[t-16],R(x,7)^R(x,18)^S(x,3),W[t-7],R(y,17)^R(y,19)^S(y,10)))
    state=initial[:]
    for t in range(rounds):
        a,b,c,d,e,f,g,h=state
        s0=R(a,2)^R(a,13)^R(a,22);s1=R(e,6)^R(e,11)^R(e,25)
        ch=(e&f)^((~e&ops.mask)&g);maj=(a&b)^(a&c)^(b&c)
        t1=A(h,s1,ch,ops.constant(K[t]),W[t]);t2=A(s0,maj)
        state=[A(t1,t2),a,b,c,A(d,t1),e,f,g]
    return [A(a,b) for a,b in zip(initial,state)]

def swap32(x):
    return z3.Concat(*[z3.Extract(i+7,i,x) for i in (0,8,16,24)])

def bitcoin_model(header, solver):
    """Exact Bitcoin SHA256d: constant first block, symbolic second and outer blocks."""
    if len(header) != 80:
        raise ValueError("Expected an 80-byte Bitcoin header")
    mid = compress(list(struct.unpack(">16I", header[:64])), IV)[0]
    tail = header[64:76] + bytes(4) + b"\x80" + bytes(39) + struct.pack(">Q", 640)
    ops = Arithmetic(32, solver)
    nonce = z3.BitVec("nonce", 32)
    words = [ops.constant(v) for v in struct.unpack(">16I", tail)]
    words[3] = swap32(nonce)
    inner = execute(words, [ops.constant(v) for v in mid], 64, ops)
    outer = execute(inner + [ops.constant(0x80000000)] + [ops.constant(0)]*6 + [ops.constant(256)],
                    [ops.constant(v) for v in IV], 64, ops)
    value = z3.Concat(*[swap32(v) for v in reversed(outer)])
    return nonce, value, ops.count
