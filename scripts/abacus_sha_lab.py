#!/usr/bin/env python3
"""Offline, reproducible abacus/SHA laboratory. Never controls the miner.

Full SHA-256 is independently checked against hashlib and the Bitcoin genesis
header. Smaller words/round counts are explicitly toy compression functions.
"""
import hashlib
import json
import math
from pathlib import Path
import struct
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from btcminer.pqmath import RodAbacus
from btcminer.protocol import target_from_bits
from abacus_search_experiment import q_to_k, recover_from_k
from btcminer.thesis2 import qualifying_primes

# FIPS 180-4 constants; do not import the miner's hash implementation.
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


def sha(data, trace=False):
    padded = data + b'\x80'
    padded += b'\0' * ((56-len(padded)) % 64) + struct.pack('>Q',len(data)*8)
    state, blocks = IV[:], []
    for i in range(0,len(padded),64):
        state, block = compress(list(struct.unpack('>16I',padded[i:i+64])),state,trace=trace)
        block.update(index=i//64,bytes_hex=padded[i:i+64].hex())
        blocks.append(block)
    return struct.pack('>8I',*state), blocks


def double_sha(data, trace=False):
    inner, first = sha(data,trace)
    outer, second = sha(inner,trace)
    return outer, {'inner_digest':inner.hex(),'first_sha':first,'second_sha':second}


def primitive_checks():
    counts = {'rotation':0,'addition_and_xor':0,'choice_majority':0}
    for w in (4,8):
        B = 1 << w
        for x in range(B):
            for n in range(w):
                assert rotr(x,n,w) % (B-1) == (x*pow(pow(2,n,B-1),-1,B-1)) % (B-1)
                counts['rotation'] += 1
            for y in range(B):
                carry, z = divmod(x+y,B)
                assert x ^ y == x+y-2*(x&y)
                for rod in (3,5,7):
                    assert z % rod == ((x%rod)+(y%rod)-carry*(B%rod)) % rod
                counts['addition_and_xor'] += 1
    for x in range(16):
        for y in range(16):
            for z in range(16):
                ch = sum((((y if (x>>i)&1 else z)>>i)&1)<<i for i in range(4))
                maj = sum((int(((x>>i)&1)+((y>>i)&1)+((z>>i)&1)>=2))<<i for i in range(4))
                assert ch == ((x&y)^((~x&15)&z))
                assert maj == ((x&y)^(x&z)^(y&z))
                counts['choice_majority'] += 1
    return counts


def capacity_study():
    rods, product, candidate, rows = [],1,2,[]
    for bits in (32,256,2048,8192):
        started=time.perf_counter()
        while product.bit_length() <= bits:
            if all(candidate % d for d in range(2,math.isqrt(candidate)+1)):
                rods.append(candidate);product *= candidate
            candidate += 1
        board=RodAbacus(tuple(rods))
        x=(1<<bits)-159
        assert board.reconstruct(board.reading(x)) == x
        rows.append({'input_bits':bits,'rods':len(rods),'capacity_bits':product.bit_length(),
                     'roundtrip_seconds':time.perf_counter()-started})
    return rows


def replay_on_rods(trace):
    """Recompute every traced compression using exact rod addition/rotation.

    Conversion costs are deliberately retained: this is an equivalence model,
    not an optimized implementation or a shortcut claim.
    """
    board=RodAbacus((65536,65537,7));B=1<<32;mask=B-1
    counts={'rod_additions':0,'mersenne_rotations':0,'bitwise_operations':0}
    def add(*values):
        raw=board.reconstruct(tuple(sum(x%r for x in values)%r for r in board.rods))
        carry=raw//B
        result=board.reconstruct(tuple((sum(x%r for x in values)-carry*(B%r))%r for r in board.rods))
        counts['rod_additions']+=1
        return result
    def rotate(x,n):
        value=((x%mask)*pow(pow(2,n,mask),-1,mask))%mask
        counts['mersenne_rotations']+=1
        return mask if x==mask else value
    def xor(*values):
        counts['bitwise_operations']+=1
        return sum((sum((v>>i)&1 for v in values)%2)<<i for i in range(32))
    def AND(a,b):
        counts['bitwise_operations']+=1
        return sum((((a>>i)&1)*((b>>i)&1))<<i for i in range(32))
    def NOT(a):return mask-a
    for block in trace['first_sha']+trace['second_sha']:
        W=block['schedule'][:16]
        for t in range(16,64):
            a,b=W[t-15],W[t-2]
            W.append(add(W[t-16],xor(rotate(a,7),rotate(a,18),a//8),
                         W[t-7],xor(rotate(b,17),rotate(b,19),b//1024)))
        assert W==block['schedule']
        state=block['initial'][:]
        for t,row in enumerate(block['rounds']):
            a,b,c,d,e,f,g,h=state
            S0=xor(rotate(a,2),rotate(a,13),rotate(a,22))
            S1=xor(rotate(e,6),rotate(e,11),rotate(e,25))
            ch=xor(AND(e,f),AND(NOT(e),g))
            maj=xor(AND(a,b),AND(a,c),AND(b,c))
            T1=add(h,S1,ch,K[t],W[t]);T2=add(S0,maj)
            for name,value in [('Sigma0',S0),('Sigma1',S1),('Ch',ch),('Maj',maj),('T1',T1),('T2',T2)]:
                assert value==row[name]
            state=[add(T1,T2),a,b,c,add(d,T1),e,f,g]
            assert state==list(row['after'].values())
        assert [add(a,b) for a,b in zip(state,block['initial'])]==block['output']
    return counts


def run():
    out=ROOT/'validation'/'abacus-sha-lab';out.mkdir(parents=True,exist_ok=True)
    checked=0
    for n in (0,1,3,55,56,63,64,65,80,119,120,128,255):
        data=bytes((i*17+3)%256 for i in range(n))
        assert sha(data)[0] == hashlib.sha256(data).digest()
        assert double_sha(data)[0] == hashlib.sha256(hashlib.sha256(data).digest()).digest()
        checked+=1
    genesis=(struct.pack('<I',1)+bytes(32)+bytes.fromhex('4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b')[::-1]
             +struct.pack('<III',1231006505,0x1d00ffff,2083236893))
    assert double_sha(genesis)[0][::-1].hex() == '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f'
    previous=hashlib.sha256(b'abacus-lab-parent').digest()
    merkle=hashlib.sha256(b'abacus-lab-merkle-placeholder').digest()
    ladder=[];example=None
    for bits in (0x207fffff,0x2000ffff,0x1f00ffff):
        prefix=struct.pack('<I',0x20000000)+previous+merkle+struct.pack('<II',1700000000,bits)
        target=target_from_bits(bits);hits=[]
        for nonce in range(65536):
            header=prefix+struct.pack('<I',nonce)
            digest=hashlib.sha256(hashlib.sha256(header).digest()).digest()
            if int.from_bytes(digest,'little') <= target:
                hits.append(nonce)
        ladder.append({'bits':hex(bits),'target':str(target),'samples':65536,'hits':len(hits),
                       'first_nonce':hits[0] if hits else None,'expected_trials_uniform_model':2**256/(target+1)})
        if bits==0x2000ffff:
            example=prefix+struct.pack('<I',hits[0] if hits else 0)
    digest,trace=double_sha(example,True)
    assert digest==hashlib.sha256(hashlib.sha256(example).digest()).digest()
    # The third rod preserves the unreduced sums as well as 32-bit words.
    board=RodAbacus((65536,65537,7));variables=0
    def annotate(value):
        nonlocal variables
        if isinstance(value,dict):return {k:annotate(v) for k,v in value.items()}
        if isinstance(value,list):return [annotate(v) for v in value]
        if isinstance(value,int):
            assert board.reconstruct(board.reading(value))==value
            variables+=1
        return value
    annotate(trace)  # Also checks intermediate sums, all of which fit this board.
    # Every word in each traced round gets both binary and circular projections.
    for block in trace['first_sha']+trace['second_sha']:
        for row in block['rounds']:
            row['abacus']={k:{'binary':format(v,'032b'),'rods':board.reading(v),
                              'mod360':v%360,'mod144000':v%144000,
                              'mersenne':v%0xffffffff,'all_ones':v==0xffffffff}
                           for k,v in row['after'].items()}
    # Fixed toy definition: truncate IV/K/input words to w bits; rotation
    # offsets reduced modulo w; logical shifts keep FIPS distances. No claim
    # that truncation commutes with full SHA or preserves its security.
    toy=[]
    words=trace['first_sha'][1]['schedule'][:16]
    for w in (4,8,16,32):
        initial=[v&((1<<w)-1) for v in trace['first_sha'][1]['initial']]
        for rounds in (1,2,4,8,16,32,64):
            base,_=compress(words,initial,w,rounds)
            changed=[]
            for bit in range(w):
                altered=words[:];altered[3]^=1<<bit
                other,_=compress(altered,initial,w,rounds)
                changed.append(sum(bin(x^y).count('1') for x,y in zip(base,other)))
            toy.append({'word_bits':w,'rounds':rounds,'flipped_input_word':3,
                        'mean_changed_state_bits':sum(changed)/len(changed),'state_bits':8*w})
    fields=[]
    for name,start,length in [('version',0,4),('previous_hash',4,32),('merkle_root',36,32),
                              ('time',68,4),('nBits',72,4),('nonce',76,4)]:
        distances=[]
        for bit in range(length*8):
            altered=bytearray(example);altered[start+bit//8]^=1<<(bit%8)
            h=hashlib.sha256(hashlib.sha256(altered).digest()).digest()
            distances.append(sum(bin(a^b).count('1') for a,b in zip(h,digest)))
        fields.append({'name':name,'byte_offset':start,'bytes':length,
                       'bits_tested':len(distances),'mean_changed_hash_bits':sum(distances)/len(distances),
                       'minimum':min(distances),'maximum':max(distances)})
    clock=(2,3,5,*qualifying_primes())
    mapping=q_to_k(3439,clock);assert mapping==(19,181,180)
    assert recover_from_k(3439,180)==(19,181)
    report={'schema':1,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'input_source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
              for name in ('btcminer/pqmath.py','btcminer/protocol.py','btcminer/thesis2.py',
                           'scripts/abacus_search_experiment.py')},
            'checks':{'hashlib_lengths':checked,'genesis':True,'traced_integer_roundtrips':variables,
                      'primitives':primitive_checks(),'abacus_replay':replay_on_rods(trace)},'capacity':capacity_study(),
            'large_precision_estimate':{'decimal_digits':300000000,
              'approx_binary_bits':300000000*math.log2(10),'approx_packed_bytes':300000000*math.log2(10)/8,
              'status':'Storage estimate only; no huge prime generated, operated on, or certified.'},
            'example':{'header':example.hex(),'display_hash':digest[::-1].hex(),
                       'scope':'Synthetic header only, not a valid block or a Testnet submission.'},
            'trace':trace,'rod_moduli':board.rods,'ladder':ladder,'toy_diffusion':toy,
            'header_field_bit_flips':fields,
            'pq_example':{'n':3439,'p':19,'q':181,'k':180,'phi':3240,'G':'units modulo 3439',
                          'G_cardinality':3240,'G_decomposition':'C18 x C180',
                          'ellipse_a':'181/2','ellipse_c':'19/2','ellipse_b':90},
            'status':'Research instrument with numerical checks; no new formal proof or mining speedup.'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('checks','capacity','ladder','status')},indent=2))
    return report


if __name__=='__main__':run()
