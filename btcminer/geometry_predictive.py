"""NG2 geometry grammars. Exact integers; canonical charts; bounded IPC decoding.

See docs/GEOMETRY-CODEC.txt and GEO-08..GEO-13 in the contract. Anchor offsets
are circle coordinates, not a proof concerning sphere packing or SHA256d.
"""
import hashlib
from math import isqrt
import struct
from .geometry_codec import (integer, pack_fields, Bits, frames, LIMIT, MAX_COUNT)

NAMES = ('rod-delta','hex-shell','root-offset','predictive','adaptive-rods')
RULES = (
    'shortest-arc;[-floor(m/2),ceil(m/2));negative-even-tie;zigzag-gamma',
    'E-chart;N(k)=1+3k(k+1);clockwise-from(k,0);common-shell-or-per-point',
    'anchors=0,1,-1;nearest-circle-distance;lowest-index-tie;zigzag-gamma',
    'per-point-raw-or-shortest-arc;gamma-bit-cost;raw-on-tie',
    'minimal-prefix-per-offset;count-stream=packed3|RLE|delta-RLE;lowest-mode-on-tie',
)


def identity(mode):
    integer(mode,'NG2 mode',0,len(NAMES)-1)
    return hashlib.sha256(b'btc-geometry/NG2;'+NAMES[mode].encode()+b';'+RULES[mode].encode()+frames()[-1].fingerprint).digest()


def capability():
    registry=hashlib.sha256(b'btc-geometry/NG2-registry;'+bytes([len(NAMES)])
                            +b''.join(identity(i) for i in range(len(NAMES)))).hexdigest()
    return {'version':'NG2','registry':registry}


def zigzag(n):
    return 2*n if n>=0 else -2*n-1


def unzigzag(n):
    return n//2 if n%2==0 else -(n//2)-1


def gamma(n):
    integer(n,'gamma natural')
    k=(n+1).bit_length()-1
    return [(0,k),(1,1),(n+1-(1<<k),k)]


def read_gamma(bits, maximum):
    k=0
    while bits.take(1)==0:
        k+=1
        if k>(maximum+1).bit_length()-1:
            raise ValueError('Gamma field exceeds bound')
    value=(1<<k)+bits.take(k)-1
    integer(value,'gamma value',0,maximum)
    return value


def shortest_arc(previous, current, modulus):
    integer(modulus,'modulus',2)
    integer(previous,'previous residue',0,modulus-1)
    integer(current,'current residue',0,modulus-1)
    return (current-previous+modulus//2)%modulus-modulus//2


def root_reference(residue, modulus):
    integer(residue,'residue',0,modulus-1)
    choices=[(i,shortest_arc(root,residue,modulus)) for i,root in enumerate((0,1,modulus-1))]
    return min(choices,key=lambda item:(abs(item[1]),item[0]))


def shell_address(value):
    integer(value,'hex ordinal')
    if value==0:return 0,0
    k=(3+isqrt(12*value-3))//6
    return k,value-(1+3*k*(k-1))


def shell_value(k, offset):
    integer(k,'shell radius');integer(offset,'shell offset',0,0 if k==0 else 6*k-1)
    return 0 if k==0 else 1+3*k*(k-1)+offset


def shell_point(k, offset):
    shell_value(k,offset)
    if k==0:return 0,0
    side,t=divmod(offset,k)
    starts=((k,0),(k,k),(0,k),(-k,0),(-k,-k),(0,-k))
    steps=((0,1),(-1,0),(-1,-1),(0,-1),(1,0),(1,1))
    a,b=starts[side];da,db=steps[side]
    return a+t*da,b+t*db


def point_address(a,b):
    if type(a) is not int or type(b) is not int:raise ValueError('Exact E coordinates required')
    k=max(abs(a),abs(b),abs(a-b))
    if k==0:return 0,0
    if a==k and 0<=b<k:side,t=0,b
    elif b==k and 0<a<=k:side,t=1,k-a
    elif b-a==k and 0<b<=k:side,t=2,-a
    elif a==-k and -k<b<=0:side,t=3,-b
    elif b==-k and -k<=a<0:side,t=4,a+k
    else:side,t=5,a
    return k,side*k+t


def encode_counts(counts):
    if not counts:raise ValueError('Empty rod-count stream')
    for n in counts:integer(n,'used rods',1,len(frames()))
    runs=[]
    for n in counts:
        if runs and runs[-1][0]==n:runs[-1]=(n,runs[-1][1]+1)
        else:runs.append((n,1))
    candidates=[[(0,2)]+[(n-1,3) for n in counts]]
    rle=[(1,2)];delta=[(2,2)];previous=1
    for n,length in runs:
        rle += [(n-1,3)]+gamma(length-1)
        delta += gamma(zigzag(n-previous))+gamma(length-1);previous=n
    candidates += [rle,delta]
    # Compare actual side-stream bytes, deterministic lower-mode tie.
    return min((pack_fields(fields) for fields in candidates),key=len)


def decode_counts(data, count):
    integer(count,'point count',1,MAX_COUNT)
    bits=Bits(data);mode=bits.take(2);out=[];previous=1
    if mode==0:out=[bits.take(3)+1 for _ in range(count)]
    elif mode in (1,2):
        while len(out)<count:
            n=bits.take(3)+1 if mode==1 else previous+unzigzag(read_gamma(bits,2*len(frames())))
            integer(n,'used rods',1,len(frames()))
            length=read_gamma(bits,count-1)+1
            if len(out)+length>count:raise ValueError('Rod-count run exceeds point count')
            out.extend([n]*length);previous=n
    else:raise ValueError('Unknown rod-count stream')
    for n in out:integer(n,'used rods',1,len(frames()))
    bits.finish()
    if encode_counts(out)!=data:raise ValueError('Noncanonical rod-count stream')
    return out


def setup(values):
    origin=min(values);bound=max(values)-origin
    frame=next(f for f in frames() if f.capacity>bound)
    return origin,bound,frame,[v-origin for v in values]


def encode_body(values, mode):
    integer(mode,'NG2 mode',0,len(NAMES)-1)
    if mode==1:
        addresses=[shell_address(v) for v in values]
        common=all(k==addresses[0][0] for k,_ in addresses)
        fields=[(int(common),1)]
        if common:fields+=gamma(addresses[0][0])
        for k,offset in addresses:
            if not common:fields+=gamma(k)
            fields.append((offset,(6*k-1).bit_length() if k else 0))
        return pack_fields(fields)
    origin,bound,frame,offsets=setup(values)
    rows=[frame.tree.encode(v) for v in offsets]
    if mode==4:
        counts=[next(i+1 for i,f in enumerate(frames()) if f.capacity>v) for v in offsets]
        side=encode_counts(counts);fields=[]
        for offset,n in zip(offsets,counts):
            f=frames()[n-1];fields.extend(zip(f.tree.encode(offset),f.widths))
        return struct.pack('>II',origin,bound)+bytes([len(side)])+side+pack_fields(fields)
    header=bytes([len(frame.moduli)])+struct.pack('>II',origin,bound)
    fields=[];previous=None
    for row in rows:
        raw=list(zip(row,frame.widths))
        if mode==2:
            for residue,m in zip(row,frame.moduli):
                anchor,delta=root_reference(residue,m)
                fields += [(anchor,2)]+gamma(zigzag(delta))
        elif previous is None:
            fields+=raw
        else:
            delta=[]
            for a,b,m in zip(previous,row,frame.moduli):
                delta+=gamma(zigzag(shortest_arc(a,b,m)))
            if mode==0:fields+=delta
            else:
                use_delta=sum(w for _,w in delta)<sum(frame.widths)
                fields += [(int(use_delta),1)]+(delta if use_delta else raw)
        previous=row
    return header+pack_fields(fields)


def read_row(bits, frame):
    row=tuple(bits.take(w) for w in frame.widths)
    if any(r>=m for r,m in zip(row,frame.moduli)):raise ValueError('Noncanonical residue')
    return row


def read_delta(bits, modulus):
    delta=unzigzag(read_gamma(bits,modulus))
    if not -(modulus//2) <= delta < (modulus+1)//2:raise ValueError('Arc outside range')
    return delta


def decode_body(body, count, mode):
    integer(mode,'NG2 mode',0,len(NAMES)-1);integer(count,'point count',1,MAX_COUNT)
    if mode==1:
        bits=Bits(body);common=bits.take(1);max_shell=shell_address(LIMIT-1)[0]
        radius=read_gamma(bits,max_shell) if common else None;values=[]
        for _ in range(count):
            k=radius if common else read_gamma(bits,max_shell)
            offset=bits.take((6*k-1).bit_length() if k else 0)
            value=shell_value(k,offset);integer(value,'decoded nonce',0,LIMIT-1);values.append(value)
        bits.finish()
    else:
        if len(body)<9:raise ValueError('Truncated geometry bounds')
        if mode==4:
            origin,bound=struct.unpack('>II',body[:8]);size=body[8]
            if size==0 or 9+size>len(body):raise ValueError('Invalid rod-count side-stream size')
            counts=decode_counts(body[9:9+size],count);bits=Bits(body[9+size:]);frame=None
        else:
            prefix=body[0];integer(prefix,'rod prefix',1,len(frames()));frame=frames()[prefix-1]
            origin,bound=struct.unpack('>II',body[1:9]);bits=Bits(body[9:])
            if bound>=frame.capacity:raise ValueError('Insufficient CRT capacity')
        if origin+bound>=LIMIT:raise ValueError('Bounds exceed nonce range')
        values=[];previous=None
        for i in range(count):
            if mode==4:
                f=frames()[counts[i]-1];row=read_row(bits,f)
            else:
                f=frame
                if mode==2:
                    residues=[]
                    for m in f.moduli:
                        anchor=bits.take(2)
                        if anchor>2:raise ValueError('Invalid root anchor')
                        delta=read_delta(bits,m);root=(0,1,m-1)[anchor]
                        residue=(root+delta)%m
                        if root_reference(residue,m)!=(anchor,delta):raise ValueError('Noncanonical root reference')
                        residues.append(residue)
                    row=tuple(residues)
                elif previous is None:row=read_row(bits,f)
                else:
                    predicted=True if mode==0 else bits.take(1)==1
                    row=tuple((a+read_delta(bits,m))%m for a,m in zip(previous,f.moduli)) if predicted else read_row(bits,f)
            value=f.tree.decode(row)
            if value>bound:raise ValueError('Decoded point exceeds bound')
            values.append(origin+value);previous=row
        bits.finish()
    # Re-encoding enforces minimal prefixes, exact min/max bounds, deterministic
    # root ties, count-stream choice, predictive tags and common-shell choice.
    if encode_body(values,mode)!=body:raise ValueError('Noncanonical geometry body')
    return values


def metadata(values,mode):
    result={'symbolic_form':NAMES[mode],'frame_fingerprint':identity(mode).hex(),
            'partition_route':('hex/E/clockwise' if mode==1 else 'CRT/ordered-prefix'),
            'certificate_chain_ids':{'rod-delta':['GEO-01','GEO-08'], 'hex-shell':['GEO-09'],
                                     'root-offset':['GEO-01','GEO-10'], 'predictive':['GEO-01','GEO-08','GEO-11'],
                                     'adaptive-rods':['GEO-01','GEO-03','GEO-12']}[NAMES[mode]],
            'certificate_scope':'Contract arguments and executable gates; not a cryptographic or formal-proof certificate'}
    if mode==1:
        result['shells']=[{'radius':k,'offset':j,'E_point':shell_point(k,j)} for k,j in map(shell_address,values)]
    else:
        origin,bound,frame,offsets=setup(values);result.update(origin=origin,bound=bound,moduli=list(frame.moduli))
        if mode==4:
            counts=[next(i+1 for i,f in enumerate(frames()) if f.capacity>v) for v in offsets]
            result.update(used_counts=counts,count_stream_mode=('packed3','RLE','delta-RLE')[encode_counts(counts)[0]&3])
    return result
