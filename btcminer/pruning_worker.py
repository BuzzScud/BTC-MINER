"""Isolated, reusable SMT worker. Unknown work is always retained."""
import hashlib
import json
import sys
import time
from .constraintmodel import bitcoin_model, z3
from .adaptive import retain_candidates

MODEL = 'bitcoin-sha256d-v1'


def request_key(header, target, nonces):
    return hashlib.sha256(json.dumps([header, str(target), nonces],separators=(',',':')).encode()).hexdigest()


def evaluate(request):
    header=bytes.fromhex(request['header']);target=int(request['target'])
    if sum(key in request for key in ('nonces','nonce_codes','nonce_geometry')) != 1:
        raise ValueError('Ambiguous or missing nonce encoding')
    if 'nonce_geometry' in request:
        from .geometry_codec import decode_points
        nonces=decode_points(request['nonce_geometry'])
    elif 'nonce_codes' in request:
        from .scaled_abacus import q_codec
        encoded=request['nonce_codes']
        if type(encoded['count']) is not int or not 0<=encoded['count']<=64:
            raise ValueError('Invalid encoded candidate count')
        nonces=q_codec(encoded['M']).unpack(bytes.fromhex(encoded['data']),encoded['count'])
    else:nonces=request['nonces']
    if len(header)!=80 or not 0<=target<1<<256 or len(nonces)>64 or any(type(n)!=int or not 0<=n<1<<32 for n in nonces):
        raise ValueError('Invalid pruning request')
    if request.get('model')!=MODEL:raise ValueError('Hash model mismatch')
    key=request_key(request['header'],target,nonces)
    from .geometry_predictive import capability
    result={'model':MODEL,'key':key,'keep':list(nonces),'excluded':0,'unknown':True,'reason':'solver unavailable'}
    if request.get('geometry_offer') is True:result['geometry_capability']=capability()
    if z3 is None:return result
    budget=max(1,min(2000,int(request.get('budget_ms',200))))/1000
    started=time.monotonic();deadline=started+budget
    # The exact prefix condition is necessary for the complete target comparison.
    # Fixed-value propagation also supports very small adaptive buckets.
    solver=z3.Then('simplify','propagate-values','solve-eqs','simplify','smt').solver()
    solver.set(max_memory=256)
    nonce,value,carries=bitcoin_model(header,solver)
    solver.add(z3.ULE(z3.Extract(255,192,value),z3.BitVecVal(target>>192,64)))
    adaptive=retain_candidates(solver,nonce,nonces,deadline,bucket_size=8)
    result.update(adaptive)
    result.update(
        reason='bounded full-SHA constraints' if not adaptive['unknown'] else 'unresolved candidates retained',
        carry_constraints=carries,seconds=time.monotonic()-started,
        concrete_hashes=0)
    return result


def main():
    for line in sys.stdin:
        try:
            request=json.loads(line);result=evaluate(request)
        except Exception as e:
            result={'error':type(e).__name__+': '+str(e)}
        print(json.dumps(result),flush=True)


if __name__=='__main__':main()
