"""Research progression and scoped evidence discovery on the shared model.

MUST retain every claim domain and outstanding obligation; source declaration
inventory alone is not a proof. SHALL obtain accepted repair roots only through
the current source/object/axiom gate, and treat the external provider coverage
ledger as explicit per-formula research context. MAY discover additional Lean
sources without promoting their status. No recurrence or CRT theorem authorizes
SHA256d exclusions. See ../MASTER_PLAN.md PROOF-01, PUBLISH-01 and LIVE-01; the
progression functions below are explicit research commands, not live job gates.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import time
from . import ROOT
from .shared_abacus import Calculation, shared_pool


def claims():
    return json.loads((ROOT/'research/claims.json').read_text())


def inventory():
    """Declaration inventory, not a semantic verification of arbitrary prose."""
    roots = [ROOT/'reference', ROOT/'research',
             ROOT/'validation/miner-proof-repair-20261007/sources',
             ROOT/'validation/miner-math-library-20261010/snapshot/sources',
             ROOT.parent/'bitcoin-algorithm-observatory-2026-10-07/catalogue-study/proofs',
             ROOT/'validation/aristotle-shared-abacus-857374a3/sources',
             ROOT.parent/'Aristotle-9b854e2d-2026-09-29/source',
             ROOT.parent/'Aristotle-9b854e2d-2026-09-29/project-files',
             ROOT.parent/'Aristotle-9b854e2d-2026-09-29/history',
             ROOT/'validation/archive-audit/857374a3-5a8f-4b18-9f97-f889ef5399b8/sources',
             ROOT/'validation/archive-audit/5f501e9e-d021-4e48-b01a-f9facfee2057/sources',
             ROOT/'validation/archive-audit/refresh/5f501e9e-d021-4e48-b01a-f9facfee2057/sources',
             ROOT/'validation/archive-audit/live-source-overrides',
             ROOT/'validation/archive-audit/live-source-history',
             ROOT/'validation/archive-audit/final-snapshot/5f501e9e-d021-4e48-b01a-f9facfee2057/sources']
    rows=[]; seen=set(); registry=claims()['claims']
    for root in roots:
        if not root.exists(): continue
        for path in sorted(root.rglob('*.lean')):
            if '.lake' in path.parts or 'prior-runs' in path.parts or 'registry-history' in path.parts: continue
            data=path.read_bytes(); digest=hashlib.sha256(data).hexdigest()
            if digest in seen: continue
            seen.add(digest); source=data.decode()
            matches=list(re.finditer(r'^\s*(?:(?:private|public|protected|noncomputable)\s+)*(?:theorem|lemma|axiom)\s+([^\s(:{]+)',source,re.M))
            declarations=[]
            for match in matches:
                name=match.group(1);end=source.find(':=',match.end())
                statement=source[match.start():end if end!=-1 else match.end()].strip()
                bindings=[c['id'] for c in registry if any(t.split('.')[-1]==name for t in c['lean_theorems'])]
                declarations.append({'name':name,'statement':statement[:12000],
                                     'lexical_candidate_claim_ids':bindings,
                                     'status':'mapping_candidate' if bindings else 'unmapped_inventory',
                                     'mapping_scope':'Declaration suffix matches are navigation candidates, not qualified theorem or semantic proof bindings.'})
            try: display=str(path.relative_to(ROOT.parent))
            except ValueError: display=str(path)
            rows.append({'path':display,'sha256':digest,'declarations':declarations,
                         'proof_status':'inventory_only; see claim-specific validation',
                         'contains_sorry_token':bool(re.search(r'\bsorry\b',source))})
    # Acceptance is checked at request time, never inferred from a module name
    # or a historical success flag. Discovery remains useful if a gate is stale.
    from .proof_evidence import verify, EvidenceError
    try:
        evidence = verify(ROOT)
        accepted = {'status':'accepted_scoped_kernel_evidence',
                    'proof_manifest_sha256':evidence['manifest_sha256'],
                    'audited_roots':evidence['theorem_count'],
                    'named_theorems':evidence['required_named_theorems'], 'scope':evidence['scope']}
    except EvidenceError as error:
        accepted = {'status':'unaccepted_or_stale', 'error':str(error)}
    external_path = ROOT/'research/provider-coverage-ledger.json'
    external = json.loads(external_path.read_text()) if external_path.exists() else None
    from .math_catalogue import catalogue
    return {'scope':'Available local source snapshots, deduplicated by source hash; declaration discovery is not proof checking',
            'current_formula_catalogue':catalogue(),
            'accepted_repair_evidence':accepted,
            'external_provider_coverage_snapshot':external,
            'external_provider_scope':'Context snapshot only; provider labels and finite outputs do not establish implementation refinement',
            'modules':rows,'module_count':len(rows),'declaration_count':sum(len(r['declarations']) for r in rows),
            'unmapped_declarations':sum(d['status']=='unmapped_inventory' for r in rows for d in r['declarations'])}


def fib(n):
    # Independent positional fast doubling oracle, used after the rod calculation.
    if n==0:return 0,1
    a,b=fib(n//2);c=a*(2*b-a);d=a*a+b*b
    return (d,c+d) if n%2 else (c,d)


def audit_sha_carries(width=32, rounds=64, seed=109):
    """Check each traced addition as an integer claim on the resident abacus.

    This is an executable correspondence check, after computing the trace. It
    is not a pre-hash filter and its calculations must not count as saved work.
    """
    import random
    from .claim_calculus import ClaimCalculator
    from .constraintmodel import compress, IV
    if width not in (8,16,32,64) or not 1 <= rounds <= 64:
        raise ValueError('Use widths 8/16/32/64 and 1..64 rounds')
    rng=random.Random(seed); mask=(1<<width)-1
    words=[rng.getrandbits(width) for _ in range(16)]
    initial=[v&mask for v in IV]
    output,trace=compress(words,initial,width,rounds,True)
    calc=ClaimCalculator(slots=16,bits=width+4)
    checked_count=0
    def check(raw,value,carry):
        nonlocal checked_count
        result=calc.decide(('eq','sum',('add','result',('mul','carry',1<<width))),
                           {'sum':raw,'result':value,'carry':carry})
        if not result['truth']: raise ArithmeticError('SHA carry disagrees with shared integer model')
        checked_count+=1
    for row in trace['expansion']:check(row['sum'],row['W'],row['carry'])
    for row in trace['rounds']:
        check(row['T1_unreduced'],row['T1'],row['carries']['T1'])
        check(row['T2_unreduced'],row['T2'],row['carries']['T2'])
        check(row['T1']+row['T2'],row['after']['a'],row['carries']['a'])
        check(row['before']['d']+row['T1'],row['after']['e'],row['carries']['e'])
    final=trace['rounds'][-1]['after']
    for i,key in enumerate('abcdefgh'):
        check(initial[i]+final[key],output[i],trace['feedforward_carries'][i])
    return {'ok':True,'width':width,'rounds':rounds,'integer_claims_checked':checked_count,
            'capacity_bits':calc.calculation.frame.capacity.bit_length(),
            'scope':'Post-computation trace validation; zero pre-hash exclusions claimed'}


def study_level(bits):
    started=time.monotonic(); calc=Calculation(bits=64)
    a=(1 << bits)-19;b=(1 << max(4,bits//2))-11
    calc.load(0,a).load(1,b)
    rod_start=time.monotonic()
    calc.run([('mul',2,0,1),('add',3,2,0),('sub',2,3,1)])
    program_seconds=time.monotonic()-rod_start
    observed=calc.columns[2].value()
    formula_ok=observed==a*b+a-b
    ids=[id(c._data) for c in calc.columns];frame=calc.frame
    calc.clear();clear_ok=all(c.value()==0 for c in calc.columns)
    calc.load(0,-a).load(1,b).run([('add',2,0,1)])
    reuse_ok=frame is calc.frame and ids==[id(c._data) for c in calc.columns]
    signed_ok=calc.columns[2].value()==-a+b
    depth=bits; rod_start=time.monotonic()
    jump=calc.frame.jump((1,1),(0,1),depth,bound=1 << depth)
    jump_seconds=time.monotonic()-rod_start
    jump_value=jump.value();recurrence_ok=jump_value==fib(depth)[0]
    return {'ok':all((formula_ok,clear_ok,reuse_ok,signed_ok,recurrence_ok)),
            'input_bits':bits,'result_bits':abs(observed).bit_length(),
            'formula':'((a*b)+a)-b','signed_formula':'-a+b',
            'formula_matches_python':formula_ok,'signed_matches_python':signed_ok,
            'clear_reuses_columns':reuse_ok and clear_ok,'capacity_growths':calc.growths,
            'frame':calc.frame.description(),'recurrence':'Fibonacci (1,1); initial (0,1)',
            'depth':depth,'jump_matches_independent_fast_doubling':recurrence_ok,
            'jump_result_bits':jump_value.bit_length(),'program_seconds':program_seconds,
            'rod_jump_seconds':jump_seconds,'total_seconds':time.monotonic()-started,
            'result_sha256':hashlib.sha256(abs(observed).to_bytes((abs(observed).bit_length()+7)//8,'big')).hexdigest(),
            'bitcoin_exclusions':0}


def structure_study(depth=5):
    """Q coordinates and a recursive Descartes bend system on the same frames.

    Bend tuples do not encode sphere centers. Their counts are not counts of
    distinct geometric spheres and do not prove nonoverlap.
    """
    from math import gcd
    from .scaled_abacus import SCALES, q_codec
    calc=Calculation(slots=10,bits=128); q_rows=[]
    for scale in SCALES:
        codec=q_codec(scale);count=0;ok=True
        for value in codec.values:
            coordinates=codec.coordinates(value);p,q=coordinates['p'],coordinates['q']
            calc.load(0,p).load(1,q).run([('mul',2,0,1),('addc',3,0,0,-1),
                ('addc',4,1,0,-1),('mul',5,3,4)])
            product=calc.columns[2].value();phi=calc.columns[5].value()
            ok &= product==value and phi//gcd(p-1,q-1)==coordinates['k']
            count+=1
        q_rows.append({'M':scale,'checked_pairs':count,'ok':ok,
                       'gcd_backend':'exact positional gcd; gcd is not a rodwise ring operation'})
    frontier={(-1,2,2,3,3)};seen=set(frontier);levels=[];invariants=True
    for generation in range(1,depth+1):
        following=set();checks=0
        for bends in sorted(frontier):
            for mirror in range(5):
                for i,b in enumerate(bends):calc.load(i,b)
                program=[('const',5)]+[('add',5,5,i) for i in range(5)]
                program += [('mulc',6,mirror,0,-2),('add',mirror,5,6),('const',5),('const',7)]
                for i in range(5):program += [('add',5,5,i),('mul',6,i,i),('add',7,7,6)]
                program += [('mul',8,5,5),('mulc',9,7,0,3),('sub',9,8,9)]
                calc.run(program)
                child=tuple(calc.columns[i].value() for i in range(5))
                expected=list(bends);expected[mirror]=sum(bends)-2*bends[mirror]
                invariants &= child==tuple(expected) and calc.columns[9].value()==0
                checks+=1
                if child not in seen:following.add(child)
        seen.update(following);frontier=following
        levels.append({'depth':generation,'new_distinct_bend_tuples':len(following),
                       'reflection_checks':checks,'invariant_ok':invariants})
    return {'ok':invariants and all(r['ok'] for r in q_rows),'q_models':q_rows,
            'reflection':'b_i := sum(b)-2*b_i','invariant':'sum(b)^2 = 3*sum(b_i^2)',
            'seed':[-1,2,2,3,3],'bend_levels':levels,'shared_frame':calc.frame.description(),
            'scope':'Coupled exact curvature algebra; no centers, nonoverlap proof, sphere-count claim or SHA exclusions'}


def progressive_study(max_bits=16384, persist=True):
    if type(max_bits) is not int or not 32 <= max_bits <= 65536:
        raise ValueError('Study ladder supports 32..65536 bits within the local memory budget')
    from .mathrevision import fingerprint
    revision=fingerprint(); revision_id=hashlib.sha256(json.dumps(revision,sort_keys=True).encode()).hexdigest()
    destination=ROOT/'validation/shared-abacus'; destination.mkdir(parents=True,exist_ok=True)
    cache_path=destination/'progress.json'
    prior=json.loads(cache_path.read_text()) if persist and cache_path.exists() else {}
    previous={r['input_bits']:r for r in prior.get('levels',[]) if r.get('ok')} if prior.get('revision_id')==revision_id else {}
    ladder=sorted(set(b for b in (32,256,4096,8192,16384,32768,65536,max_bits) if b<=max_bits))
    result={'started_at_utc':datetime.now(timezone.utc).isoformat(),'revision_id':revision_id,
            'source_fingerprint':revision,'levels':[], 'ok':True,
            'added_to_miner':True,'scope':'Exact coupled formulas and recurrence evaluation, not SHA search reduction',
            'claims':claims(),'native_memory_limit_rods':8192}
    for bits in ladder:
        row=dict(previous[bits],reused_prior_validation=True) if bits in previous else study_level(bits)
        result['levels'].append(row);result['ok'] &= row['ok']
        if persist:
            from .settings import atomic_json
            atomic_json(cache_path,result)
        if not row['ok']: break
    result['source_unchanged']=fingerprint()==revision
    result['ok'] &= result['source_unchanged']
    result['resident_root_builds']=shared_pool().builds
    result['structure']=structure_study()
    result['ok'] &= result['structure']['ok'] and fingerprint()==revision
    if persist:
        from .settings import atomic_json
        atomic_json(cache_path,result)
        atomic_json(destination/'proof-inventory.json',inventory())
        with (destination/'study-history.jsonl').open('a') as log:log.write(json.dumps(result)+'\n')
    return result
