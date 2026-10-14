#!/usr/bin/env python3
"""Kernel-check finite miner outputs and universal traversal identities via Lake.

This does not claim a formal refinement proof of Python/C or all Aristotle files.
Only Std is imported; no Mathlib proof worker is started beside a running miner.
"""
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
from fractions import Fraction
from math import gcd, isqrt

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer import pqmath as p, rodmath as r, thesis2 as t, coreprimes as c
from btcminer.protocol import DIFF1, target_from_bits, target_from_difficulty

OUT=ROOT/'validation/miner-lean-check'
BIN=ROOT/'.test-tools/lean-4.28.0-darwin_aarch64/bin'

def natlist(xs): return '['+', '.join(str(x) for x in xs)+']'

def main():
    expressions=[]
    def check(group, expression): expressions.append((group,expression))
    for step in range(1,360):
        if gcd(step,360)==1:
            check('dial_inverse',f'({step} * {pow(step,-1,360)}) % 360 = 1')
    for n in range(257):
        check('dynamic_rods',f'trialPrime {n} 17 = {str(p.is_prime(n)).lower()}')
    for prime in t.qualifying_primes():
        check('qualifying_prime',f'trialPrime {prime} 380 = true ∧ 144000 % ({prime}-1) = 0')
    for start in range(0,144002,256):
        size=min(256,144002-start)
        expected=[q for q in t.qualifying_primes() if start <= q < start+size]
        check('qualifying_census',f'qualifyingChunk {start} {size} = {natlist(expected)}')
    for n in (0,1,359,360,143999,144000,4294943999,4294944000,4294967295):
        abacus=p.RodAbacus((128,9,125)); residues=abacus.reading(n); out=abacus.reconstruct(residues)
        check('crt',f'{out} < 144000 ∧ '+ ' ∧ '.join(f'{out} % {rod} = {residue}' for rod,residue in zip(abacus.rods,residues)))
    for n in (0,1,2,3,19,121,209,5041):
        for denominator in (1,2,7):
            v=Fraction(n,denominator);floor=p.floor_sqrt(v);ceil=p.ceil_sqrt(v)
            check('rational_sqrt',f'{floor}^2 * {denominator} ≤ {n} ∧ {n} < ({floor}+1)^2*{denominator} ∧ {n} ≤ {ceil}^2*{denominator} ∧ ({ceil} = 0 ∨ ({ceil}-1)^2*{denominator} < {n})')
    for a,b in ((3,7),(11,19),(71,109),(97,109)):
        e=p.PQEllipse(a,b); area=e.area_over_pi_squared; minor=e.semi_minor_squared
        check('ellipse',f'{b}^2 = {a}^2 + 4*{minor.numerator}/{minor.denominator} ∧ {b}^4*{area.denominator} = {e.n}^2*{area.denominator}+16*{area.numerator}')
    for x in range(-4,5):
        for y in range(-4,5):
            digits=t.encode_gaussian(x,y)
            check('gaussian',f'gaussianValue {natlist(digits)} = (({x} : Int), ({y} : Int))')
    for base in (2,10,60):
        for denominator in range(2,32):
            result=t.expand(denominator,base,max_digits=1000)
            digits=result['digits']; k=result['cycle_start']; size=len(digits)
            a=' + '.join(f'{d}*{base}^{size-i-1}' for i,d in enumerate(digits))
            if k < 0:
                check('base_expansion',f'{denominator}*({a}) = {base}^{size}')
            else:
                prefix=' + '.join(f'{d}*{base}^{k-i-1}' for i,d in enumerate(digits[:k])) or '0'
                check('base_expansion',f'{denominator}*(({a})-({prefix})) = {base}^{size}-{base}^{k}')
    for start in range(0,144000,256):
        size=min(256,144000-start)
        expected=[x for x in t.square_roots_of_one() if start <= x < start+size]
        check('clock_roots',f'(((List.range {size}).map (fun x => x+{start})).filter (fun x => x*x % 144000 == 1)) = {natlist(expected)}')
    for prime in c.CORE:
        for grid in ('square','hexagonal'):
            h='true' if grid=='hexagonal' else 'false'
            check('prime_rod_circle',f'rodCount {prime} {h} = {r.rod_circle_count(prime,grid)}')
            radius=isqrt(4*prime//3)+1
            check('integer_circle',f'latticeCount {prime} {radius} {h} = {c.circle_count({prime:1},grid)}')
    for dimensions in (2,3,4):
        for n in (0,1,11,19,71,97,109):
            check('shell',f'shell {dimensions} {n} = {r.shell_count(dimensions,n)}')
    for a in (7,11,19):
        for b in (5,7,11):
            for exponent in range(4):
                check('tower',f'({a} ^ ({b}^{exponent})) % 360 = {r.tower3(a,b,exponent,360,12,2)}')
    for base in range(11*19):
        factor=r.split_with(209,base,144000,(2,3,5))
        if factor is not None:
            check('split_soundness',f'1 < {factor} ∧ {factor} < 209 ∧ 209 % {factor} = 0')
    for bits in ('01010000','02008000','03008000','1d00ffff','207fffff','17034219',
                 '2100ffff','220000ff','20010000','01123456'):
        n=int(bits,16);check('compact_target',f'compact {n} = {target_from_bits(bits)}')
    for value in ('0.125','3.7','1','2',str(DIFF1),str(DIFF1+1),str(2*DIFF1),'1e100'):
        d=Fraction(value)
        check('difficulty_floor',f'min (2^256-1) ({DIFF1}*{d.denominator}/{d.numerator}) = {target_from_difficulty(value)}')
    # Certify the complete finite field label table that feeds every live traversal.
    labels=[a+19*b-1 for a,b in t.board_loop()]
    # Boolean membership certificates avoid a quadratic Decidable/Nodup proof
    # term while still checking all 360 labels and the exact table length.
    for start in range(0,360,16):
        size=min(16,360-start)
        check('board_permutation',f'let labels : List Nat := {natlist(labels)}; labels.length = 360 ∧ (List.range {size}).all (fun n => labels.contains (n+{start})) = true')
    for prime in t.qualifying_primes():
        check('cell_inverse',f'({prime} * {pow(prime,-1,400)}) % 400 = 1')
    header='''import MinerMath.Core
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MinerMath

def trialPrime (n bound : Nat) : Bool :=
  n ≥ 2 && (bound+1)^2 > n && (List.range (bound+1)).all (fun d => d < 2 || d ≥ n || n % d != 0)
def qualifyingChunk (start size : Nat) : List Nat :=
  ((List.range size).map (fun x => x+start)).filter (fun n => n ≥ 7 && 144000 % (n-1) == 0 && trialPrime n 380)
def rodCount (n : Nat) (hex : Bool) : Nat :=
  ((List.range n).flatMap fun x => (List.range n).filter fun y =>
    (x*x+y*y+(if hex then x*y else 0)) % n == 1).length
def latticeCount (n radius : Nat) (hex : Bool) : Nat :=
  ((List.range (2*radius+1)).flatMap fun i => (List.range (2*radius+1)).filter fun j =>
    let x : Int := Int.ofNat i - Int.ofNat radius
    let y : Int := Int.ofNat j - Int.ofNat radius
    x*x+y*y-(if hex then x*y else 0) == (n : Int)).length
def shell : Nat → Nat → Nat
  | 0,n => if n == 0 then 1 else 0
  | d+1,n => shell d n + 2 * ((List.range (n+1)).foldl (fun s i =>
      if i > 0 && i*i ≤ n then s + shell d (n-i*i) else s) 0)
def gaussianValue : List Nat → Int × Int
  | [] => (0,0)
  | d::ds => let (x,y) := gaussianValue ds; ((d : Int)-x-y,x-y)
def compact (bits : Nat) : Nat :=
  let exponent := bits / 16777216
  let mantissa := bits % 8388608
  if exponent ≤ 3 then mantissa / 2^(8*(3-exponent)) else mantissa * 2^(8*(exponent-3))
'''
    # Independent chunks bound Lean's retained kernel reduction cache. The old
    # monolithic file exhausted its 1536 MiB limit near the shell certificates.
    (OUT/'MinerMath/VectorDefs.lean').write_text(header+'\nend MinerMath\n')
    modules=[]
    for start in range(0,len(expressions),128):
        module=f'MinerMath.VectorChunk{start//128:03d}'; modules.append(module)
        body=[]
        for i,(group,expression) in enumerate(expressions[start:start+128],start):
            name=f'{group}_{i:04d}'
            body += [f'theorem {name} : {expression} := by decide +kernel',f'#print axioms {name}']
        (OUT/(module.replace('.','/')+'.lean')).write_text(
            'import MinerMath.VectorDefs\nset_option maxRecDepth 1000000\n'
            'set_option maxHeartbeats 0\nnamespace MinerMath\n'+'\n'.join(body)+'\nend MinerMath\n')
    (OUT/'MinerMath/Vectors.lean').write_text(''.join('import '+m+'\n' for m in modules))
    env=dict(os.environ,PATH=str(BIN)+os.pathsep+os.environ['PATH'],PYTHONDONTWRITEBYTECODE='1')
    report={'checked_at_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
            'scope':'Universal traversal/CRT/ellipse and strict target/pruning/carry contracts plus finite certificates of actual Python outputs; not a formal Python/C refinement or full Aristotle audit',
            'certificates':len(expressions),'groups':sorted(set(g for g,_ in expressions)),
            'python_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted((ROOT/'btcminer').glob('*.py'))},
            'lean_version':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
            'lake_version':subprocess.check_output([str(BIN/'lake'),'--version'],text=True).strip()}
    with (OUT/'lake-build.log').open('w') as log:
        # Build serially, including helpers, so independent Lake jobs cannot
        # multiply the memory budget on this machine.
        for module in ['MinerMath.Core','MinerMath.Strict','MinerMath.VectorDefs',*modules,None]:
            command=[str(BIN/'lake'),'build']+(['+'+module] if module else [])
            process=subprocess.Popen(command,cwd=OUT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                code=process.wait(timeout=180)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL)
                process.wait()
                code=124
            if code:break
        result=subprocess.CompletedProcess(command,code)
    core_names=['uint32_decomposition','last_tile_size','inverse_step','phase_injective',
                'ellipse_difference_squares','crt_unique']
    strict_names=['accepted_iff_mem','accepted_value_count','zero_target_accepts_only_zero',
                  'smoothed_score_bound',
                  'difficulty_floor_zero','floor_threshold_exact','prefix_necessary',
                  'prefix_counterexample','retain_winner','removed_is_loser','five_word_carry',
                  'final_tile_valid','tile_coordinates_injective','signed_interval_unique']
    names=core_names+['Strict.'+name for name in strict_names]+[f'{group}_{i:04d}' for i,(group,_) in enumerate(expressions)]
    audit=OUT/'Audit.lean'
    audit.write_text('import MinerMath\n'+'\n'.join('#print axioms MinerMath.'+name for name in names)+'\n')
    audit_code=None
    if result.returncode==0:
        with (OUT/'axioms.log').open('w') as log:
            audit_process=subprocess.Popen([str(BIN/'lake'),'env','lean','-j1','-M1536','Audit.lean'],
                cwd=OUT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                audit_code=audit_process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                os.killpg(audit_process.pid,signal.SIGKILL)
                audit_process.wait()
                audit_code=124
    output=(OUT/'axioms.log').read_text() if audit_code is not None else (OUT/'lake-build.log').read_text()
    audited_count=sum('does not depend on any axioms' in line or 'depends on axioms:' in line for line in output.splitlines())
    axioms=set(a.strip() for match in re.findall(r'depends on axioms: \[([^]]*)\]',output) for a in match.split(','))
    report.update(ok=result.returncode==0 and audit_code==0 and audited_count==len(names) and axioms <= {'propext','Classical.choice','Quot.sound'},exit_code=result.returncode,axiom_audit_exit_code=audit_code,audited_theorems=audited_count,axioms=sorted(axioms),
                  lean_sha256={str(path.relative_to(OUT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in OUT.rglob('*.lean')})
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('ok','certificates','groups','axioms')},indent=2))
    return 0 if report['ok'] else 1

if __name__=='__main__':raise SystemExit(main())
