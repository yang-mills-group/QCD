#!/usr/bin/env python3
"""Check that freshly compiled review proofs reject specific changed specifications.
Only disposable review copies are mutated. The authenticated submission is read-only.
These are Lean compilation controls, not additional Comparator/kernel-export runs.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from flavor_suite import AUDITS, MODULES, PREFIX

SUITE = 'flavor'

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
INFRASTRUCTURE_ERRORS = (
    'unknown module prefix', 'unknown identifier', 'unknownidentifier', 'object file',
    'permission denied', 'interrupted', 'failed to read', 'maximum number of heartbeats',
    'maximum recursion depth', 'deterministic timeout', '(deterministic) timeout',
    'tactic timed out', 'stack overflow', 'out of memory', 'failed to allocate memory',
    'resource exhausted',
)

def has_infrastructure_error(output):
    return any(pattern in output.lower() for pattern in INFRASTRUCTURE_ERRORS)

CASES = [
    ('unchanged', 'FlavorSpec', None, None, 'FlavorProof'),
    ('half_fermion_screening', 'FlavorSpec', '11 - 2 * f / 3', '11 - f / 3', 'FlavorProof'),
    ('relaxed_trajectory_budget', 'FlavorSpec', 'QCD.su.slopeConstant / 2', 'QCD.su.slopeConstant / 3', 'FlavorProof'),
    ('wrong_two_loop_flavor', 'FlavorSpec', '102 - 38 * f / 3', '102 - 39 * f / 3', 'TwoLoopProof'),
    ('extra_determinant_flavor', 'FlavorDeterminantSpec', 'fun _ : Fin F => M', 'fun _ : Fin (F+1) => M', 'FlavorDeterminantProof'),
    ('missing_loglog_term', 'TwoLoopSpec', 'A*t + k*Real.log t', 'A*t', 'TwoLoopProof'),
    ('wrong_loglog_normalization', 'TwoLoopSpec', '6*gBeta1 f/gBeta0 f', '3*gBeta1 f/gBeta0 f', 'TwoLoopProof'),
    ('reversed_beta_flow', 'BanksZaksSpec', '-2 * a^2 * (oneLoopCoefficient', '2 * a^2 * (oneLoopCoefficient', 'BanksZaksProof'),
    ('wrong_wilson_convention', 'RunningConventionSpec', ': ℝ := 6/g^2', ': ℝ := 3/g^2', 'RunningConventionProof'),
    ('wrong_three_loop_flavor', 'BZHigherOrderSpec', '325*f^2/54', '324*f^2/54', 'BZHigherOrderProof'),
]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for flag in ['built-source', 'lean-bin', 'baseline', 'work']:
        p.add_argument('--'+flag, type=Path, required=True)
    a = p.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, lean, baseline, work = [v.resolve() for v in [a.built_source,a.lean_bin,a.baseline,a.work]]
    work.mkdir(parents=True, exist_ok=False)
    base = json.loads((baseline/'results.json').read_text())
    if base['suite'] != SUITE or base['status'] != 'passed' or not base['inputs_unchanged']:
        raise SystemExit('Need an accepted fresh '+SUITE+'-suite compilation')
    frozen = {m:sha(repo/'checks'/(m+'.lean')) for m in MODULES}
    if frozen != base['review_source_sha256']: raise SystemExit('Baseline source mismatch')
    snapshot = json.loads((repo/'evidence/supplied-target/staged-source-hashes.json').read_text())
    if not all(sha(source/k)==v for k,v in snapshot.items()): raise SystemExit('Submission mismatch')
    toolhash = {str(x):sha(x) for x in [lean/'lean',lean/'lake']}
    env = os.environ.copy()
    env.update(PATH=str(lean)+os.pathsep+env.get('PATH',''),LEAN_NUM_THREADS='4')
    paths = subprocess.check_output([str(lean/'lake'),'env','printenv','LEAN_PATH'],cwd=source,env=env,text=True).strip()
    record = dict(status='running',suite=SUITE,started_utc=now(),source_files_verified=len(snapshot),
        review_source_sha256=frozen,tools_sha256=toolhash,baseline_receipt_sha256=sha(baseline/'results.json'),checks=[])
    for name,module,old,new,last in CASES:
        folder=work/name; src=folder/'src'; build=folder/'build'
        src.mkdir(parents=True); build.mkdir()
        for m in MODULES: shutil.copyfile(repo/'checks'/(m+'.lean'),src/(m+'.lean'))
        first=MODULES.index(module); stop=MODULES.index(last)
        for m in MODULES[:first]: shutil.copyfile(baseline/(m+'.olean'),build/(m+'.olean'))
        changed=src/(module+'.lean')
        if old is not None:
            value=changed.read_text()
            if value.count(old)!=1: raise SystemExit('Mutation must match exactly once: '+name)
            changed.write_text(value.replace(old,new,1))
        case=dict(case=name,changed_module=module,old=old,new=new,expected_failure_module=None if old is None else last,
            original_sha256=frozen[module],mutated_sha256=sha(changed),modules=[])
        runenv=dict(env,LEAN_PATH=str(build)+os.pathsep+paths)
        failed=None; diagnostic=''
        for m in MODULES[first:stop+1]:
            log=folder/(m+'.log')
            with log.open('w') as stream:
                r=subprocess.run([str(lean/'lean'),'--root='+str(src),'-o',str(build/(m+'.olean')),str(src/(m+'.lean'))],
                    cwd=source,env=runenv,stdout=stream,stderr=subprocess.STDOUT)
            out=log.read_text()
            axioms={n:re.findall(r'[\w.]+',v) for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",out)}
            names_ok=set(axioms)=={PREFIX+n for n in AUDITS[m]}
            okay=r.returncode==0 and names_ok and all(set(v)<=ALLOWED for v in axioms.values())
            case['modules'].append(dict(module=m,exit_code=r.returncode,log_sha256=sha(log),audit_passed=okay))
            if not okay:
                failed=m; diagnostic=out
                break
        compiler_rejection = failed == last and case['modules'][-1]['exit_code']==1 and 'error:' in diagnostic
        case.update(observed_failure_module=failed,passed=(failed is None if old is None else compiler_rejection and not has_infrastructure_error(diagnostic)))
        record['checks'].append(case)
        (work/'results.json').write_text(json.dumps(record,indent=2)+'\n')
        print(name+': '+('passed' if case['passed'] else 'FAILED'),flush=True)
        if not case['passed']: raise SystemExit(diagnostic[-5000:] or 'Unexpected mutation result')
    stable=all(sha(repo/'checks'/(m+'.lean'))==v for m,v in frozen.items()) and all(sha(source/k)==v for k,v in snapshot.items()) and all(sha(Path(k))==v for k,v in toolhash.items())
    record.update(status='passed' if stable else 'failed',finished_utc=now(),inputs_unchanged=stable)
    (work/'results.json').write_text(json.dumps(record,indent=2)+'\n')
    if not stable: raise SystemExit('Inputs changed during controls')

if __name__=='__main__': main()
