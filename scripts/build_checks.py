#!/usr/bin/env python3
"""Compile fresh review modules against a previously built, authenticated QCD project."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

MODULES = ['MassFitSpec', 'MassFitProof', 'AcceptanceSpec', 'AcceptanceProof']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--built-source', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--suite', choices=['original', 'semantic', 'flavor', 'sensitivity', 'body', 'robustness', 'normalization', 'mass-current'], default='original')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, work, leanbin = args.built_source.resolve(), args.work.resolve(), args.lean_bin.resolve()
    work.mkdir(parents=True, exist_ok=False)
    snapshot = json.loads((repo/'evidence/supplied-target/staged-source-hashes.json').read_text())
    for rel, digest in snapshot.items():
        if sha(source/rel) != digest: raise SystemExit('Source mismatch: '+rel)
    env = os.environ.copy()
    env['PATH'] = str(leanbin)+os.pathsep+env.get('PATH','')
    paths = subprocess.check_output([str(leanbin/'lake'),'env','printenv','LEAN_PATH'],cwd=source,env=env,text=True).strip()
    env['LEAN_PATH'] = str(work)+os.pathsep+paths
    env['LEAN_NUM_THREADS'] = '4'
    if args.suite == 'mass-current':
        from mass_current_suite import AUDITS, MODULES as mass_current_modules, PREFIX
        modules = mass_current_modules
    elif args.suite == 'normalization':
        from normalization_suite import AUDITS, MODULES as normalization_modules, PREFIX
        modules = normalization_modules
    elif args.suite == 'robustness':
        from robustness_suite import AUDITS, MODULES as robustness_modules, PREFIX
        modules = robustness_modules
    elif args.suite == 'body':
        from body_suite import AUDITS, MODULES as body_modules, PREFIX
        modules = body_modules
    elif args.suite == 'sensitivity':
        from sensitivity_suite import AUDITS, MODULES as sensitivity_modules, PREFIX
        modules = sensitivity_modules
    elif args.suite == 'flavor':
        from flavor_suite import AUDITS, MODULES as flavor_modules, PREFIX
        modules = flavor_modules
    elif args.suite == 'semantic':
        from semantic_suite import AUDITS, MODULES as semantic_modules, PREFIX
        modules = semantic_modules
    else:
        modules = MODULES
    review_hashes={m:sha(repo/'checks'/(m+'.lean')) for m in modules}
    tool_hashes={str(p):sha(p) for p in [leanbin/'lean',leanbin/'lake']}
    results=[]
    for module in modules:
        file=repo/'checks'/(module+'.lean')
        command=[str(leanbin/'lean'),'--root='+str(repo/'checks'),'-o',str(work/(module+'.olean')),str(file)]
        started=datetime.now(timezone.utc).isoformat()
        with (work/(module+'.log')).open('w') as stream:
            p=subprocess.run(command,cwd=source,env=env,stdout=stream,stderr=subprocess.STDOUT)
        output=(work/(module+'.log')).read_text()
        axioms={name:re.findall(r'[\w.]+',contents) for name,contents in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output)}
        expected = len(AUDITS[module]) if args.suite != 'original' else (4 if module.endswith('Proof') else 0)
        names_ok = args.suite == 'original' or set(axioms) == {PREFIX+n for n in AUDITS[module]}
        ok=p.returncode==0 and len(axioms)==expected and names_ok and not any(set(v)-ALLOWED for v in axioms.values()) and 'declaration uses \'sorry\'' not in output
        result={'module':module,'status':'passed' if ok else 'failed','exit_code':p.returncode,'started_utc':started,
                'finished_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':sha(file),'log_sha256':sha(work/(module+'.log')),'axioms':axioms}
        results.append(result)
        record={'suite':args.suite,'status':'running','scope':'Fresh review compilation; reuses previously built submission; not a new full build','source_files_verified':len(snapshot),'review_source_sha256':review_hashes,'tools_sha256':tool_hashes,'results':results}
        if not ok: record['status']='failed'
        (work/'results.json').write_text(json.dumps(record,indent=2)+'\n')
        print(module+': '+result['status'],flush=True)
        if not ok:
            print(output[-10000:]);raise SystemExit(1)
    stable=all(sha(source/p)==h for p,h in snapshot.items()) and all(sha(repo/'checks'/(m+'.lean'))==h for m,h in review_hashes.items()) and all(sha(Path(p))==h for p,h in tool_hashes.items())
    record.update(status='passed' if stable else 'failed',inputs_unchanged=stable)
    (work/'results.json').write_text(json.dumps(record,indent=2)+'\n')
    if not stable: raise SystemExit('Inputs changed during compilation')

if __name__=='__main__': main()
