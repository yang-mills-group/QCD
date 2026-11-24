#!/usr/bin/env python3
"""Run explicit positive/negative controls through both-kernel Comparator mode."""
import argparse, hashlib, json, os, subprocess
from datetime import datetime,timezone
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean-bin',type=Path,required=True);p.add_argument('--tools-bin',type=Path,required=True);p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
    lean=a.lean_bin.resolve();tools=a.tools_bin.resolve()
    env=os.environ.copy();env.update(PATH=str(lean)+os.pathsep+env['PATH'],LEAN_NUM_THREADS='4',COMPARATOR_LANDRUN=str(tools/'landrun-mac'),COMPARATOR_LEAN4EXPORT=str(tools/'lean4export'),COMPARATOR_NANODA=str(tools/'nanoda_bin'))
    cases={
      'valid':('theorem check : 1+1=2 := by sorry\n','theorem check : 1+1=2 := by rfl\n',None),
      'wrong_statement':('theorem check : 1+1=2 := by sorry\n','theorem check : 2+2=4 := by rfl\n','theorem statement do not match'),
      'custom_axiom':('theorem check : 1+1=2 := by sorry\n','axiom bad : 1+1=2\ntheorem check : 1+1=2 := bad\n',"Illegal axiom detected: 'bad'"),
      'sorry_proof':('theorem check : 1+1=2 := by sorry\n','theorem check : 1+1=2 := by sorry\n',"Illegal axiom detected: 'sorryAx'"),
      'changed_definition':('def Target : Prop := False\ntheorem check : Target := by sorry\n','def Target : Prop := True\ntheorem check : Target := by trivial\n',"Const does not match between challenge and target 'Target'"),
    }
    result={'started_utc':datetime.now(timezone.utc).isoformat(),'mode':'macOS fake-landrun; no Linux isolation','tools_sha256':{x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in tools.iterdir() if x.is_file()},'checks':[]}
    for name,(challenge,solution,expected) in cases.items():
        project=work/name;project.mkdir()
        (project/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
        (project/'lakefile.toml').write_text('name="control"\nversion="0.1.0"\n[[lean_lib]]\nname="Challenge"\n[[lean_lib]]\nname="Solution"\n')
        (project/'Challenge.lean').write_text(challenge);(project/'Solution.lean').write_text(solution)
        (project/'comparator.json').write_text(json.dumps(dict(challenge_module='Challenge',solution_module='Solution',theorem_names=['check'],permitted_axioms=['propext','Classical.choice','Quot.sound'],enable_nanoda=True)))
        run=subprocess.run([str(lean/'lake'),'env',str(tools/'comparator'),'comparator.json'],cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
        (project/'run.log').write_text(run.stdout)
        if expected:ok=run.returncode!=0 and expected in run.stdout
        else:ok=run.returncode==0 and all(x in run.stdout for x in ['Nanoda kernel accepts the solution','Lean default kernel accepts the solution','Your solution is okay!'])
        result['checks'].append(dict(case=name,passed=ok,exit_code=run.returncode,log_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),expected_diagnostic=expected))
        result['status']='passed' if all(x['passed'] for x in result['checks']) else 'failed'
        (work/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(name+': '+str(ok),flush=True)
        if not ok:raise SystemExit(run.stdout)
if __name__=='__main__':main()
