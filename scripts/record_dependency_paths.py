#!/usr/bin/env python3
"""Authenticate inputs and inspect declaration dependencies in the Lean environment."""
import argparse,hashlib,json,os,subprocess
from datetime import datetime,timezone
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for name in ['built-source','lean-bin','work']:p.add_argument('--'+name,type=Path,required=True)
 a=p.parse_args();repo=Path(__file__).resolve().parents[1]
 source,lean,work=[v.resolve() for v in [a.built_source,a.lean_bin,a.work]]
 work.mkdir(parents=True,exist_ok=False)
 snapshot=json.loads((repo/'evidence/supplied-target/staged-source-hashes.json').read_text())
 if not all(sha(source/k)==v for k,v in snapshot.items()):raise SystemExit('Source mismatch')
 program=repo/'audit/DependencyPaths.lean';before=sha(program)
 toolhash={str(p):sha(p) for p in [lean/'lean',lean/'lake']}
 env=os.environ.copy();env['PATH']=str(lean)+os.pathsep+env.get('PATH','')
 env['LEAN_PATH']=subprocess.check_output([str(lean/'lake'),'env','printenv','LEAN_PATH'],cwd=source,env=env,text=True).strip()
 env['LEAN_NUM_THREADS']='4'
 start=datetime.now(timezone.utc).isoformat()
 with (work/'inspection.log').open('w') as out:
  r=subprocess.run([str(lean/'lean'),str(program)],cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT)
 lines=(work/'inspection.log').read_text().splitlines()
 payloads=[x.split('DEPENDENCY_JSON ',1)[1] for x in lines if 'DEPENDENCY_JSON ' in x]
 if r.returncode or len(payloads)!=1:raise SystemExit('\n'.join(lines[-30:]))
 graph=json.loads(payloads[0])
 stable=sha(program)==before and all(sha(source/k)==v for k,v in snapshot.items()) and all(sha(Path(k))==v for k,v in toolhash.items())
 result=dict(status='passed' if stable else 'failed',exit_code=r.returncode,started_utc=start,
  finished_utc=datetime.now(timezone.utc).isoformat(),inputs_unchanged=stable,source_files_verified=len(snapshot),
  program_sha256=before,tools_sha256=toolhash,log_sha256=sha(work/'inspection.log'),inspection=graph,
  scope='Compiler-environment diagnostic, not a new kernel theorem. Edges can occur in types or values. Absence from this restricted traversal is not mathematical independence.')
 (work/'result.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
 print(result['status'],graph['visited_YM_declarations'])
 for x in graph['targets']:print(x['target'],x['in_restricted_dependency_closure'],len(x['path']))
 if not stable:raise SystemExit('Inputs changed')
if __name__=='__main__':main()
