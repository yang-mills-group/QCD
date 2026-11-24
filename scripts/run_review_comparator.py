#!/usr/bin/env python3
"""Check the fresh review targets against an already-built authenticated submission.
This is a review overlay. It does not claim a second clean submission build.
"""
import argparse,hashlib,json,os,shutil,subprocess,time
from datetime import datetime,timezone
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
    p=argparse.ArgumentParser(description=__doc__)
    for flag in ['built-source','lean-bin','tools-bin','work']:p.add_argument('--'+flag,type=Path,required=True)
    p.add_argument('--suite',choices=['original','semantic','flavor','sensitivity','body','robustness','normalization'],default='original')
    a=p.parse_args();repo=Path(__file__).resolve().parents[1];source=a.built_source.resolve();lean=a.lean_bin.resolve();tools=a.tools_bin.resolve();work=a.work.resolve()
    work.mkdir(parents=True,exist_ok=False);project=work/'project';project.mkdir();evidence=work/'evidence';evidence.mkdir()
    snapshot=json.loads((repo/'evidence/supplied-target/staged-source-hashes.json').read_text())
    for path,digest in snapshot.items():
        if sha(source/path)!=digest:raise SystemExit('Submission mismatch: '+path)
    modules=['MassFitSpec','MassFitProof','AcceptanceSpec','AcceptanceProof']
    challenge,solution='ReviewChallenge','ReviewSolution'
    config_dir=repo/'comparator'
    if a.suite=='normalization':
        from normalization_suite import MODULES
        modules=MODULES
        challenge,solution='NormalizationChallenge','NormalizationSolution'
        config_dir=config_dir/'normalization'
    elif a.suite=='robustness':
        from robustness_suite import MODULES
        modules=MODULES
        challenge,solution='RobustnessChallenge','RobustnessSolution'
        config_dir=config_dir/'robustness'
    elif a.suite=='body':
        from body_suite import MODULES
        modules=MODULES
        challenge,solution='BodyChallenge','BodySolution'
        config_dir=config_dir/'body'
    elif a.suite=='sensitivity':
        from sensitivity_suite import MODULES
        modules=MODULES
        challenge,solution='SensitivityChallenge','SensitivitySolution'
        config_dir=config_dir/'sensitivity'
    elif a.suite=='flavor':
        from flavor_suite import MODULES
        modules=MODULES
        challenge,solution='FlavorChallenge','FlavorSolution'
        config_dir=config_dir/'flavor'
    elif a.suite=='semantic':
        from semantic_suite import MODULES
        modules=MODULES
        challenge,solution='SemanticChallenge','SemanticSolution'
        config_dir=config_dir/'semantic'
    for m in modules:shutil.copyfile(repo/'checks'/(m+'.lean'),project/(m+'.lean'))
    for name in [challenge+'.lean',solution+'.lean','comparator.json']:shutil.copyfile(config_dir/name,project/name)
    shutil.copyfile(source/'lean-toolchain',project/'lean-toolchain')
    (project/'lakefile.toml').write_text('name="qcd_review"\nversion="0.1.0"\npackagesDir='+json.dumps(str(source/'.lake/packages'))+'\n[[lean_lib]]\nname="ReviewSupport"\nroots='+json.dumps(modules)+'\n[[lean_lib]]\nname='+json.dumps(challenge)+'\n[[lean_lib]]\nname='+json.dumps(solution)+'\n[[require]]\nname="bootstrap_B"\npath='+json.dumps(str(source))+'\n')
    manifest=json.loads((source/'lake-manifest.json').read_text());manifest['name']='qcd_review';manifest['packagesDir']=str(source/'.lake/packages')
    for dep in manifest['packages']:dep['inherited']=True
    manifest['packages'].append(dict(type='path',name='bootstrap_B',scope='',dir=str(source),inherited=False,configFile='lakefile.toml',manifestFile='lake-manifest.json'));save(project/'lake-manifest.json',manifest)
    frozen={x.name:sha(x) for x in project.iterdir() if x.is_file()}
    toolhash={str(x):sha(x) for x in list(tools.iterdir())+[lean/'lean',lean/'lake'] if x.is_file()}
    env=os.environ.copy();env.update(PATH=str(lean)+os.pathsep+env['PATH'],LEAN_NUM_THREADS='4',COMPARATOR_LANDRUN=str(tools/'landrun-mac'),COMPARATOR_LEAN4EXPORT=str(tools/'lean4export'),COMPARATOR_NANODA=str(tools/'nanoda_bin'))
    cmd=[str(lean/'lake'),'env',str(tools/'comparator'),'comparator.json'];record=dict(status='running',suite=a.suite,started_utc=now(),source_build_reused=True,review_build_initially_absent=True,source_files_verified=len(snapshot),review_inputs=frozen,tools_sha256=toolhash,command=cmd,mode='macOS fake-landrun; no Linux isolation')
    save(evidence/'result.json',record);start=time.monotonic()
    with (evidence/'comparator.log').open('w') as log:r=subprocess.run(cmd,cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT)
    output=(evidence/'comparator.log').read_text();markers=['Nanoda kernel accepts the solution','Lean default kernel accepts the solution','Your solution is okay!']
    stable=all(sha(project/x)==h for x,h in frozen.items()) and all(sha(Path(x))==h for x,h in toolhash.items()) and all(sha(source/x)==h for x,h in snapshot.items())
    ok=r.returncode==0 and all(x in output.splitlines() for x in markers) and stable
    record.update(status='passed' if ok else 'failed',exit_code=r.returncode,finished_utc=now(),elapsed_seconds=round(time.monotonic()-start,2),inputs_unchanged=stable,log_sha256=sha(evidence/'comparator.log'));save(evidence/'result.json',record)
    print(record['status']);print(output[-4000:]);raise SystemExit(0 if ok else 1)
if __name__=='__main__':main()
