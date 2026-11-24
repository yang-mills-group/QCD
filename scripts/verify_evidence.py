#!/usr/bin/env python3
"""Check packaged evidence consistency, required verdicts and pinned review files.
This validates records; it does not rerun a kernel or authenticate an external signer.
"""
import hashlib,importlib,json,re,tarfile
from fractions import Fraction
from pathlib import Path
from test_flavor_mutations import has_infrastructure_error

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise SystemExit('FAIL: '+message)

def check_axiom_log(path,expected):
    """Cross-check structured receipts against the actual compiler messages."""
    output=path.read_text()
    reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output)
    observed={name:re.findall(r'[\w.]+',contents) for name,contents in reports}
    require(len(reports)==len(observed),'no duplicate axiom reports '+str(path))
    require(observed==expected,'axiom receipt matches compiler log '+str(path))
    require("declaration uses 'sorry'" not in output,'no proof holes '+str(path))

def check_manifest(repo):
    """Check all packaged files, including omissions from the manifest itself."""
    manifest='provenance/review-files.sha256'
    entries={}
    for line in (repo/manifest).read_text().splitlines():
        match=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
        require(match is not None,'manifest record format')
        digest,name=match.groups()
        path=Path(name)
        require(not path.is_absolute() and '..' not in path.parts and name==path.as_posix(),
            'manifest relative path '+name)
        require(name not in entries and name!=manifest,'manifest unique entry '+name)
        entries[name]=digest
    packaged={name for name in ['.gitignore','LICENSE','NOTICE','README.md','VERIFICATION.md'] if (repo/name).is_file()}
    for directory in ['audit','checks','comparator','docs','evidence','provenance','scripts']:
        for path in (repo/directory).rglob('*'):
            if path.is_file() and '__pycache__' not in path.parts and path.suffix!='.pyc' and path.name!='.DS_Store':
                packaged.add(path.relative_to(repo).as_posix())
    packaged.discard(manifest)
    require(set(entries)==packaged,'manifest inventory: missing '+str(sorted(packaged-set(entries)))+
        ', unexpected '+str(sorted(set(entries)-packaged)))
    for name,digest in entries.items():
        require(sha(repo/name)==digest,'review manifest '+name)
    return len(entries)

def main():
    repo=Path(__file__).resolve().parents[1]
    def read(path):return json.loads((repo/path).read_text())
    supplied=repo/'evidence/supplied-target';new=repo/'evidence/independent-checks'
    meta=read('provenance/submission.json');archive=repo/meta['source_archive']
    require(sha(archive)==meta['source_archive_sha256'],'source archive')
    require(sha(repo/'docs/informal-part-VI-review-r02.pdf')==meta['informal_review_sha256'],'informal review')
    copied=repo/'provenance/supplied-comparator';archive_hashes={}
    with tarfile.open(archive) as t:
        for m in t.getmembers():
            if not m.isfile():continue
            name=m.name.removeprefix('massive-qcd-lean/')
            digest=hashlib.sha256(t.extractfile(m).read()).hexdigest();archive_hashes[name]=digest
            if name.startswith('comparator/'):
                require(sha(copied/name.removeprefix('comparator/'))==digest,'copied verifier '+name)
    status=read('evidence/supplied-target/status.json')
    require(status['status']=='passed' and status['stage']=='complete','supplied completion')
    markers=['Nanoda kernel accepts the solution','Lean default kernel accepts the solution','Your solution is okay!']
    for folder,receipt in [(supplied,'comparator.json'),(new/'review-comparator','result.json')]:
        data=json.loads((folder/receipt).read_text());log=folder/'comparator.log'
        require(data['exit_code']==0 and sha(log)==data['log_sha256'],'comparator log integrity '+str(folder))
        require(all(m in log.read_text().splitlines() for m in markers),'both-kernel verdicts '+str(folder))
        if receipt=='result.json':
            require(data['status']=='passed' and data['inputs_unchanged'],'review comparator status')
            for name,digest in data['review_inputs'].items():
                current=repo/('checks' if name in ['MassFitSpec.lean','MassFitProof.lean','AcceptanceSpec.lean','AcceptanceProof.lean'] else 'comparator')/name
                if current.exists():require(sha(current)==digest,'review comparator source '+name)
    expected='32f8e0d3322520e251c27a96c7123aab2d695f68bb15fa60190e460cbe063dba'
    for name in ['reference-export','staged-reference-export']:
        data=read('evidence/supplied-target/'+name+'.json')
        require(data['exit_code']==0 and data['sha256']==expected and data['matches_published_digest'],'frozen export '+name)
    allowed={'propext','Classical.choice','Quot.sound'};theorems={}
    policies=list((repo/'comparator').rglob('comparator.json'))
    require(len(policies)==7,'seven review Comparator configurations')
    for path in policies:
        policy=json.loads(path.read_text())
        require(set(policy['permitted_axioms'])==allowed and policy['enable_nanoda'],
            'review Comparator axiom and kernel policy '+str(path.relative_to(repo)))
    data=read('evidence/independent-checks/results.json')
    require(len(data['results'])==4,'module count')
    for item in data['results']:
        m=item['module'];require(item['status']=='passed' and item['exit_code']==0,'Lean module '+m)
        require(sha(repo/'checks'/(m+'.lean'))==item['source_sha256'],'Lean source '+m)
        require(sha(new/(m+'.log'))==item['log_sha256'],'Lean log '+m)
        check_axiom_log(new/(m+'.log'),item['axioms'])
        for name,axioms in item['axioms'].items():require(set(axioms)<=allowed,'axioms '+name)
        theorems.update(item['axioms'])
    require(len(theorems)==8 and 'YMReview.QCD.acceptance' in theorems,'eight theorem audits')
    for file,count in [('mass-fit',44),('input-guard',9),('wilson',41)]:
        data=read('evidence/independent-checks/'+file+'.json')
        require(data['status']=='passed' and len(data['checks'])==count and all(c['passed'] for c in data['checks']),file+' checks')
        if file=='wilson':
            for path,digest in data['source_sha256'].items():require(archive_hashes['proof/'+path]==digest,'Wilson source '+path)
    data=read('evidence/independent-checks/comparator-controls/results.json')
    require(data['status']=='passed' and len(data['checks'])==5,'comparator controls')
    for case in data['checks']:
        log=new/'comparator-controls'/case['case']/'run.log'
        require(case['passed'] and sha(log)==case['log_sha256'],'control '+case['case'])
        if case['expected_diagnostic']:require(case['expected_diagnostic'] in log.read_text(),'control diagnostic '+case['case'])
    from semantic_suite import AUDITS, MODULES, PREFIX, TARGETS
    semantic=repo/'evidence/semantic-checks'
    data=read('evidence/semantic-checks/compilation/results.json')
    require(data['status']=='passed' and data['inputs_unchanged'],'semantic compilation status')
    require([x['module'] for x in data['results']]==MODULES,'semantic module inventory')
    semantic_theorems={}
    for item in data['results']:
        m=item['module'];require(item['status']=='passed' and item['exit_code']==0,'semantic Lean module '+m)
        require(sha(repo/'checks'/(m+'.lean'))==item['source_sha256']==data['review_source_sha256'][m],'semantic source '+m)
        require(sha(semantic/'compilation'/(m+'.log'))==item['log_sha256'],'semantic log '+m)
        check_axiom_log(semantic/'compilation'/(m+'.log'),item['axioms'])
        require(set(item['axioms'])=={PREFIX+n for n in AUDITS[m]},'semantic theorem inventory '+m)
        for name,axioms in item['axioms'].items():require(set(axioms)<=allowed,'semantic axioms '+name)
        semantic_theorems.update(item['axioms'])
    require(len(semantic_theorems)==37,'37 semantic-suite axiom reports')
    require(len(set(theorems)|set(semantic_theorems))==41,'41 distinct reviewed declarations')
    coverage=read('evidence/semantic-checks/coverage.json')
    require(coverage['new_audited_theorems']==33 and coverage['overall_physical_identification']=='incomplete','semantic coverage limits')
    require([x['id'] for x in coverage['areas']]==[1,2,3,4],'four correspondence areas')
    require(all(x.get('open') for x in coverage['areas'][1:]),'open physical obligations retained')
    sc=semantic/'comparator';data=json.loads((sc/'result.json').read_text())
    require(data['status']=='passed' and data['exit_code']==0 and data['inputs_unchanged'],'semantic comparator status')
    previous_tools=read('evidence/independent-checks/review-comparator/result.json')['tools_sha256']
    require(data['tools_sha256']==previous_tools,'same recorded tools as the previous accepted review run')
    require(sha(sc/'comparator.log')==data['log_sha256'],'semantic comparator log integrity')
    require(all(m in (sc/'comparator.log').read_text().splitlines() for m in markers),'semantic both-kernel verdicts')
    config=read('comparator/semantic/comparator.json')
    require(config['theorem_names']==[PREFIX+n for n in TARGETS],'seven semantic targets')
    for name,digest in data['review_inputs'].items():
        if name in {m+'.lean' for m in MODULES}:current=repo/'checks'/name
        elif name in ['SemanticChallenge.lean','SemanticSolution.lean','comparator.json']:current=repo/'comparator/semantic'/name
        else:current=sc/name
        require(sha(current)==digest,'semantic comparator input '+name)
    from flavor_suite import AUDITS as FA, MODULES as FM, TARGETS as FT
    flavor=repo/'evidence/flavor-checks'
    fd=read('evidence/flavor-checks/compilation/results.json')
    require(fd['suite']=='flavor' and fd['status']=='passed' and fd['inputs_unchanged'],'flavor compilation status')
    require([x['module'] for x in fd['results']]==FM,'flavor module inventory')
    flavor_theorems={}
    for item in fd['results']:
        m=item['module'];require(item['status']=='passed' and item['exit_code']==0,'flavor module '+m)
        require(sha(repo/'checks'/(m+'.lean'))==item['source_sha256']==fd['review_source_sha256'][m],'flavor source '+m)
        require(sha(flavor/'compilation'/(m+'.log'))==item['log_sha256'],'flavor log '+m)
        check_axiom_log(flavor/'compilation'/(m+'.log'),item['axioms'])
        require(set(item['axioms'])=={PREFIX+n for n in FA[m]},'flavor theorem inventory '+m)
        for name,axioms in item['axioms'].items():require(set(axioms)<=allowed,'flavor axioms '+name)
        flavor_theorems.update(item['axioms'])
    require(len(flavor_theorems)==82,'82 flavor-suite axiom reports')
    require(len(set(theorems)|set(semantic_theorems)|set(flavor_theorems))==112,'112 distinct reviewed declarations')
    fc=flavor/'comparator';data=json.loads((fc/'result.json').read_text())
    require(data['suite']=='flavor' and data['status']=='passed' and data['exit_code']==0 and data['inputs_unchanged'],'flavor comparator status')
    require(data['tools_sha256']==previous_tools,'flavor same recorded tools')
    require(sha(fc/'comparator.log')==data['log_sha256'],'flavor comparator log integrity')
    require(all(m in (fc/'comparator.log').read_text().splitlines() for m in markers),'flavor both-kernel verdicts')
    require(read('comparator/flavor/comparator.json')['theorem_names']==[PREFIX+n for n in FT],'twelve flavor targets')
    for name,digest in data['review_inputs'].items():
        if name in {m+'.lean' for m in FM}:current=repo/'checks'/name
        elif name in ['FlavorChallenge.lean','FlavorSolution.lean','comparator.json']:current=repo/'comparator/flavor'/name
        else:current=fc/name
        require(sha(current)==digest,'flavor comparator input '+name)
    extra_theorems={}
    for suite,tag,count,modules_count in [('sensitivity','Sensitivity',147,46),('body','Body',24,10),('robustness','Robustness',42,8),('normalization','Normalization',23,9)]:
        inventory=importlib.import_module(suite+'_suite')
        folder=repo/('evidence/'+suite+'-checks')
        comp=json.loads((folder/'compilation/results.json').read_text())
        require(comp['suite']==suite and comp['status']=='passed' and comp['inputs_unchanged'],suite+' compilation status')
        require(comp['tools_sha256']==fd['tools_sha256'],suite+' compilation tools')
        require([x['module'] for x in comp['results']]==inventory.MODULES and len(inventory.MODULES)==modules_count,suite+' module inventory')
        audited={}
        for item in comp['results']:
            m=item['module'];require(item['status']=='passed' and item['exit_code']==0,suite+' module '+m)
            require(sha(repo/'checks'/(m+'.lean'))==item['source_sha256']==comp['review_source_sha256'][m],suite+' source '+m)
            require(sha(folder/'compilation'/(m+'.log'))==item['log_sha256'],suite+' log '+m)
            check_axiom_log(folder/'compilation'/(m+'.log'),item['axioms'])
            require(set(item['axioms'])=={PREFIX+n for n in inventory.AUDITS[m]},suite+' theorem inventory '+m)
            for name,axioms in item['axioms'].items():require(set(axioms)<=allowed,suite+' axioms '+name)
            audited.update(item['axioms'])
            source=(repo/'checks'/(m+'.lean')).read_text()
            require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source),suite+' no proof bypass '+m)
        require(len(audited)==count,suite+' declaration audit count')
        extra_theorems.update(audited)
        evidence=folder/'comparator';run=json.loads((evidence/'result.json').read_text())
        require(run['suite']==suite and run['status']=='passed' and run['exit_code']==0 and run['inputs_unchanged'],suite+' comparator status')
        require(run['tools_sha256']==previous_tools,suite+' comparator tools')
        require(sha(evidence/'comparator.log')==run['log_sha256'],suite+' comparator log hash')
        require(all(m in (evidence/'comparator.log').read_text().splitlines() for m in markers),suite+' both-kernel verdicts')
        config=read('comparator/'+suite+'/comparator.json')
        require(config['theorem_names']==[PREFIX+n for n in inventory.TARGETS],suite+' challenge targets')
        require(set(config['permitted_axioms'])==allowed and config['enable_nanoda'],suite+' challenge policy')
        for name,digest in run['review_inputs'].items():
            if name in {m+'.lean' for m in inventory.MODULES}:current=repo/'checks'/name
            elif name in [tag+'Challenge.lean',tag+'Solution.lean','comparator.json']:current=repo/'comparator'/suite/name
            else:current=evidence/name
            require(sha(current)==digest,suite+' comparator input '+name)
        controls=importlib.import_module('test_'+suite+'_mutations').CASES
        result=json.loads((folder/'mutations/results.json').read_text())
        require(result['suite']==suite and result['status']=='passed' and result['inputs_unchanged'],suite+' mutation status')
        require(result['review_source_sha256']==comp['review_source_sha256'],suite+' mutation sources')
        require(result['baseline_receipt_sha256']==sha(folder/'compilation/results.json'),suite+' mutation baseline')
        require(result['tools_sha256']==comp['tools_sha256'],suite+' mutation tools')
        require([x['case'] for x in result['checks']]==[c[0] for c in controls],suite+' mutation inventory')
        for case,definition in zip(result['checks'],controls):
            name,module,old,new,last=definition
            raw=(repo/'checks'/(module+'.lean')).read_text()
            require(old is None or raw.count(old)==1,suite+' unique mutation '+name)
            changed=raw if old is None else raw.replace(old,new,1)
            require(case['passed'] and case['changed_module']==module and case['old']==old and case['new']==new,suite+' mutation case '+name)
            require(case['original_sha256']==comp['review_source_sha256'][module] and case['mutated_sha256']==hashlib.sha256(changed.encode()).hexdigest(),suite+' mutation bytes '+name)
            require(case['observed_failure_module']==(None if old is None else last),suite+' mutation rejection '+name)
            for item in case['modules']:
                require(sha(folder/'mutations'/name/(item['module']+'.log'))==item['log_sha256'],suite+' mutation log '+name)
            if old is None:require(all(x['exit_code']==0 and x['audit_passed'] for x in case['modules']),suite+' unchanged control')
            else:
                item=case['modules'][-1];output=(folder/'mutations'/name/(last+'.log')).read_text()
                require(item['exit_code']==1 and not item['audit_passed'] and 'error:' in output,suite+' compiler rejection '+name)
                require(not has_infrastructure_error(output),suite+' not infrastructure or resource failure '+name)
    require(len(set(theorems)|set(semantic_theorems)|set(flavor_theorems)|set(extra_theorems))==177,'177 distinct reviewed declarations')
    from test_flavor_mutations import CASES
    mutations=read('evidence/flavor-checks/mutations/results.json')
    require(mutations['status']=='passed' and mutations['inputs_unchanged'],'flavor mutation status')
    require(mutations['review_source_sha256']==fd['review_source_sha256'],'mutation baseline sources')
    require(mutations['baseline_receipt_sha256']==sha(flavor/'compilation/results.json'),'mutation baseline receipt')
    require(mutations['tools_sha256']==fd['tools_sha256'],'mutation compiler hashes')
    require([x['case'] for x in mutations['checks']]==[c[0] for c in CASES],'ten mutation controls')
    for result,case in zip(mutations['checks'],CASES):
        name,module,old,new,last=case
        raw=(repo/'checks'/(module+'.lean')).read_text()
        changed=raw if old is None else raw.replace(old,new,1)
        require(result['passed'] and result['changed_module']==module and result['old']==old and result['new']==new,'mutation case '+name)
        require(result['original_sha256']==fd['review_source_sha256'][module] and result['mutated_sha256']==hashlib.sha256(changed.encode()).hexdigest(),'mutation content '+name)
        observed=result['observed_failure_module']
        require(observed==(None if old is None else last),'expected rejection '+name)
        for item in result['modules']:
            log=flavor/'mutations'/name/(item['module']+'.log')
            require(sha(log)==item['log_sha256'],'mutation log '+name+'/'+item['module'])
        if old is None:require(all(x['exit_code']==0 and x['audit_passed'] for x in result['modules']),'unchanged mutation control')
        else:
            item=result['modules'][-1];output=(flavor/'mutations'/name/(last+'.log')).read_text()
            require(item['exit_code']==1 and not item['audit_passed'] and 'error:' in output,'compiler rejection '+name)
            require(not has_infrastructure_error(output),'not infrastructure or resource failure '+name)
    scope=read('evidence/flavor-checks/source-scope.json')
    require(scope['conclusions']==dict(actual_existence_flavors=6,generic_one_loop_positive_through=16,
        current_trajectory_estimate_flavors_at_most=8,two_loop_path_proved=False,banks_zaks_qft_constructed=False,
        full_free_qcd_benchmark_constructed=False),'physical scope limits')
    with tarfile.open(archive) as t:
        for item in scope['files']:
            rel='proof/'+item['path'];require(archive_hashes[rel]==item['sha256'],'source excerpt file '+rel)
            source_lines=t.extractfile('massive-qcd-lean/'+rel).read().decode().splitlines(keepends=True)
            for e in item['excerpts']:require(''.join(source_lines[e['start']-1:e['end']])==e['text'],'source excerpt text '+rel)
    graph=read('evidence/flavor-checks/dependency-paths/result.json')
    require(graph['status']=='passed' and graph['exit_code']==0 and graph['inputs_unchanged'],'dependency inspection status')
    require(graph['program_sha256']==sha(repo/'audit/DependencyPaths.lean'),'dependency inspection program')
    require(graph['tools_sha256']==fd['tools_sha256'],'dependency inspection compiler')
    log=repo/'evidence/flavor-checks/dependency-paths/inspection.log'
    require(graph['log_sha256']==sha(log),'dependency inspection log')
    payloads=[x.split('DEPENDENCY_JSON ',1)[1] for x in log.read_text().splitlines() if 'DEPENDENCY_JSON ' in x]
    require(len(payloads)==1 and json.loads(payloads[0])==graph['inspection'],'dependency inspection payload')
    require(graph['inspection']['root']=='YM.Massive.interacting_six','dependency root')
    targets={x['target']:x for x in graph['inspection']['targets']}
    for target in ['YM.QCD.Acre.Stratum.MarchQ.Earlier','YM.QCD.Acre.Stratum.MarchQ.Track.slope_all','YM.QCD.Acre.Stratum.MarchQ.Track.perimeter','YM.QCD.Pearl.docket','YM.QCD.Raft.calibrated','YM.QCD.Acre.Stratum.MarchQ.Track.Survey.sum_toll']:
        item=targets[target]
        require(item['present_in_environment'] and item['in_restricted_dependency_closure'] and item['path'][0]==graph['inspection']['root'] and item['path'][-1]==target,'dependency path '+target)
    coverage=read('evidence/flavor-checks/coverage.json')
    require(coverage['new_audited_declarations']==136 and coverage['total_distinct_review_declarations']==177,'running coverage counts')
    require(coverage['new_comparator_targets']==27 and coverage['new_mutation_controls']==26,'running validation counts')
    require(coverage['reference_ode_global_existence_proved'] and not any(coverage[k] for k in ['actual_continuum_two_loop_proved','banks_zaks_qft_constructed','source_massless_limit_proved','full_free_qcd_comparison_constructed']),'reference/physical distinction')
    require(len(coverage['areas'])==7 and all(x['open'] for x in coverage['areas']),'remaining physical obligations')
    index=read('evidence/flavor-checks/target-index.json')['targets']
    expected_targets=[]
    for suite in ['flavor','sensitivity','body','robustness','normalization']:
        inventory=importlib.import_module(suite+'_suite')
        expected_targets.extend((suite,inventory.PREFIX+name) for name in inventory.TARGETS)
    require([(x['suite'],x['theorem']) for x in index]==expected_targets,'classified target inventory')
    for item in index:
        suite=item['suite'];name=item['theorem'].removeprefix(PREFIX)
        inventory=importlib.import_module(suite+'_suite')
        require(item['classification'] in ['submitted_source','conditional_submitted_source','perturbative_reference','scalar_control'],'target classification '+name)
        require(item['challenge']=='comparator/'+suite+'/'+suite.title()+'Challenge.lean','target challenge location '+name)
        modules=[m for m,names in inventory.AUDITS.items() if name in names]
        require(len(modules)==1 and item['proof']=='checks/'+modules[0]+'.lean','target proof location '+name)
        challenge=(repo/item['challenge']).read_text()
        require('theorem '+name+' : '+item['proposition']+' := by sorry' in challenge,'target proposition '+name)
        definitions=[p for p in (repo/'checks').glob('*Spec.lean') if re.search(r'\bdef '+re.escape(item['proposition'])+r'\b',p.read_text())]
        require(len(definitions)==1 and item['specification']==definitions[0].relative_to(repo).as_posix(),'target specification location '+name)
        require(bool(item['scope']),'target scope note '+name)
    from record_flavor_scope import benchmark_rows
    rows=read('evidence/flavor-checks/flavor-benchmarks.json')['rows']
    require(rows==benchmark_rows(),'flavor reference values')
    for row in rows:
        bracket=row['a_star_three_loop_bracket']
        if bracket is None:continue
        lo,hi=Fraction(bracket['lower']),Fraction(bracket['upper'])
        b0,b1,b2=[Fraction(row[k]) for k in ['B0','B1','B2_MSbar']]
        require(0<lo<hi and hi-lo<=Fraction(1,10**16),'narrow positive three-loop interval')
        require(b0+b1*lo+b2*lo*lo>0 and b0+b1*hi+b2*hi*hi<=0,'three-loop endpoint signs')
        if row['flavors']==6:require(1<lo<hi<2,'six-flavor bracket agrees with Lean bound')
        if row['flavors']==16:require(Fraction(1,318)<lo<hi<Fraction(1,316),'sixteen-flavor bracket agrees with Lean bound')
    from verify_mass_current_evidence import verify as verify_mass_current
    new_count=verify_mass_current(repo,archive,archive_hashes)
    manifest_count=check_manifest(repo)
    print(f'PASS: archive, frozen inputs, eight Comparator runs with both kernels, 177 earlier + {new_count} new Lean-only theorem audits, 125 earlier + 3 new diagnostic/control checks, authenticated source excerpts, explicit physical limits, and {manifest_count} manifest files.')
if __name__=='__main__':main()
