"""Validate the separately counted November 23 Lean-only supplement."""
import hashlib
import json
import re
import tarfile
from mass_current_suite import AUDITS, MODULES, PREFIX
from test_mass_current_mutations import CASES
from test_flavor_mutations import has_infrastructure_error


def verify(repo, archive, archive_hashes):
    from verify_evidence import check_axiom_log
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def need(ok, label):
        if not ok:
            raise SystemExit('FAIL: mass/current '+label)

    folder = repo/'evidence/mass-current-checks'
    comp = json.loads((folder/'compilation/results.json').read_text())
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    need(comp['status'] == 'passed' and comp['inputs_unchanged'], 'compilation status')
    need(comp['suite'] == 'mass-current', 'suite')
    need([x['module'] for x in comp['results']] == MODULES, 'module inventory')
    need(comp['source_files_verified'] == len(json.loads(
        (repo/'evidence/supplied-target/staged-source-hashes.json').read_text())), 'source inventory')
    baseline = json.loads((repo/'evidence/normalization-checks/compilation/results.json').read_text())
    need(comp['tools_sha256'] == baseline['tools_sha256'], 'recorded compiler')
    count = 0
    for item in comp['results']:
        module = item['module']
        log = folder/'compilation'/(module+'.log')
        output = log.read_text()
        observed = {name: re.findall(r'[\w.]+', contents) for name, contents in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
        need(item['status'] == 'passed' and item['exit_code'] == 0, 'module '+module)
        need(sha(repo/'checks'/(module+'.lean')) == item['source_sha256'] ==
             comp['review_source_sha256'][module], 'source '+module)
        need(sha(log) == item['log_sha256'], 'log '+module)
        check_axiom_log(log, item['axioms'])
        need(observed == item['axioms'] and set(observed) == {PREFIX+n for n in AUDITS[module]},
             'axiom inventory '+module)
        need(all(set(v) <= allowed for v in observed.values()) and
             "declaration uses 'sorry'" not in output, 'axiom policy '+module)
        count += len(observed)
    need(count == 10, 'ten new declarations')
    mut = json.loads((folder/'mutations/results.json').read_text())
    need(mut['status'] == 'passed' and mut['inputs_unchanged'], 'control status')
    need(mut['review_source_sha256'] == comp['review_source_sha256'] and
         mut['tools_sha256'] == comp['tools_sha256'], 'control baseline')
    need(mut['baseline_receipt_sha256'] == sha(folder/'compilation/results.json'), 'baseline receipt')
    need([x['case'] for x in mut['checks']] == [x[0] for x in CASES], 'control inventory')
    for case, definition in zip(mut['checks'], CASES):
        name, module, old, new, last = definition
        raw = (repo/'checks'/(module+'.lean')).read_text()
        need(old is None or raw.count(old) == 1, 'unique mutation '+name)
        changed = raw if old is None else raw.replace(old, new, 1)
        need(case['passed'] and case['changed_module'] == module and
             case['old'] == old and case['new'] == new, 'control '+name)
        need(case['original_sha256'] == comp['review_source_sha256'][module] and
             case['mutated_sha256'] == hashlib.sha256(changed.encode()).hexdigest(), 'mutation '+name)
        need(case['observed_failure_module'] == (None if old is None else last), 'failure module '+name)
        for item in case['modules']:
            log = folder/'mutations'/name/(item['module']+'.log')
            need(sha(log) == item['log_sha256'], 'control log '+name)
        if old is None:
            need(all(x['exit_code'] == 0 and x['audit_passed'] for x in case['modules']), 'unchanged control')
        else:
            output = (folder/'mutations'/name/(last+'.log')).read_text()
            need(case['modules'][-1]['exit_code'] == 1 and 'error:' in output and
                 not has_infrastructure_error(output), 'intended compiler rejection '+name)
    scope = json.loads((folder/'source-audit.json').read_text())
    need(scope['conclusions'] == {
        'finite_vector_contact_proved': True,
        'finite_axial_contact_with_remainder_proved': True,
        'continuum_contact_normalization_verified': False,
        'conventional_mass_scheme_conversion_verified': False,
        'counterexample_to_full_goal_constructed': False,
    }, 'physical scope')
    with tarfile.open(archive) as source:
        for item in scope['files']:
            rel = 'proof/'+item['path']
            need(archive_hashes[rel] == item['sha256'], 'archived source '+rel)
            lines = source.extractfile('massive-qcd-lean/'+rel).read().decode().splitlines(keepends=True)
            for excerpt in item['excerpts']:
                need(''.join(lines[excerpt['start']-1:excerpt['end']]) == excerpt['text'], 'excerpt '+rel)
    return count
