#!/usr/bin/env python3
"""Parameterized replay of the recorded QCD macOS verification workflow.

Requires the exact recorded tools; this wrapper has not been run end to end.
The original completed runner is preserved verbatim in evidence/supplied-target.
Run the supplied QCD verification stages on macOS with upstream fake-landrun.

The package remains unchanged. Linux Landlock/systemd isolation is absent by
explicit user choice. Statement matching, axiom checking, both kernel checks,
and the published independent challenge export digest remain required.
"""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package', type=Path, required=True)
parser.add_argument('--tools', type=Path, required=True)
parser.add_argument('--run', type=Path, required=True)
args = parser.parse_args()
ROOT = args.run.resolve()
BUNDLE = args.package.resolve()
ROOT.mkdir(parents=True, exist_ok=False)
(ROOT / 'evidence').mkdir()
PROJECT = ROOT / 'project'
EVIDENCE = ROOT / 'evidence'
TOOLS = args.tools.resolve()
LEAN = (TOOLS / 'lean').resolve()
EXPECTED_EXPORT = '32f8e0d3322520e251c27a96c7123aab2d695f68bb15fa60190e460cbe063dba'
EXPORT_TARGETS = ('Nat String String.mk Char Char.ofNat List Quot Quot.mk Quot.lift Quot.ind '
                  'YM.Massive.interacting_six propext Classical.choice Quot.sound '
                  'Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble '
                  'Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList').split()
ENV = {key: os.environ[key] for key in ('HOME', 'TMPDIR') if key in os.environ}
ENV.update(PATH=f'{LEAN}/bin:{TOOLS}/bin:/opt/homebrew/bin:/usr/bin:/bin',
           LANG='en_US.UTF-8', GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL='/dev/null',
           GIT_TERMINAL_PROMPT='0', LEAN_NUM_THREADS='8', LEAN_ABORT_ON_PANIC='1',
           XDG_CACHE_HOME=str(ROOT / 'cache'), MATHLIB_CACHE_DIR=str(ROOT / 'cache/mathlib'),
           COMPARATOR_LANDRUN=str(TOOLS / 'bin/landrun-mac'),
           COMPARATOR_LEAN4EXPORT=str(TOOLS / 'bin/lean4export'),
           COMPARATOR_NANODA=str(TOOLS / 'bin/nanoda_bin'))
STATE = {'status': 'running', 'stage': 'initializing', 'pid': os.getpid(),
         'mode': 'macOS; upstream fake-landrun; Linux Landlock/systemd isolation absent',
         'theorem': 'YM.Massive.interacting_six', 'kernel_checks_required': ['Nanoda', 'Lean'],
         'completed_stages': []}


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, data):
    tmp = path.with_name(path.name + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(path)


def status(stage, **fields):
    STATE.update(stage=stage, updated_utc=now(), **fields)
    save(ROOT / 'status.json', STATE)
    print(f'{now()} {stage}', flush=True)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def run(stage, command, cwd=PROJECT):
    log = EVIDENCE / f'{stage}.log'
    status(stage, active_log=str(log), command=[str(x) for x in command])
    started = time.monotonic()
    with log.open('w') as stream:
        proc = subprocess.Popen([str(x) for x in command], cwd=cwd, env=ENV,
                                stdout=stream, stderr=subprocess.STDOUT)
        STATE['child_pid'] = proc.pid
        save(ROOT / 'status.json', STATE)
        code = proc.wait()
    receipt = {'command': [str(x) for x in command], 'cwd': str(cwd), 'exit_code': code,
               'elapsed_seconds': round(time.monotonic() - started, 2),
               'finished_utc': now(), 'log_sha256': sha(log)}
    save(EVIDENCE / f'{stage}.json', receipt)
    STATE.pop('child_pid', None)
    if code:
        raise RuntimeError(f'{stage} exited {code}; see {log}')
    STATE['completed_stages'].append(stage)
    return log


def snapshot():
    result = {}
    for parent, dirs, files in os.walk(PROJECT):
        dirs[:] = [d for d in dirs if d != '.lake']
        for name in files:
            path = Path(parent) / name
            if path.is_symlink():
                raise RuntimeError(f'Unexpected source link: {path}')
            result[str(path.relative_to(PROJECT))] = sha(path)
    return result


def export_reference(stage):
    command = [LEAN / 'bin/lake', 'env', TOOLS / 'bin/lean4export', 'Challenge', '--'] + EXPORT_TARGETS
    log = EVIDENCE / f'{stage}.log'
    status(stage, active_log=str(log), command=[str(x) for x in command])
    h, size = hashlib.sha256(), 0
    with log.open('w') as stream:
        proc = subprocess.Popen([str(x) for x in command], cwd=PROJECT, env=ENV,
                                stdout=subprocess.PIPE, stderr=stream)
        STATE['child_pid'] = proc.pid
        save(ROOT / 'status.json', STATE)
        for block in iter(lambda: proc.stdout.read(1024 * 1024), b''):
            h.update(block)
            size += len(block)
        code = proc.wait()
    STATE.pop('child_pid', None)
    receipt = {'exit_code': code, 'sha256': h.hexdigest(), 'expected_sha256': EXPECTED_EXPORT,
               'bytes': size, 'matches_published_digest': h.hexdigest() == EXPECTED_EXPORT,
               'finished_utc': now()}
    save(EVIDENCE / f'{stage}.json', receipt)
    if code or h.hexdigest() != EXPECTED_EXPORT:
        raise RuntimeError(f'{stage}: independent challenge export did not match; see {stage}.json')
    STATE['completed_stages'].append(stage)


def controls():
    cases = {
        'accept': 'theorem qcdSmoke : 1 + 1 = 2 := by rfl\n',
        'statement_mismatch': 'theorem qcdSmoke : 2 + 2 = 4 := by rfl\n',
        'forbidden_axiom': 'axiom forbidden : 1 + 1 = 2\ntheorem qcdSmoke : 1 + 1 = 2 := forbidden\n',
    }
    receipts = []
    status('comparator-controls')
    for name, solution in cases.items():
        project = ROOT / 'controls' / name
        project.mkdir(parents=True)
        (project / 'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
        (project / 'lakefile.toml').write_text('name = "qcd_mac_control"\nversion = "0.1.0"\n'
                                             '[[lean_lib]]\nname = "Challenge"\n'
                                             '[[lean_lib]]\nname = "Solution"\n')
        (project / 'Challenge.lean').write_text('theorem qcdSmoke : 1 + 1 = 2 := by sorry\n')
        (project / 'Solution.lean').write_text(solution)
        save(project / 'comparator.json', {
            'challenge_module': 'Challenge', 'solution_module': 'Solution',
            'theorem_names': ['qcdSmoke'],
            'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'enable_nanoda': True})
        command = [str(LEAN / 'bin/lake'), 'env', str(TOOLS / 'bin/comparator'), 'comparator.json']
        proc = subprocess.run(command, cwd=project, env=ENV, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, timeout=180)
        (project / 'run.log').write_text(proc.stdout)
        if name == 'accept':
            passed = proc.returncode == 0 and all(marker in proc.stdout for marker in (
                'Nanoda kernel accepts the solution', 'Lean default kernel accepts the solution',
                'Your solution is okay!'))
        elif name == 'statement_mismatch':
            passed = proc.returncode != 0 and 'theorem statement do not match' in proc.stdout
        else:
            passed = proc.returncode != 0 and "Illegal axiom detected: 'forbidden'" in proc.stdout
        receipts.append({'case': name, 'exit_code': proc.returncode, 'expected_behavior_observed': passed,
                         'log_sha256': sha(project / 'run.log')})
        save(EVIDENCE / 'controls.json', receipts)
        if not passed:
            raise RuntimeError(f'Comparator control failed: {name}; see {project / "run.log"}')
    STATE['completed_stages'].append('comparator-controls')


def main():
    if (ROOT / 'status.json').exists():
        raise RuntimeError('This runner requires a fresh run; inspect existing status before resuming.')
    STATE['started_utc'] = now()
    status('preflight')
    free = shutil.disk_usage(ROOT).free
    if free < 200 * 1024 ** 3:
        raise RuntimeError(f'Expected at least 200 GiB free before build, have {free / 1024 ** 3:.1f}')
    version = subprocess.check_output([str(LEAN / 'bin/lean'), '--githash'], text=True).strip()
    if version != '8c9756b28d64dab099da31a4c09229a9e6a2ef35':
        raise RuntimeError('Wrong Lean toolchain commit')
    expected_tools = json.loads((Path(__file__).resolve().parents[1] /
        'evidence/supplied-target/tool-hashes.json').read_text())
    for old_path, digest in expected_tools.items():
        name = Path(old_path).name
        file = LEAN / 'bin' / name if name in ('lean', 'lake') else TOOLS / 'bin' / name
        if sha(file) != digest:
            raise RuntimeError('Tool differs from recorded macOS binary: ' + name)
    run('inputs', [sys.executable, '-I', '-B', BUNDLE / 'comparator/check-inputs',
                  '--prepare-reference', PROJECT], cwd=ROOT)
    run('dependencies', [sys.executable, '-I', '-B', BUNDLE / 'comparator/prepare-dependencies'])
    lock = json.loads((PROJECT / 'lake-manifest.json').read_text())
    for package in lock['packages']:
        p = PROJECT / '.lake/packages' / package['name']
        head = subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(p), 'status', '--porcelain',
                                         '--untracked-files=no'], text=True).strip()
        if head != package['rev'] or dirty:
            raise RuntimeError(f'Dependency pin/cleanliness failure: {package["name"]}')
    save(EVIDENCE / 'run-environment.json', {'environment_overrides': ENV, 'free_bytes_at_start': free,
                                          'platform': sys.platform, 'package': str(BUNDLE)})
    tool_files = list((TOOLS / 'bin').iterdir()) + [LEAN / 'bin/lean', LEAN / 'bin/lake']
    tool_hashes = {str(p): sha(p) for p in tool_files}
    save(EVIDENCE / 'tool-hashes.json', tool_hashes)
    controls()
    reference_sources = snapshot()
    save(EVIDENCE / 'reference-source-hashes.json', reference_sources)
    run('mathlib-cache', [LEAN / 'bin/lake', 'exe', 'cache', '--cache-from=master',
                         '--repo=leanprover-community/mathlib4', 'get'])
    if (PROJECT / '.lake/build/lib/lean/YM').exists() or (PROJECT / 'Solution.lean').exists():
        raise RuntimeError('Unexpected submission artifacts before independent reference build')
    run('reference-build', [LEAN / 'bin/lake', 'build', 'Challenge'])
    if snapshot() != reference_sources:
        raise RuntimeError('Reference source changed during preparation/build')
    export_reference('reference-export')
    run('add-solution', [sys.executable, '-I', '-B', BUNDLE / 'comparator/check-inputs',
                         '--add-solution', PROJECT])
    for rel in ('YM/Plata/Massive.olean', 'Solution.olean'):
        if (PROJECT / '.lake/build/lib/lean' / rel).exists():
            raise RuntimeError(f'Unexpected previously built submission: {rel}')
    staged_sources = snapshot()
    save(EVIDENCE / 'staged-source-hashes.json', staged_sources)
    export_reference('staged-reference-export')
    log = run('comparator', [LEAN / 'bin/lake', 'env', TOOLS / 'bin/comparator', 'comparator.json'])
    output = log.read_text()
    for marker in ('Nanoda kernel accepts the solution', 'Lean default kernel accepts the solution',
                   'Your solution is okay!'):
        if marker not in output.splitlines():
            raise RuntimeError(f'Comparator success marker missing: {marker}')
    if snapshot() != staged_sources:
        raise RuntimeError('Staged sources changed during verification')
    if any(sha(Path(p)) != expected for p, expected in tool_hashes.items()):
        raise RuntimeError('Verification tool binary changed during run')
    run('final-input-check', [sys.executable, '-I', '-B', BUNDLE / 'comparator/check-inputs'])
    status('complete', status='passed', finished_utc=now(), active_log=None, command=None)


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        status(STATE['stage'], status='failed', finished_utc=now(), error=str(error))
        raise
