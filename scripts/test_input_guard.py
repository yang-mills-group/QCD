#!/usr/bin/env python3
"""Mutation tests of the supplied input authenticator on isolated copies."""
import argparse, hashlib, json, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    repo=Path(__file__).resolve().parents[1]
    meta=json.loads((repo/'provenance/submission.json').read_text()); archive=repo/meta['source_archive']
    assert hashlib.sha256(archive.read_bytes()).hexdigest()==meta['source_archive_sha256']
    results=[]
    with tempfile.TemporaryDirectory(prefix='qcd-input-') as tmp:
        root=Path(tmp)
        with tarfile.open(archive) as t:
            # Our archived source has only regular files and directories.
            for m in t.getmembers():
                if not (m.isfile() or m.isdir()) or m.name.startswith('/') or '..' in Path(m.name).parts:raise ValueError('Unsafe archive entry')
            t.extractall(root)
        bundle=root/'massive-qcd-lean'; checker=bundle/'comparator/check-inputs'
        def run(name,extra=(),expect=None):
            p=subprocess.run([sys.executable,'-I','-B',str(checker),*map(str,extra)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            ok=p.returncode==0 if expect is None else p.returncode!=0 and expect in p.stdout
            results.append(dict(name=name,passed=ok,exit_code=p.returncode,output=p.stdout))
            if not ok:raise AssertionError(name+': '+p.stdout)
        run('authentic_package')
        for name,rel in [('proof_byte','proof/YM/Plata/Massive.lean'),('reference_byte','comparator/frozen/reference/YM/Massive/Target/Statement.lean'),('manifest_byte','comparator/submission-inputs.sha256'),('solution_byte','comparator/Solution.lean')]:
            path=bundle/rel;data=path.read_bytes();path.write_bytes(data+b'\n')
            run(name,expect='Wrong SHA-256');path.write_bytes(data)
        extra=bundle/'proof/Unexpected.lean';extra.write_text('-- added file\n');run('extra_source',expect='Unexpected file inventory');extra.unlink()
        path=bundle/'proof/YM/Plata/Massive.lean';data=path.read_bytes();target=root/'linked.lean';target.write_bytes(data);path.unlink();path.symlink_to(target)
        run('symlink_source',expect='Expected a regular file');path.unlink();path.write_bytes(data)
        stage=root/'stage';run('prepare_reference',['--prepare-reference',stage])
        path=stage/'YM/Massive/Target/Statement.lean';path.write_bytes(path.read_bytes()+b'\n')
        run('changed_staged_reference',['--add-solution',stage],expect='Wrong SHA-256')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(dict(status='passed',checks=results),indent=2)+'\n')
    print(f'{len(results)} input-guard checks passed')
if __name__=='__main__':main()
