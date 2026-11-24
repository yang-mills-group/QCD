#!/usr/bin/env python3
"""Record bounded source inspection and exact perturbative reference values."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import re

SELECTIONS = {
    'YM/QCD/Matter.lean': [(3,10),(134,170)],
    'YM/QCD/Raft/Roads.lean': [(3,5),(28,45)],
    'YM/QCD/Pearl/Survey.lean': [(3,12),(19,23)],
    'YM/QCD/Pearl/Usage.lean': [(57,59),(79,85)],
    'YM/QCD/Flume/Bow.lean': [(19,31)],
    'YM/QCD/Page/Steppes.lean': [(49,66)],
    'YM/Massive/Stratum/Burg.lean': [(20,23),(53,69)],
    'YM/Massive/Target/Tower.lean': [(3,23),(87,106),(130,152),(183,211)],
    'YM/Massive/Finite/Core.lean': [(27,47),(69,89)],
    'YM/Massive/Reference/Scaling.lean': [(77,109)],
    'YM/Massive/Stratum/Velour.lean': [(81,105)],
    'YM/VStages/Revolves.lean': [(25,31),(74,137)],
    'YM/VStages/Settlement.lean': [(15,26),(34,35),(53,69),(76,109)],
    'YM/Parishes/Caves.lean': [(130,134)],
    'YM/Massive/Target/Statement.lean': [(10,58)],
}
PATTERN = r'banks.?zaks|two[- ]loops?|2[- ]loops?|second[- ]loop'

def three_loop_bracket(b0,b1,b2):
    """Exact rational sign bracket for the positive reference root when b0>0>b2.

    This is a diagnostic calculation, not another kernel-checked theorem.
    """
    if not (b0>0 and b2<0):return None
    def value(a):return b0+b1*a+b2*a*a
    lo,hi=Q(0),Q(1)
    while value(hi)>=0:hi*=2
    for _ in range(60):
        middle=(lo+hi)/2
        if value(middle)>0:lo=middle
        else:hi=middle
    assert value(lo)>0 and value(hi)<=0
    return lo,hi

def benchmark_rows():
    rows=[]
    for f in range(18):
        b0=Q(11)-Q(2*f,3); b1=Q(102)-Q(38*f,3)
        b2=Q(2857,2)-Q(5033*f,18)+Q(325*f*f,54)
        bz = b0>0 and b1<0
        root = -b0/b1 if bz else None
        bracket=three_loop_bracket(b0,b1,b2)
        midpoint=(bracket[0]+bracket[1])/2 if bracket else None
        rows.append(dict(flavors=f,B0=str(b0),B1=str(b1),B2_MSbar=str(b2),
            asymptotically_free_one_loop=b0>0,current_trajectory_budget=f<=8,
            positive_two_loop_bz_zero=bz,a_star=str(root) if root is not None else None,
            alpha_star_illustrative=4*math.pi*float(root) if root is not None else None,
            derivative_at_root=str(-2*root*root*b1) if root is not None else None,
            a_star_three_loop_bracket=dict(lower=str(bracket[0]),upper=str(bracket[1])) if bracket else None,
            alpha_three_loop_illustrative=4*math.pi*float(midpoint) if midpoint is not None else None,
            relative_root_shift_percent_illustrative=100*float(midpoint/root-1) if midpoint is not None and root is not None else None))
    return rows

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--built-source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();repo=Path(__file__).resolve().parents[1]
    source=a.built_source.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    snapshot=json.loads((repo/'evidence/supplied-target/staged-source-hashes.json').read_text())
    files=[]
    for rel,ranges in SELECTIONS.items():
        raw=(source/rel).read_bytes();digest=hashlib.sha256(raw).hexdigest()
        if snapshot[rel]!=digest:raise SystemExit('Source mismatch: '+rel)
        lines=raw.decode().splitlines(keepends=True)
        files.append(dict(path=rel,sha256=digest,excerpts=[dict(start=s,end=e,text=''.join(lines[s-1:e])) for s,e in ranges]))
    matches=[];n=0
    for rel,digest in sorted(snapshot.items()):
        if not rel.startswith('YM/') or not rel.endswith('.lean'):continue
        raw=(source/rel).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest:raise SystemExit('Source mismatch: '+rel)
        n+=1
        for i,line in enumerate(raw.decode().splitlines(),1):
            if re.search(PATTERN,line,re.I):matches.append(dict(path=rel,line=i,text=line))
    record=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),files=files,
        bounded_search=dict(pattern=PATTERN,scope='Authenticated YM/*.lean files, recursively',files_searched=n,matches=matches,
            interpretation='Text search is not a proof of mathematical absence. The sole matched second loopBound phrase names unrelated variables.'),
        conclusions=dict(actual_existence_flavors=6,generic_one_loop_positive_through=16,
            current_trajectory_estimate_flavors_at_most=8,two_loop_path_proved=False,
            banks_zaks_qft_constructed=False,full_free_qcd_benchmark_constructed=False))
    (out/'source-scope.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
    table=dict(scope='Specified perturbative benchmarks; not measurements/extractions of the submitted continuum theory',
        three_loop_intervals='Exact rational sign brackets computed in Python; illustrative decimals use their midpoints. These are not additional Lean theorem audits.',
        convention='a=g^2/(16*pi^2), d a/d log(mu)=-2*a^2*(B0+B1*a+B2*a^2+...)',
        source='https://arxiv.org/pdf/hep-ph/9302208, equations (1) and (10); factor two converts log(mu^2) to log(mu)',
        rows=benchmark_rows())
    (out/'flavor-benchmarks.json').write_text(json.dumps(table,indent=2)+'\n')
    print(f'Recorded {len(files)} source excerpts, searched {n} files, and tabulated 18 flavor counts.')

if __name__=='__main__':main()
