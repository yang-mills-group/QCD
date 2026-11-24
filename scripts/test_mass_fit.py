#!/usr/bin/env python3
"""Exact rational checks of the submitted all-ordered-pairs mass scheme.
Independent calculation, not execution of Lean's real-number definitions.
"""
from fractions import Fraction as Q
import argparse, json
from pathlib import Path

N=6
PAIRS=[(i,j) for i in range(N) for j in range(N) if i!=j]
def fit(b):
    total=sum(b[i][j] for i,j in PAIRS)
    return [sum(b[i][j]+b[j][i] for j in range(N) if i!=j)/8-total/40 for i in range(N)]
def loss(b,u): return sum((b[i][j]-u[i]-u[j])**2 for i,j in PAIRS)
def six_pair(b):
    first=(b[0][1]+b[0][2]-b[1][2])/2
    return [first]+[b[0][i]-first for i in range(1,N)]
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    checks=[]
    def check(name,condition,**detail):
        checks.append(dict(name=name,passed=bool(condition),**detail))
        if not condition: raise AssertionError(name)
    design=[[Q(int(k==i)+int(k==j)) for k in range(N)] for i,j in PAIRS]
    gram=[[sum(row[i]*row[j] for row in design) for j in range(N)] for i in range(N)]
    check('ordered_pair_gram_8I_plus_2J',all(gram[i][j]==(10 if i==j else 2) for i in range(N) for j in range(N)))
    # Verify the normal equations on every basis vector of all 36 readings,
    # including arbitrary diagonals and asymmetric off-diagonal readings.
    for k in range(N*N):
        b=[[Q(int(i*N+j==k)) for j in range(N)] for i in range(N)]
        u=fit(b)
        check('normal_equations_basis_%02d'%k,all(sum(gram[i][j]*u[j] for j in range(N))==sum(b[i][j]+b[j][i] for j in range(N) if i!=j) for i in range(N)))
    # l-infinity -> l-infinity norm of the fit and difference maps.
    coeff=[]
    for i,j in PAIRS:
        b=[[Q(0) for _ in range(N)] for _ in range(N)];b[i][j]=1
        coeff.append(fit(b))
    check('individual_error_bound_3delta_over_2',all(sum(abs(row[i]) for row in coeff)==Q(3,2) for i in range(N)))
    check('pair_difference_error_bound_2delta',all(sum(abs(row[i]-row[j]) for row in coeff)==2 for i,j in PAIRS))
    r=list(map(Q,range(1,7)));d=Q(1,1000)
    b=[[r[i]+r[j]+(d if {i,j}=={4,5} else 0) for j in range(N)] for i in range(N)]
    u=fit(b)
    check('six_pair_prescription_returns_reference',six_pair(b)==r)
    check('all_pair_prescription_differs',u==[r[i]+(-d/20 if i<4 else d/5) for i in range(N)])
    check('all_pair_loss_strictly_smaller',loss(b,u)==Q(6,5)*d*d and loss(b,r)==2*d*d and loss(b,u)<loss(b,r),fitted=list(map(str,u)),fitted_loss=str(loss(b,u)),six_pair_loss=str(loss(b,r)))
    # Deliberately wrong row divisor: the normal-equation residual catches it.
    bad=[sum(b[i][j]+b[j][i] for j in range(N) if i!=j)/10-sum(b[i][j] for i,j in PAIRS)/40 for i in range(N)]
    check('wrong_divisor_mutation_detected',any(sum(gram[i][j]*bad[j] for j in range(N))!=sum(b[i][j]+b[j][i] for j in range(N) if i!=j) for i in range(N)))
    check('read_margin_implies_positive_and_separated',1-Q(3,2)/100>0 and 1-Q(2)/100>0,minimum_mass_margin=str(1-Q(3,2)/100),minimum_separation_margin=str(1-Q(2)/100))
    result={'status':'passed','arithmetic':'exact fractions','scope':'Independent model of supplied Signals.loss; synthetic b is not asserted to arise from the constructed theory','checks':checks}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'{len(checks)} exact rational checks passed')
if __name__=='__main__':main()
