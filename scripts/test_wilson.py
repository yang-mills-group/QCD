#!/usr/bin/env python3
"""Independent finite Wilson-operator diagnostic, using Python complex numbers.
Maps explicitly to Gamma.lean and Stencil.lean; does not execute Lean definitions.
No continuum, positivity-of-measure, or renormalization claim follows from this test.
"""
import argparse, cmath, hashlib, itertools, json, math
from pathlib import Path

def eye(n):return [[complex(i==j) for j in range(n)] for i in range(n)]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def adj(a):return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a[0]))]
def kron(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(c,a):return [c*x for x in a]
def err(a,b):return max(abs(x-y) for x,y in zip(a,b))
def flat(a):return [x for row in a for x in row]
sx=[[0,1],[1,0]];sy=[[0,-1j],[1j,0]];sz=[[1,0],[0,-1]]
G=[kron(sx,eye(2)),kron(sy,sx),kron(sy,sy),kron(sy,sz)];G5=kron(sz,eye(2))
def spin(g,v):return [sum(g[s][t]*v[t*3+c] for t in range(4)) for s in range(4) for c in range(3)]
def colour(g,v):return [sum(g[c][d]*v[s*3+d] for d in range(3)) for s in range(4) for c in range(3)]
# Noncommuting, unitary determinant-one matrices, exactly representable.
P=[[0,1,0],[0,0,1],[1,0,0]];Z=[[1,0,0],[0,-1,0],[0,0,-1]]
GROUP=[eye(3),P,mm(P,P),Z,mm(P,Z),mm(Z,P)]
def shift_site(x,a,h,n):y=list(x);y[a]=(y[a]+h)%n;return tuple(y)
def shifted(v,links,a,n,back=False,wrong_seam=False):
    out={}
    for x in v:
        y=shift_site(x,a,-1 if back else 1,n)
        base=y if back else x
        sign=1 if wrong_seam or base[a]!=n-1 else -1
        u=adj(links[base,a]) if back else links[x,a]
        out[x]=scale(sign,colour(u,v[y]))
    return out

def D(v,links,n,m,swap=False,wrong_seam=False):
    out={x:scale(m,z) for x,z in v.items()}
    for a in range(4):
        f=shifted(v,links,a,n,wrong_seam=wrong_seam);b=shifted(v,links,a,n,True,wrong_seam)
        for x in v:
            # m + sum [1 - (1-gamma)S/2 - (1+gamma)S*/2].
            diff=add(f[x],scale(-1,b[x]));hop=add(scale(.5,add(f[x],b[x])),scale(.5 if swap else -.5,spin(G[a],diff)))
            out[x]=add(out[x],add(v[x],scale(-1,hop)))
    return out

def W(v,links,n):
    out={x:[0j]*12 for x in v}
    for a in range(4):
        f=shifted(v,links,a,n);b=shifted(v,links,a,n,True)
        for x in v:out[x]=add(out[x],add(v[x],scale(-.5,add(f[x],b[x]))))
    return out

def spinfield(g,v):return {x:spin(g,z) for x,z in v.items()}
def field_error(a,b):return max(err(a[x],b[x]) for x in a)
def inner(v,w):return sum(a.conjugate()*b for x in v for a,b in zip(v[x],w[x]))
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    checks=[]
    def check(name,residual,tolerance=1e-10,mutation=False):
        ok=residual>1e-4 if mutation else residual<tolerance
        checks.append(dict(name=name,passed=ok,residual=residual,tolerance=tolerance,mutation=mutation))
        if not ok:raise AssertionError(name+': '+str(residual))
    for i in range(4):
        check('gamma_hermitian_'+str(i),err(flat(adj(G[i])),flat(G[i])))
        for j in range(4):check(f'clifford_{i}_{j}',err(add(flat(mm(G[i],G[j])),flat(mm(G[j],G[i]))),scale(2 if i==j else 0,flat(eye(4)))))
    product=eye(4)
    for g in G:product=mm(product,g)
    check('chirality_orientation',err(flat(G5),scale(-1,flat(product))))
    for n in [2,4]:
        sites=list(itertools.product(range(n),repeat=4));links={(x,d):eye(3) for x in sites for d in range(4)}
        for k in [(0,0,0,0),(0,1,0,1)]:
            pvec=[(2*q+1)*math.pi/n for q in k]
            base=[complex((i%5)-2,(i%3)-1)/7 for i in range(12)]
            v={x:scale(cmath.exp(1j*sum(t*q for t,q in zip(x,pvec))),base) for x in sites}
            for mass in [.1,1.7]:
                scalar=mass+sum(1-math.cos(q) for q in pvec)
                symbol=scale(scalar,base)
                for d in range(4):symbol=add(symbol,scale(1j*math.sin(pvec[d]),spin(G[d],base)))
                expected={x:scale(cmath.exp(1j*sum(t*q for t,q in zip(x,pvec))),symbol) for x in sites}
                check(f'free_symbol_n{n}_k{k}_m{mass}',field_error(D(v,links,n,mass),expected))
                if mass==.1 and k==(0,0,0,0):
                    check(f'wrong_seam_detected_n{n}',field_error(D(v,links,n,mass,wrong_seam=True),expected),mutation=True)
                    check(f'swapped_projectors_detected_n{n}',field_error(D(v,links,n,mass,swap=True),expected),mutation=True)
    for n in [2,4]:
        sites=list(itertools.product(range(n),repeat=4))
        links={(x,d):GROUP[(sum((i+1)*t for i,t in enumerate(x))+d)%len(GROUP)] for x in sites for d in range(4)}
        gauge={x:GROUP[(sum(x)*3+x[0]+1)%len(GROUP)] for x in sites}
        transformed={(x,d):mm(mm(gauge[x],links[x,d]),adj(gauge[shift_site(x,d,1,n)])) for x in sites for d in range(4)}
        v={x:[complex((i+sum(x))%7-3,(i*2+x[0])%5-2)/7 for i in range(12)] for x in sites}
        w={x:[complex((i*3+sum(x))%11-5,(i+x[1])%3-1)/11 for i in range(12)] for x in sites}
        gv={x:colour(gauge[x],v[x]) for x in sites};dv=D(v,links,n,.7)
        check(f'noncommuting_gauge_covariance_n{n}',field_error(D(gv,transformed,n,.7),{x:colour(gauge[x],dv[x]) for x in sites}))
        adjv=spinfield(G5,D(spinfield(G5,v),links,n,.7))
        check(f'gamma5_hermiticity_n{n}',abs(inner(v,D(w,links,n,.7))-inner(adjv,w)),tolerance=1e-9)
        chi=spinfield(G5,v);left1=D(chi,links,n,.3);left2=spinfield(G5,D(v,links,n,.9));wilson=W(chi,links,n)
        lhs={x:add(left1[x],left2[x]) for x in sites}
        rhs={x:add(scale(1.2,chi[x]),scale(2,wilson[x])) for x in sites}
        check(f'unequal_mass_axial_identity_with_wilson_term_n{n}',field_error(lhs,rhs))
        check(f'omitted_wilson_term_detected_n{n}',field_error(lhs,{x:scale(1.2,chi[x]) for x in sites}),mutation=True)
    paths=['YM/QCD/Lattice/Gamma.lean','YM/QCD/Lattice/Stencil.lean']
    record={'status':'passed','scope':'Independent finite Python model; source mapping manually reviewed; no Lean-to-Python extraction bridge','source_sha256':{p:hashlib.sha256((a.source/p).read_bytes()).hexdigest() for p in paths},'arithmetic':'IEEE complex; tolerances per case','checks':checks}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(record,indent=2)+'\n');print(f'{len(checks)} Wilson checks passed')
if __name__=='__main__':main()
