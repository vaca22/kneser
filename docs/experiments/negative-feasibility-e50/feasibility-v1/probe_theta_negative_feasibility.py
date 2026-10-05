"""Exploratory finite negative-moment Newton solves; run on galic only.

Ordinary high precision, finite regular depth and Gaussian quadrature.
These are NOT interval certificates and do not prove exact feasibility.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import mpmath as mp
from demo_theta_operator import fixed_point_strings


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--dps',type=int,default=170);ap.add_argument('--depth',type=int,default=600)
    ap.add_argument('--nodes',type=int,default=96);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=False);mp.mp.dps=args.dps
    strings,_,_=fixed_point_strings('e',50,150);cs=list(map(mp.mpf,strings))
    r=mp.mpf(11)/20;delta=mp.mpf(3602879701896397)/36028797018963968
    L=-mp.lambertw(-1,-1);logL=mp.log(L);start=time.time()
    def grid(n):
        t,w=mp.gauss_quadrature(n,'legendre')
        return [(t[j]/2,w[j]/2,t[j]/2+1j*delta) for j in range(n)]
    primary=grid(args.nodes);independent=grid(args.nodes+32)
    def evaluate(u,N,nodes,depth,with_jacobian):
        a=[mp.mpc(0) for _ in range(N)]
        J=mp.matrix(2*N,2*N) if with_jacobian else None
        lp=L**depth
        for t,weight,z in nodes:
            basis=[(z/r)**j for j in range(1,2*N+1)]
            w=mp.polyval(list(reversed(cs)),z)+sum(x*b for x,b in zip(u,basis))
            der=mp.mpc(1)
            for _ in range(depth):
                if with_jacobian:der/=w
                w=mp.log(w)
            if with_jacobian:der/=((w-L)*logL)
            g=mp.log(lp*(w-L))/logL-z
            for m in range(1,N+1):
                factor=weight*mp.exp(2j*mp.pi*m*t);a[m-1]+=factor*g
                if with_jacobian:
                    for j,b in enumerate(basis):
                        v=factor*der*b;J[2*m-2,j]+=v.real;J[2*m-1,j]+=v.imag
        y=mp.matrix([v for a0 in a for v in [a0.real,a0.imag]])
        return y,J
    records=[]
    for N in [2,4,8]:
        u=mp.matrix(2*N,1);steps=[]
        for iteration in range(2):
            y,J=evaluate(u,N,primary,args.depth,True)
            change=mp.lu_solve(J,-y);u+=change
            steps.append({'iteration':iteration,'residual_max':mp.nstr(mp.norm(y,mp.inf),50),
                          'correction_l1':mp.nstr(mp.norm(change,1),50)})
            print('N',N,'iteration',iteration,'residual',mp.nstr(mp.norm(y,mp.inf),8),
                  'correction',mp.nstr(mp.norm(change,1),8),'seconds',round(time.time()-start,1),flush=True)
        y,_=evaluate(u,N,primary,args.depth,False)
        cross,_=evaluate(u,N,independent,args.depth+40,False)
        records.append({'negative_modes':N,'real_variables':2*N,'steps':steps,
            'normalized_real_coefficients':[mp.nstr(x,args.dps) for x in u],
            'weighted_center_distance':mp.nstr(mp.norm(u,1),60),
            'final_residual_max':mp.nstr(mp.norm(y,mp.inf),60),
            'independent_grid_depth_residual_max':mp.nstr(mp.norm(cross,mp.inf),60)})
        print('N',N,'cross residual',mp.nstr(mp.norm(cross,mp.inf),8),flush=True)
    raw=Path(__file__).read_bytes();(args.out/Path(__file__).name).write_bytes(raw)
    result={'object':'exploratory finite negative-moment feasibility',
        'dps':args.dps,'depth':args.depth,'nodes':args.nodes,
        'cross_depth':args.depth+40,'cross_nodes':args.nodes+32,
        'coefficient_strings':strings,'source_sha256':hashlib.sha256(raw).hexdigest(),
        'results':records,'finite_exact_feasibility_certified':False,
        'uniform_in_truncation_feasibility_certified':False,'true_kneser_error_certified':False}
    (args.out/'probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE exploratory only; no exact feasibility certified',flush=True)


if __name__=='__main__':main()
