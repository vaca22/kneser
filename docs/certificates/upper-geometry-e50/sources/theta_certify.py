"""Certify a local nonlinear finite theta map with directed discs and FLINT.

Run ONLY on galic, with PYTHONPATH=/data/kneser-verify/src.
This proves a finite-dimensional fixed-point statement, not distance to Kneser.
The exact map uses rational sample parameters and exact unit-circle roots, with
cardinal roots represented exactly; discrete arc/band geometry is certified.
"""
from __future__ import annotations
import argparse
import dataclasses
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time
import platform
import mpmath as mp
from flint import arb, acb, acb_mat, ctx as flint_ctx
from theta_ball import VerifiedDisc, VerifiedDiscCtx
from theta_branch import LogAudit
from demo_theta_operator import Pass, make_params, fixed_point_strings


def raw_mpf(x):
    return list(x._mpf_)


def fraction_mpf(x):
    sign, mantissa, exponent, _ = x._mpf_
    if exponent >= 0:
        return Fraction((-1 if sign else 1)*mantissa*(1 << exponent))
    return Fraction((-1 if sign else 1)*mantissa, 1 << (-exponent))


def as_arb(x):
    s, m, e, _ = x._mpf_
    return arb(((-1 if s else 1)*m, e))


def as_acb(d):
    # Exact dyadic centre and radius converted directly, not via decimal/float.
    # The rectangular hull of a complex disc is a valid enclosure.
    radius = as_arb(d.r)
    return acb(arb(as_arb(d.c.real), radius), arb(as_arb(d.c.imag), radius))


def encode_arb(x):
    return [[int(v) for v in x.lower().man_exp()],
            [int(v) for v in x.upper().man_exp()]]


def iv_record(x):
    return [list(t) for t in x._mpi_]


def log(*args):
    print(*args, flush=True)


class RigorousPass(Pass):
    def _enclose_fixed_point(self, Lre, Lim, X):
        box = super()._enclose_fixed_point(Lre, Lim, X)
        # Repeat with ONE exact dyadic preconditioner, and explicitly check
        # weighted infinity contraction in addition to strict self-mapping.
        m = X.mpc(X.mpf(Lre), X.mpf(Lim))
        mr = mp.mp.make_mpf(m.real._mpi_[0])
        mi = mp.mp.make_mpf(m.imag._mpi_[0])
        m = X.mpc(mr, mi)
        assert box.real.a <= m.real.a <= m.real.b <= box.real.b
        assert box.imag.a <= m.imag.a <= m.imag.b <= box.imag.b
        ell = X.mpf(1) if self.base == 'e' else X.log(X.mpf(self.base))
        fm = X.exp(ell*m)-m
        gm = ell*X.exp(ell*m)-1
        a = mp.mp.make_mpf(gm.real._mpi_[0])
        b = mp.mp.make_mpf(gm.imag._mpi_[0])
        # These floating candidates are arbitrary exact dyadics; their
        # accuracy is not trusted. The interval test below validates them.
        det = a*a+b*b
        ya, yb = a/det, b/det
        Y = [[X.mpf(ya), X.mpf(yb)], [-X.mpf(yb), X.mpf(ya)]]
        assert (Y[0][0]*Y[1][1]-Y[0][1]*Y[1][0]).a > 0
        g = ell*X.exp(ell*box)-1
        J = [[g.real,-g.imag],[g.imag,g.real]]
        M = [[X.mpf(i == j)-sum(Y[i][k]*J[k][j] for k in range(2))
              for j in range(2)] for i in range(2)]
        dx = [box.real-m.real,box.imag-m.imag]
        K = [v-sum(Y[i][k]*[fm.real,fm.imag][k] for k in range(2))
             +sum(M[i][k]*dx[k] for k in range(2))
             for i,v in enumerate([m.real,m.imag])]
        for i,B in enumerate([box.real,box.imag]):
            assert K[i].a>B.a and K[i].b<B.b
        # Equal unweighted norm is enough for these nearly square boxes.
        qs = [sum(abs(M[i][j]) for j in range(2)) for i in range(2)]
        assert all(q.b < X.mpf('0.5').a for q in qs)
        self.fixed_point_audit = {
            'verified':True,'box':[iv_record(box.real),iv_record(box.imag)],
            'center':[raw_mpf(mr),raw_mpf(mi)],
            'preconditioner':[[iv_record(v) for v in row] for row in Y],
            'K':[iv_record(v) for v in K],
            'row_norms':[iv_record(v) for v in qs]}
        return box

    def __init__(self,p,base,X):
        super().__init__(p,base,X)
        old_kinds = list(self.kinds)
        n=p.n_circ
        # Exact cardinal roots remove meaningless signs of rounded sin(pi).
        for j in range(n):
            if (4*j) % n == 0:
                self.circle[j]=[X.mpc(1),X.mpc(0,1),X.mpc(-1),X.mpc(0,-1)][(4*j//n)%4]
        self.tw_circ=[X.conj(c) for c in self.circle]
        self.lower=[2*j>n for j in range(n)]
        self.zpt=[X.conj(c) if self.lower[j] else c for j,c in enumerate(self.circle)]
        self.geometry_audit=[]
        kinds=[]
        iv=mp.iv
        delta=iv.mpf(p.idelta)
        for j,z in enumerate(self.zpt):
            im=iv.mpf(z.c.imag)+iv.mpf([-1,1])*iv.mpf(z.r)
            re=iv.mpf(z.c.real)+iv.mpf([-1,1])*iv.mpf(z.r)
            if im.a>=delta.b:
                kind='arc'; margin=im-delta
            elif im.b<delta.a:
                if re.a>0: kind='band+'; margin=re
                elif re.b<0: kind='band-'; margin=-re
                else: raise ValueError('band real sign is ambiguous')
                # Both the height and real sign must be separated.
                margin=min(margin.a,(delta-im).a)
            else: raise ValueError('arc/band height is ambiguous')
            if kind!=old_kinds[j]: raise ValueError('certified geometry differs from builder')
            kinds.append(kind)
            self.geometry_audit.append({'j':j,'kind':kind,'lower':self.lower[j],
                                        'positive_margin':iv_record(margin)})
        self.kinds=kinds


def geometric(d,r,count):
    pw=d.ctx.mpc(1)
    for _ in range(count):
        yield d*pw
        pw=pw*r


def build_matrix(ps,run):
    p,X=ps.p,ps.ctx
    nt,nf,nm,n=p.nt,p.nf,p.n_modes,p.n_circ
    start=time.time()
    A=acb_mat(nf,nt,[as_acb(v) for j in range(nf)
                     for v in geometric(run['dis'][j],ps.zs[j],nt)])
    Bcols=[list(geometric(X.mpf(1)/nf,ps.tw_theta[j],nm)) for j in range(nf)]
    B=acb_mat(nm,nf,[as_acb(Bcols[j][m]) for m in range(nm) for j in range(nf)])
    log('FLINT A/B factors',round(time.time()-start,1),'s')
    BA=B*A
    arc=[j for j in range(n) if ps.kinds[j]=='arc']
    C=acb_mat(len(arc),nm,[as_acb(v) for j in arc for v in geometric(
        run['dsup'][j],X.exp(ps.I*ps.pi2*(ps.zpt[j]-ps.I*ps.idelta)),nm)])
    CBA=C*BA
    log('FLINT CBA',round(time.time()-start,1),'s')
    rows=[None]*n
    for i,j in enumerate(arc):rows[j]=[CBA[i,k] for k in range(nt)]
    for j in range(n):
        if rows[j] is None:
            rows[j]=[as_acb(v) for v in geometric(run['dband'][j],run['zpts'][j],nt)]
        if ps.lower[j]:rows[j]=[v.conjugate() for v in rows[j]]
    M=acb_mat(rows)
    Ecols=[list(geometric(X.mpf(1),ps.tw_circ[j],nt)) for j in range(n)]
    E=acb_mat(nt,n,[as_acb(Ecols[j][k]) for k in range(nt) for j in range(n)])
    DT=E*M/n
    real=[[arb(0) if i==0 else DT[i,j].real for j in range(nt)] for i in range(nt)]
    log('FLINT DT complete',round(time.time()-start,1),'s')
    return real


def make_coeffs(X,strings,R,weight=Fraction(1,2)):
    out=[]
    for k,s in enumerate(strings):
        d=X.mpf(s)
        # c0 stays exactly 1 on the normalized affine coefficient space.
        w=mp.iv.mpf(weight.numerator)/mp.iv.mpf(weight.denominator)
        extra=mp.iv.mpf(0) if k==0 else mp.iv.mpf(R)/(w**k)
        out.append(VerifiedDisc(X,d.c,X.up(mp.iv.mpf(d.r)+extra)))
    return out


def evaluate(p,base,strings,dps,R,required_shifts=None,weight=Fraction(1,2)):
    X=VerifiedDiscCtx(dps)
    audit=LogAudit()
    original_log=X.log
    def checked_log(d):
        d=X.mpf(d)
        audit.observe(d,f'log[{getattr(audit,"count",len(audit.records))}]')
        return original_log(d)
    X.log=checked_log
    ps=RigorousPass(p,base,X)
    ps.required_unwrap_shifts=required_shifts
    run=ps.run(make_coeffs(X,strings,R,weight),log=log)
    return ps,run,audit


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--base',default='e',choices=['e','2'])
    ap.add_argument('--digits',type=int,default=50)
    ap.add_argument('--dps',type=int,default=210)
    ap.add_argument('--matrix-bits',type=int,default=100)
    ap.add_argument('--radius',default='1e-50')
    ap.add_argument('--weight',default='1/2',help='exact rational coefficient-norm weight')
    ap.add_argument('--out',required=True)
    ap.add_argument('--infinite-tail',action='store_true',
                    help='also certify the infinite Taylor extension of this fixed discrete map')
    args=ap.parse_args()
    out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    source_names=['theta_certify.py','theta_ball.py','theta_branch.py','demo_theta_operator.py']
    if args.infinite_tail: source_names.append('theta_infinite.py')
    source_bytes={name:Path(__file__).with_name(name).read_bytes() for name in source_names}
    frozen=out/'sources';frozen.mkdir(exist_ok=True)
    for name,content in source_bytes.items():(frozen/name).write_bytes(content)
    p=make_params(args.base,args.digits,None)
    strings,_,_=fixed_point_strings(args.base,args.digits,p.nt)
    assert Fraction(strings[0])==1
    R=Fraction(args.radius)
    weight=Fraction(args.weight)
    assert R>0
    assert 0<weight<1
    flint_ctx.prec=args.matrix_bits
    log('parameters',p,'dps',args.dps,'radius',args.radius,'weight',str(weight))
    ps0,r0,logs0=evaluate(p,args.base,strings,args.dps,'0',weight=weight)
    eta_bounds=[fraction_mpf((r0['new'][k]-ps0.ctx.mpf(s)).absup())
                for k,s in enumerate(strings)]
    eta=sum((v*weight**k for k,v in enumerate(eta_bounds)),Fraction(0))
    log('point eta',float(eta))
    ps,run,logs=evaluate(p,args.base,strings,args.dps,args.radius,
                          ps0.unwrap_audit['shifts'],weight=weight)
    assert ps.fixed_point_audit['box']==ps0.fixed_point_audit['box']
    assert ps.geometry_audit==ps0.geometry_audit
    matrix=build_matrix(ps,run)
    entries=[[encode_arb(x) for x in row] for row in matrix]
    def frac_pair(pair):
        m,e=pair; return Fraction(m)*(Fraction(2)**e)
    cols=[sum((max(abs(frac_pair(entries[i][j][0])),abs(frac_pair(entries[i][j][1])))
                    *weight**(i-j) for i in range(p.nt)),Fraction(0))
          for j in range(p.nt)]
    q=max(cols[1:])  # The certified affine domain fixes c0=1, so h0=0.
    passed=q<1 and eta+q*R<R
    payload={'object':'nonlinear finite theta map; exact cardinal geometry; c0=1',
        'base':args.base,'params':dataclasses.asdict(p),'dps':args.dps,
        'matrix_bits':args.matrix_bits,'radius':str(R),'weight':str(weight),
        'q_domain':'normalized_tangent_h0_zero','q_full':str(max(cols)),
        'eta':str(eta),'q':str(q),
        'passed':passed,'true_kneser_error_certified':False,
        'bound_distance':str(eta/(1-q)) if q<1 else None,
        'display':{'q':float(q),'eta':float(eta),'distance':float(eta/(1-q)) if q<1 else None},
        'fixed_point':ps.fixed_point_audit,'geometry':ps.geometry_audit,
        'unwrap_point':ps0.unwrap_audit,'unwrap_ball':ps.unwrap_audit,
        'logs_point':logs0.summary(),'logs_ball':logs.summary(),
        'jacobian_intervals':entries,'point_defect_component_bounds':[str(v) for v in eta_bounds],
        'coefficient_strings':strings,
        'runtime':{'python':platform.python_version(),'mpmath':mp.__version__,
                   'python_flint':__import__('flint').__version__},
        'source_hashes':{name:hashlib.sha256(content).hexdigest() for name,content in source_bytes.items()}}
    if args.infinite_tail:
        from theta_infinite import build_witness
        payload['infinite_taylor']=build_witness(ps,run,r0,weight,R,q,eta)
        inf=payload['infinite_taylor']['bounds']
        log('INFINITE TAYLOR', {k:float(Fraction(v)) if isinstance(v,str) else v
                              for k,v in inf.items()})
        passed=passed and inf['passed']
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    log('RESULT',payload['display'],'passed',passed)
    if not passed:raise SystemExit('contraction/self-map not proved')


if __name__=='__main__':main()
