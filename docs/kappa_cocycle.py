"""Check of the cocycle law for kappa_tr (paper Remark rem:gen-cocycle):
Re kappa_tr(psi^-1 g psi) = Re kappa_tr(g) - d log|B_n|[(1/psi')o g~ - 1]/(4 a2),
for g = e^u - 1 and psi(u) = u + 0.3 u^2.  Usage: python3 docs/kappa_cocycle.py"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import mpmath as mp
from kappa_variation import *
mp.mp.dps=45
M=50
beta=mp.mpf('0.3')
def smul_(a,b): return ser_mul(a,b,M+1)
def compose(f,h):
    """f(h(u)) series, h[0]=0."""
    out=[mp.mpc(0)]*(M+1); p=[mp.mpc(1)]+[mp.mpc(0)]*M
    for k in range(M+1):
        if k>0: p=smul_(p,h)
        out=[o+f[k]*x for o,x in zip(out,p)]
    return out
psi=[mp.mpc(0),mp.mpc(1),beta]+[mp.mpc(0)]*(M-2)
# reversion of psi: solve psi(r(v))=v iteratively
r=[mp.mpc(0),mp.mpc(1)]+[mp.mpc(0)]*(M-1)
for it in range(M+2):
    c=compose(psi,r); r=[ri-(ci-(1 if i==1 else 0)) for i,(ri,ci) in enumerate(zip(r,c))]
g,a2=GERMS['exp']
gt_ser=compose(r,compose(g.taylor(M),psi))
def psiinv(x):
    v=x
    for _ in range(80):
        st=(v+beta*v*v-x)/(1+2*beta*v); v-=st
        if abs(st)<mp.mpf(10)**(-mp.mp.dps+3): break
    return v
gt=Fn(lambda v: psiinv(g.val(v+beta*v*v)),
      lambda v: g.der(v+beta*v*v)*(1+2*beta*v)/(1+2*beta*psiinv(g.val(v+beta*v*v))),
      lambda m: gt_ser[:m+1]+[mp.mpc(0)]*max(0,m-M))
print("check series vs value:", mp.nstr(abs(sum(c*mp.mpf('0.05')**k for k,c in enumerate(gt_ser))-gt.val(mp.mpf('0.05'))),3))
inv1=[mp.mpc(0)]*(M+1)  # 1/psi'(w) = 1/(1+2 beta w) series in w
for k in range(M+1): inv1[k]=(-2*beta)**k
Xt_ser=compose(inv1,gt_ser)
Xt=Fn(lambda v: 1/(1+2*beta*gt.val(v)), lambda v: -2*beta*gt.der(v)/(1+2*beta*gt.val(v))**2, lambda m: Xt_ser[:m+1])
ustar=1/mp.e-1; ut=psiinv(ustar)
Y=mp.mpf(1); eps=mp.mpf(10)**(-15)
gp_t=gate_points(gt,a2,Y,24,1500)
out,dpds,_,res,_=dlogtau(gt,a2,const(1),ut,gp_t,eps)
ktr_t={k:v/dpds for k,v in out.items()}
c=Xt.der(0)/(2*a2)
gtp=lambda M_: [ (k+1)*gt_ser[k+1] - (1 if k==0 else 0) for k in range(M_+1)]
X1=Fn(lambda v: Xt.val(v)+c*(1-gt.der(v))-1, None, lambda m:[x-c*y-(1 if i==0 else 0) for i,(x,y) in enumerate(zip(Xt.taylor(m),gtp(m)))])
Ms=melnikov(gt,X1,ut,Y)
Kg={1:mp.mpf('-0.0101990063458974086606'),2:mp.mpf('-0.0510565562013188605'),3:mp.mpf('-0.140044348152265138')}
for k in (1,2,3):
    pred=Kg[k]-mp.re(Ms[k])/(4*a2)
    print(f"n={k}: Re kappa_tr(g~) = {mp.nstr(mp.re(ktr_t[k]),18)}  cocycle prediction {mp.nstr(pred,18)}  diff {mp.nstr(abs(mp.re(ktr_t[k])-pred),3)}  (horn term {mp.nstr(mp.re(Ms[k])/(4*a2),8)})")
