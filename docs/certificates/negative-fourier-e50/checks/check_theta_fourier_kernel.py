"""Signed Fourier quadrature against independent closed-form integrals."""
from fractions import Fraction as Q
from flint import arb,acb,acb_series,ctx
from certify_theta_fourier import cell_integral,qarb


def main():
    ctx.prec=432;ctx.cap=96
    n=32;K=96;h=Q(1,2*n);rad=2*h;I=acb(0,1);pi2=2*arb.pi()
    weights=[qarb(2*h**(k+1)/Q(k+1)) for k in range(0,K,2)]
    cases=[('linear',0,m) for m in [-7,-1,0,1,7]]
    cases += [('exponential',k,m) for k,m in [(-7,-7),(-1,-1),(-7,1),(1,1),(1,-1)]]
    for kind,k,m in cases:
        total=acb(0);bound=arb(0)
        kernel=acb_series([0,-I*pi2*m]).exp()
        for j in range(n):
            center=Q(2*j+1,2*n)-Q(1,2)
            t=acb_series([acb(qarb(center)),1])
            g=t if kind=='linear' else (I*pi2*k*t).exp()
            total+=cell_integral(g,kernel,center,m,weights)
            G=qarb(abs(center)+rad) if kind=='linear' else (pi2*abs(k)*qarb(rad)).exp()
            bound+=G*(pi2*abs(m)*qarb(rad)).exp()*qarb(Q(2,n)*Q(1,2)**K)
        enclosed=total+acb(arb(0,bound),arb(0,bound))
        if kind=='linear':
            # Integral t exp(-2*pi*i*m*t) = i*(-1)^m/(2*pi*m).
            want=acb(0) if m==0 else I*(1 if m%2==0 else -1)/(pi2*m)
        else:want=acb(1 if k==m else 0)
        assert enclosed.contains(want),(kind,k,m,enclosed,want)
    print('PASS',len(cases),'signed Fourier kernel checks against closed-form integrals')


if __name__=='__main__':main()
