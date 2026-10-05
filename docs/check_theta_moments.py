"""Exact polynomial oracle for the batched Taylor integration kernel."""
from fractions import Fraction as Q
from flint import acb,acb_series,acb_mat,ctx
from certify_theta_continuous_jacobian import moments
from certify_theta_continuous import aq,uq


def main():
    ctx.prec=256;ctx.cap=12;order=12
    h=Q(1,14)
    weights=[aq(2*h**(k+1)/Q(k+1)) for k in range(0,order,2)]
    # Integer complex coefficients give an independent exact rational oracle.
    polys=[[(j+1,2-j) for j in range(order)],[(1-j,j*j-3) for j in range(order)]]
    kernels=[[(2*j-1,j+3) for j in range(order)],[(j*j,1-j) for j in range(order)]]
    series=[acb_series([acb(*v) for v in e]) for e in kernels]
    result=acb_mat([[acb(*v) for v in p] for p in polys])*moments(series,weights,order)
    for i,p in enumerate(polys):
        for m,e in enumerate(kernels):
            real=Q(0);imag=Q(0)
            for j,(a,b) in enumerate(p):
                for k,(c,d) in enumerate(e):
                    degree=j+k
                    if degree>=order or degree%2:continue
                    w=2*h**(degree+1)/Q(degree+1)
                    real+=(a*c-b*d)*w;imag+=(a*d+b*c)*w
            for part,want in [(result[i,m].real,real),(result[i,m].imag,imag)]:
                assert -uq(-part)<=want<=uq(part)
    print('PASS 4 complex batched integrals against exact rational convolution')


if __name__=='__main__':main()
