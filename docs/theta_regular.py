"""Validated finite-depth error for the base-e regular superfunctions.

These estimates identify the regular Koenigs limit, NOT the real Kneser
solution. See theta-regular-depth.md for the telescoping and Rouche proofs.
"""
from fractions import Fraction as Q
import mpmath as mp
from theta_ball import VerifiedDisc

M_LO, M_HI, LOCAL_R, KOENIGS_C = Q(137,100), Q(138,100), Q(1,10), Q(3)


def validate_constants():
    q=1/(M_LO-LOCAL_R)
    ratio=M_HI*q*q
    coefficient=M_HI/(2*M_LO*(M_LO-LOCAL_R)*(1-ratio))
    assert q<1 and ratio<1 and coefficient<KOENIGS_C
    return q,ratio,coefficient


def ivq(q):
    return mp.iv.mpf(q.numerator)/q.denominator


def inflate(d, error):
    return VerifiedDisc(d.ctx,d.c,d.ctx.up(mp.iv.mpf(d.r)+error))


def modulus_lower(d):
    X=d.ctx
    return X.down(X._mod(d.c)-mp.iv.mpf(d.r))


class RegularLimit:
    def __init__(self, ps):
        validate_constants()
        assert ps.base=='e'
        self.ps,self.X=ps,ps.ctx
        assert modulus_lower(ps.L)>ivq(M_LO).b
        assert ps.L.absup()<ivq(M_HI).a
        assert (mp.iv.mpf(ps.L.c.real)-mp.iv.mpf(ps.L.r)).a>ivq(LOCAL_R).b
        # The certified exp fixed point is also a principal-log fixed point.
        assert (mp.iv.mpf(ps.L.c.imag)-mp.iv.mpf(ps.L.r)).a>0
        assert (mp.iv.mpf(ps.L.c.imag)+mp.iv.mpf(ps.L.r)).b<mp.iv.pi.a
        self.log_multiplier_lower=modulus_lower(ps.logL)
        assert self.log_multiplier_lower>0

    def inverse(self, w):
        X,ps=self.X,self.ps
        d=X.mpf(1)
        for _ in range(ps.p.depth):
            d=d/w
            w=X.log(w)
        u=w-ps.L
        U=mp.iv.mpf(u.absup())
        assert 2*U.b<ivq(LOCAL_R).a
        assert modulus_lower(u)>0
        rel=ivq(KOENIGS_C)*U
        assert rel.b<1
        chi=ps.Lpow*u
        # Certify the same principal logarithm for the exact limit.
        chi_error=mp.iv.mpf(ps.Lpow.absup())*ivq(KOENIGS_C)*U*U
        X.log(inflate(chi,chi_error))
        finite=X.log(chi)/ps.logL
        finite_derivative=d/(u*ps.logL)
        # -log(1-rel)<=rel/(1-rel), enabling a rational-only reduction check.
        error=rel/(1-rel)/mp.iv.mpf(self.log_multiplier_lower)
        derivative_relative=5*rel/(1-rel)
        exact=inflate(finite,error)
        exact_derivative=inflate(finite_derivative,
                                mp.iv.mpf(finite_derivative.absup())*derivative_relative)
        return exact,exact_derivative,{
            'terminal_u_upper':X.up(U),
            'value_error_upper':X.up(error),
            'derivative_relative_error_upper':X.up(derivative_relative)}

    def forward(self,z):
        X,ps=self.X,self.ps
        v=X.exp((z-ps.p.depth)*ps.logL)
        V=mp.iv.mpf(v.absup())
        error=2*ivq(KOENIGS_C)*V*V
        total=V+error
        assert 2*total.b<ivq(LOCAL_R).a
        assert (ivq(KOENIGS_C)*total*total).b<error.a
        assert (4*ivq(KOENIGS_C)*total).b<1
        initial_error=X.up(error)
        gain=X.up(mp.iv.mpf(1))
        error=mp.iv.mpf(initial_error)
        nominal=ps.L+v
        for _ in range(ps.p.depth):
            re_upper=mp.iv.mpf(nominal.c.real)+mp.iv.mpf(nominal.r)
            factor=mp.iv.exp(re_upper+error)
            gain=X.up(mp.iv.mpf(gain)*factor)
            error=mp.iv.mpf(initial_error)*mp.iv.mpf(gain)
            nominal=X.exp(nominal)
        return inflate(nominal,error),{
            'initial_v_upper':X.up(V),
            'initial_inverse_error_upper':initial_error,
            'propagation_gain_upper':gain,
            'value_error_upper':X.up(error)}
