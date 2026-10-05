"""Directed complex discs for the finite theta operator.

Integration: ``from theta_ball import VerifiedDisc as Disc, VerifiedDiscCtx
as DiscCtx`` after the legacy class definitions and before ``is_disc_ctx``.
No heuristic ulp factors are used. Trusted base: mpmath.iv real/complex
arithmetic and elementary functions, and mpmath's exact internal dyadic
endpoint constructors. This is an interval arithmetic certificate backend,
not a formal verification of mpmath itself.

Rounding proof: every centre expression is evaluated on singleton interval
inputs. _from_box chooses the exact lower-left endpoint as its centre, and
uses the upward-rounded Euclidean box diagonal as its radius. It therefore
covers the whole result box, including all centre rounding error. All
analytic radius expressions are evaluated by iv and their upper endpoints
are stored exactly, without conversion through finite-precision arithmetic.
The lower-left choice is slightly less tight than midpoint, but eliminates
any midpoint-rounding assumption. Every subsequent mpf is an exact dyadic
input; decimal strings are parsed directly by iv. No ordinary mp arithmetic
is used for any bound.

For discs D(c,r), D(d,s): product radius is |c|s+|d|r+rs;
reciprocal radius is r/(a(a-r)) for a <= |c| and a>r; exp radius
is exp(Re(c))*(exp(r)-1); log radius is -log(1-r/a), requiring
a>r and disjointness from the principal cut. Rounded centre-box radii are
added to each. These follow respectively by expansion, the reciprocal
identity, the exponential power series, and the log power series. Real and
imaginary projections and conjugation preserve the radius. Each scalar
operation is therefore an enclosure by induction over the computation.

Contexts share mpmath.iv's global precision. Use one precision at a time;
changing it between operations remains enclosing but changes tightness.
"""
from __future__ import annotations
import mpmath as mp

_ZERO = mp.mpf(0)._mpf_


def _endpoint(x, upper):
    """Extract finite iv endpoint as an exact dyadic, with NO rounding."""
    ans = mp.mp.make_mpf(x._mpi_[int(upper)])
    if not mp.isfinite(ans):
        raise ArithmeticError("nonfinite interval endpoint")
    return ans


def _complex(re, im):
    return mp.mp.make_mpc((re._mpf_, im._mpf_))


class VerifiedDisc:
    __slots__ = ("ctx", "c", "r")

    def __init__(self, ctx, c, r):
        # Internal callers supply exact stored dyadics; external callers must
        # use ctx.mpf/mpc to enclose decimal parsing and initial arithmetic.
        if not hasattr(c, "_mpc_") or not hasattr(r, "_mpf_"):
            raise TypeError("Disc constructor requires exact mpc/mpf; use ctx.mpf/mpc")
        if r < 0 or not mp.isfinite(r) or not mp.isfinite(c):
            raise ValueError("invalid disc")
        self.ctx, self.c, self.r = ctx, c, r

    def _coerce(self, other):
        if isinstance(other, VerifiedDisc):
            if other.ctx is not self.ctx:
                raise ValueError("mixed disc contexts")
            return other
        return self.ctx.mpf(other)

    def __add__(self, other):
        o, X = self._coerce(other), self.ctx
        return X._with_radius(X._point(self.c) + X._point(o.c), X._iv(self.r) + X._iv(o.r))
    __radd__ = __add__

    def __neg__(self):
        # Negation is exact in mpmath, including at reduced current precision.
        re, im = self.c._mpc_
        def neg(t):
            return (1-t[0], t[1], t[2], t[3]) if t[1] else t
        return VerifiedDisc(self.ctx, mp.mp.make_mpc((neg(re), neg(im))), self.r)

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        o, X = self._coerce(other), self.ctx
        r, s = X._iv(self.r), X._iv(o.r)
        extra = X._mod(self.c)*s + X._mod(o.c)*r + r*s
        return X._with_radius(X._point(self.c)*X._point(o.c), extra)
    __rmul__ = __mul__

    def inverse(self):
        X = self.ctx
        a = X._abslow(self.c)
        if not self.r < a:
            raise ZeroDivisionError("disc contains zero or separation unproved")
        ai, r = X._iv(a), X._iv(self.r)
        return X._with_radius(1/X._point(self.c), r/(ai*(ai-r)))

    def __truediv__(self, other):
        return self*self._coerce(other).inverse()

    def __rtruediv__(self, other):
        return self._coerce(other)*self.inverse()

    @property
    def real(self):
        return VerifiedDisc(self.ctx, mp.mp.make_mpc((self.c._mpc_[0], _ZERO)), self.r)

    @property
    def imag(self):
        return VerifiedDisc(self.ctx, mp.mp.make_mpc((self.c._mpc_[1], _ZERO)), self.r)

    def absup(self):
        return self.ctx.up(self.ctx._mod(self.c) + self.ctx._iv(self.r))


class VerifiedDiscCtx:
    is_verified_disc_context = True
    iv = mp.iv
    def __init__(self, dps):
        self.dps = dps
        mp.iv.dps = dps
        mp.mp.dps = dps

    @staticmethod
    def _iv(x):
        return mp.iv.mpf(x)

    @staticmethod
    def up(x):
        return _endpoint(mp.iv.mpf(x), True)

    @staticmethod
    def down(x):
        return _endpoint(mp.iv.mpf(x), False)

    def _point(self, c):
        # real/imag properties return exact dyadic components.
        return mp.iv.mpc(c.real, c.imag)

    def _mod(self, c):
        re, im = self._iv(c.real), self._iv(c.imag)
        return mp.iv.sqrt(re*re + im*im)

    def _absup(self, c):
        return self.up(self._mod(c))

    def _abslow(self, c):
        return self.down(self._mod(c))

    def _from_box(self, box):
        if hasattr(box, "_mpci_"):
            re, im = box.real, box.imag
        else:
            re, im = mp.iv.mpf(box), mp.iv.mpf(0)
        cr, ci = self.down(re), self.down(im)
        wr = self._iv(self.up(re)) - self._iv(cr)
        wi = self._iv(self.up(im)) - self._iv(ci)
        radius = self.up(mp.iv.sqrt(wr*wr + wi*wi))
        return VerifiedDisc(self, _complex(cr, ci), radius)

    def _with_radius(self, box, extra):
        b = self._from_box(box)
        return VerifiedDisc(self, b.c, self.up(self._iv(b.r) + extra))

    def mpf(self, x):
        if isinstance(x, VerifiedDisc):
            if x.ctx is not self:
                raise ValueError("mixed disc contexts")
            return x
        if isinstance(x, complex) or hasattr(x, "_mpc_"):
            return self._from_box(mp.iv.mpc(x.real, x.imag))
        return self._from_box(mp.iv.mpf(x))

    def mpc(self, a, b=0):
        da, db = self.mpf(a), self.mpf(b)
        if da.c.imag != 0 or db.c.imag != 0:
            # mpc(z) is expected to preserve a complex operand.
            return da + self.mpf(1j)*db
        return VerifiedDisc(self, _complex(da.c.real, db.c.real),
                            self.up(self._iv(da.r) + self._iv(db.r)))

    @property
    def pi(self):
        return self._from_box(mp.iv.pi)

    def exp(self, d):
        d = self.mpf(d)
        extra = mp.iv.exp(self._iv(d.c.real))*mp.iv.expm1(self._iv(d.r))
        return self._with_radius(mp.iv.exp(self._point(d.c)), extra)

    def log(self, d):
        d = self.mpf(d)
        a = self._abslow(d.c)
        if not d.r < a:
            raise ValueError("log: disc contains zero or separation unproved")
        # For Re(c)>0 the closest point on the cut is zero, already excluded.
        if d.c.real <= 0 and self.down(abs(self._iv(d.c.imag))) <= d.r:
            raise ValueError("log: disc intersects principal branch cut")
        extra = -mp.iv.log1p(-self._iv(d.r)/self._iv(a))
        return self._with_radius(mp.iv.log(self._point(d.c)), extra)

    def conj(self, d):
        d = self.mpf(d)
        im = d.c._mpc_[1]
        nim = (1-im[0], im[1], im[2], im[3]) if im[1] else im
        return VerifiedDisc(self, mp.mp.make_mpc((d.c._mpc_[0], nim)), d.r)
