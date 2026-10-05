"""Directed branch certificates for the finite theta map.

The Disc backend must rigorously enclose its arguments.  This module adds no
heuristic ulps.  Decisions use mpmath.iv interval endpoints; mp.nint proposes
an integer only, which is subsequently certified by strict inequalities.
"""
from __future__ import annotations

import mpmath as mp


def _iv(ctx):
    iv = getattr(ctx, 'iv', mp.iv)
    if iv.dps < ctx.dps:
        raise ValueError('audit interval precision below Disc precision')
    return iv


def _record(x):
    # Binary endpoints are exact, portable proof data; decimal is display only.
    return {'display': str(x), 'binary_endpoints': [list(t) for t in x._mpi_]}


def _real_hull(d):
    iv = _iv(d.ctx)
    return iv.mpf(d.c.real) + iv.mpf([-1, 1]) * iv.mpf(d.r)


def audited_unwrap(theta, period, shifts=None):
    """Return (unwrapped_discs, audit). Every raw sample's integer is recorded.

    shifts, if given, is the full centre-pass list, including shifts[0] = 0.
    Without it a candidate is proposed from the enclosed quotient's centre.
    Success proves the identical nearest-integer branch throughout the input
    coefficient ball, even when successive samples have nonzero shifts.
    """
    if not theta:
        raise ValueError('empty theta samples')
    if shifts is not None and (len(shifts) != len(theta) or shifts[0] != 0):
        raise ValueError('shifts must have nf entries beginning with zero')
    iv = _iv(period.ctx)
    out, chosen, cells = [theta[0]], [0], []
    min_margin = None
    for j, raw in enumerate(theta[1:], 1):
        q = (raw - out[-1]) / period
        x = _real_hull(q)
        k = int(shifts[j]) if shifts is not None else int(mp.nint(mp.re(q.c)))
        left, right = iv.mpf(k) - iv.mpf(1)/2, iv.mpf(k) + iv.mpf(1)/2
        if not (x.a > left.b and x.b < right.a):
            raise ValueError(f'unwrap sample {j}: {x} not strictly in cell ({k}-1/2,{k}+1/2)')
        margins = (x - left, right - x)
        margin = min(margins[0].a, margins[1].a)
        min_margin = margin if min_margin is None else min(min_margin, margin)
        cells.append({'sample': j, 'shift': k, 'quotient_real': _record(x),
                      'margin_lower': _record(margin)})
        chosen.append(k)
        out.append(raw - k * period)
    # Builder only warns for this last decision; it does not change the map.
    q = (theta[0] - out[-1]) / period
    x = _real_hull(q)
    k = int(mp.nint(mp.re(q.c)))
    wrap_stable = bool(x.a > iv.mpf(k)-iv.mpf(1)/2 and x.b < iv.mpf(k)+iv.mpf(1)/2)
    return out, {'verified': True, 'shifts': chosen, 'cells': cells,
                 'minimum_cell_margin': _record(min_margin) if min_margin is not None else None,
                 'closing_wrap': k, 'closing_wrap_stable': wrap_stable,
                 'closing_quotient': _record(x)}


class LogAudit:
    """Observe every principal log argument *before* evaluating the log.

    Attach manually at each log site or wrap ctx.log temporarily. Site labels
    such as theta[17]/inverse[4], theta[17]/final, circle[22]/band- identify
    the actual chain. Failed observations are retained and then raise.
    """
    def __init__(self, compact=True):
        self.compact = compact
        self.records = []
        self.count = 0
        self.failed = False
        self.worst_zero = None
        self.worst_cut = None
        self._min_zero = None
        self._min_cut = None

    def observe(self, d, label='log'):
        iv = _iv(d.ctx)
        re, im, radius = iv.mpf(d.c.real), iv.mpf(d.c.imag), iv.mpf(d.r)
        modulus = iv.sqrt(re*re + im*im)
        # Distance to the CLOSED negative real ray, including zero.
        if re.b <= 0:
            distance = abs(im)
        elif re.a >= 0:
            distance = modulus
        else:
            # Unlikely for exact stored centres, but conservative if rounded.
            distance = abs(im)
        zero_margin, cut_margin = modulus-radius, distance-radius
        ok = bool(zero_margin.a > 0 and cut_margin.a > 0)
        self.count += 1
        self.failed = self.failed or not ok
        new_zero = self._min_zero is None or zero_margin.a < self._min_zero
        new_cut = self._min_cut is None or cut_margin.a < self._min_cut
        if not self.compact or not ok or new_zero or new_cut:
            record = {'site': label, 'index': self.count, 'verified': ok,
                      'zero_margin': _record(zero_margin),
                      'cut_margin': _record(cut_margin),
                      'argument_radius': _record(radius)}
            if not self.compact or not ok:
                self.records.append(record)
            if new_zero:
                self._min_zero, self.worst_zero = zero_margin.a, record
            if new_cut:
                self._min_cut, self.worst_cut = cut_margin.a, record
        if not ok:
            raise ValueError(f'principal log audit failed at {label}: cut margin {cut_margin}, zero margin {zero_margin}')
        return d

    def summary(self):
        return {'verified': self.count > 0 and not self.failed, 'count': self.count,
                'compact': self.compact, 'worst_zero': self.worst_zero,
                'worst_cut': self.worst_cut, 'records': self.records}
