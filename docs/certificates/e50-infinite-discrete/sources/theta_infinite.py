"""Infinite Taylor extension of the FIXED discrete theta map.

The scalar enclosures are trusted evaluator output; all block reductions and
self-map comparisons below use exact rationals. This is not the continuous
ideal operator and is not a true-Kneser error certificate.
"""
from fractions import Fraction as Q


def upward_dyadic(value, bits=40):
    """Coarsen a nonnegative rational upward to keep tail powers portable.

    Exact 130-digit dyadics raised to the 150th power can exceed Python's
    integer-to-string limit. These coarse bounds only multiply small tails.
    """
    assert value >= 0
    scale = 1 << bits
    return Q((value.numerator*scale+value.denominator-1)//value.denominator, scale)


def reduce_bounds(n, r, radius, low_q, low_defect, rho, K, B):
    assert n >= 2 and 0 <= rho < r < 1
    assert radius > 0 and min(low_q, low_defect, K, B) >= 0
    ratio = rho / r
    low = sum((r**k for k in range(1, n)), Q(0))
    tail = r**n / (1-r)
    a, b = low_q, low*K*ratio**n
    c, d = tail*K*ratio, tail*K*ratio**n
    q = max(a+c, b+d)
    defect = low_defect+B*tail
    return dict(a=a, b=b, c=c, d=d, q=q, defect=defect,
                output_tail=B*tail,
                distance=defect/(1-q) if q < 1 else None,
                passed=q < 1 and defect+q*radius < radius)


def build_witness(ps, run, point_run, weight, radius, low_q, low_defect):
    # Import only on the numerical path; checking needs the standard library.
    from theta_certify import fraction_mpf
    upper = lambda x: upward_dyadic(fraction_mpf(x.absup()))
    p = ps.p
    samples = [upper(z) for z in ps.zs]
    bands = [upper(run['zpts'][j]) for j in range(p.n_circ)
             if ps.kinds[j] != 'arc']
    inverse = [upper(x) for x in run['dis']]
    forward = [upper(run['dsup'][j]) if ps.kinds[j] == 'arc'
               else upper(run['dband'][j]) for j in range(p.n_circ)]
    # Certified geometry gives Im(z)>=delta on every arc. Every Fourier
    # reconstruction multiplier then has modulus <=1, so G_j<=n_modes.
    node_K = [v*p.n_modes*max(inverse) if ps.kinds[j] == 'arc' else v
              for j, v in enumerate(forward)]
    values = [upper(v) for v in point_run['vals']]
    rho, K, B = max(samples+bands), max(node_K), max(values)
    reduced = reduce_bounds(p.nt, weight, radius, low_q, low_defect, rho, K, B)
    return {
        'object': 'infinite Taylor extension of fixed discrete theta map',
        'coverage': 'complex coefficient discs contain pointwise infinite ball',
        'sample_radius_bounds': list(map(str, samples)),
        'band_radius_bounds': list(map(str, bands)),
        'inverse_derivative_bounds': list(map(str, inverse)),
        'node_derivative_bounds': list(map(str, forward)),
        'point_node_value_bounds': list(map(str, values)),
        'rho': str(rho), 'K': str(K), 'B': str(B),
        'bounds': {k: str(v) if isinstance(v, Q) else v for k,v in reduced.items()},
        'true_kneser_error_certified': False,
    }


def check_witness(data):
    w = data['infinite_taylor']
    assert w['object'] == 'infinite Taylor extension of fixed discrete theta map'
    assert w['coverage'] == 'complex coefficient discs contain pointwise infinite ball'
    assert data['q_domain'] == 'normalized_tangent_h0_zero'
    p = data['params']
    def bounds(key, count):
        result = list(map(Q, w[key]))
        assert len(result) == count and all(v >= 0 for v in result)
        return result
    samples = bounds('sample_radius_bounds', p['nf'])
    bands = bounds('band_radius_bounds', sum(g['kind'] != 'arc' for g in data['geometry']))
    inverse = bounds('inverse_derivative_bounds', p['nf'])
    forward = bounds('node_derivative_bounds', p['n_circ'])
    values = bounds('point_node_value_bounds', p['n_circ'])
    rho, B = max(samples+bands), max(values)
    K = max(v*p['n_modes']*max(inverse) if g['kind'] == 'arc' else v
            for v,g in zip(forward, data['geometry']))
    assert (rho,K,B) == tuple(Q(w[k]) for k in ['rho','K','B'])
    result = reduce_bounds(p['nt'], Q(data['weight']), Q(data['radius']),
                           Q(data['q']), Q(data['eta']), rho, K, B)
    for k,v in result.items():
        if isinstance(v,Q): assert Q(w['bounds'][k]) == v, k
        else: assert w['bounds'][k] == v, k
    assert result['passed'] and w['true_kneser_error_certified'] is False
    return result
