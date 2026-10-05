"""R009 finite bounded interpolation on a rank half-plane.

These scalar interpolants do not by themselves solve hyperoperation successor
equations. Infinite positivity and a common height disk are separate hypotheses.
All mpmath computations are diagnostics, without interval rounding control.
"""
from __future__ import annotations

import mpmath as mp


def _data(nodes, values, sigma):
    sigma = mp.mpf(sigma)
    nodes, values = tuple(mp.mpf(x) for x in nodes), tuple(mp.mpc(x) for x in values)
    if not mp.isfinite(sigma) or not nodes or len(nodes) != len(values):
        raise ValueError("finite sigma and equally sized nonempty data required")
    if len(set(nodes)) != len(nodes) or any(not mp.isfinite(x) or x <= sigma for x in nodes):
        raise ValueError("distinct finite real nodes must exceed sigma")
    if any(not mp.isfinite(x) for x in values):
        raise ValueError("values must be finite")
    return nodes, values, sigma


def pick_matrix(nodes, values, *, sigma, bound):
    nodes, values, sigma = _data(nodes, values, sigma)
    bound = mp.mpf(bound)
    if not mp.isfinite(bound) or bound <= 0:
        raise ValueError("bound must be positive and finite")
    return mp.matrix([[(bound**2 - values[i] * mp.conj(values[j])) / (x + y - 2*sigma)
                       for j, y in enumerate(nodes)] for i, x in enumerate(nodes)])


def minimum_bound(nodes, values, *, sigma):
    """Finite-data extremal norm by a generalized Hermitian eigenproblem."""
    nodes, values, sigma = _data(nodes, values, sigma)
    c = mp.matrix([[1 / (x+y-2*sigma) for y in nodes] for x in nodes])
    lower = mp.cholesky(c)
    inverse = lower**-1
    v = mp.diag(values)
    a = inverse * v * c * v.H * inverse.H
    # Remove arithmetic asymmetry before calling the Hermitian eigensolver.
    a = (a + a.H) / 2
    eigenvalues = mp.eighe(a, eigvals_only=True)
    return mp.sqrt(max(mp.mpf(0), eigenvalues[len(eigenvalues)-1]))


def blaschke_bound(rank, *, sigma, last):
    sigma, rank = mp.mpf(sigma), mp.mpc(rank)
    if sigma >= 3 or not mp.isfinite(sigma) or not mp.isfinite(rank) or mp.re(rank) <= sigma:
        raise ValueError("require sigma<3 and finite rank in its open half-plane")
    if isinstance(last, bool) or not isinstance(last, int) or last < 3:
        raise ValueError("last must be an integer >=3")
    return mp.fprod(abs((rank-n)/(rank+n-2*sigma)) for n in range(3, last+1))


class FiniteSchur:
    """Strict finite Pick interpolation, with a constant free Schur parameter.

    Singular extremal data are deliberately rejected; the theoretical Pick
    criterion includes them, but this diagnostic implementation uses strict data.
    """
    def __init__(self, nodes, values, *, sigma, bound, free=0):
        nodes, values, self.sigma = _data(nodes, values, sigma)
        self.bound, self.free = mp.mpf(bound), mp.mpc(free)
        if not mp.isfinite(self.bound) or self.bound <= 0 or not mp.isfinite(self.free) or abs(self.free) > 1:
            raise ValueError("positive finite bound and |free|<=1 required")
        p = pick_matrix(nodes, values, sigma=self.sigma, bound=self.bound)
        if mp.eighe(p, eigvals_only=True)[0] <= 0:
            raise ValueError("this evaluator requires strictly positive Pick data")
        remaining_nodes = [(x-self.sigma-1)/(x-self.sigma+1) for x in nodes]
        remaining_values = [x/self.bound for x in values]
        self.steps = []
        while remaining_nodes:
            alpha, beta = remaining_nodes[0], remaining_values[0]
            if abs(beta) >= 1:
                raise ArithmeticError("Schur reduction lost strictness; increase precision")
            self.steps.append((alpha, beta))
            remaining_values = [((value-beta)/(1-mp.conj(beta)*value))
                                / ((node-alpha)/(1-mp.conj(alpha)*node))
                                for node, value in zip(remaining_nodes[1:], remaining_values[1:])]
            remaining_nodes = remaining_nodes[1:]

    def value(self, rank):
        rank = mp.mpc(rank)
        if not mp.isfinite(rank) or mp.re(rank) <= self.sigma:
            raise ValueError("finite rank in the open half-plane required")
        z = (rank-self.sigma-1)/(rank-self.sigma+1)
        g = self.free
        for alpha, beta in reversed(self.steps):
            b = (z-alpha)/(1-mp.conj(alpha)*z)
            g = (beta+b*g)/(1+mp.conj(beta)*b*g)
        return self.bound*g
