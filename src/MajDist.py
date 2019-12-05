#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#


from sage.all import Polyhedron as _Polyhedron
from sage.all import PolynomialRing as _PolynomialRing
from sage.all import QQ as _QQ
from sage.all import var as _var
from Zeta.smurf import SMURF as _Zeta_smurf

# compute the major distribution of a poset P
def MajorDistribution(P):
    from sage.combinat.posets.posets import FinitePoset 
    if not isinstance(P, FinitePoset):
        # An error here means we cannot interpret input as a poset
        P = FinitePoset(P)
    n = len(P)
    relations = []
    zero_vec = tuple([0 for i in range(n + 1)]) 

    # Basic function: add k to the i-th component of v.
    def add_k_i(v, i, k):
        u = list(v)
        u[i] += k
        return tuple(u)

    # nonnegative relations.
    relations += [add_k_i(zero_vec, i, 1) for i in range(1, n + 1)]
    poset_edges = P.cover_relations()
    rel_to_vec = lambda x: add_k_i(add_k_i(zero_vec, x[0], 1), x[1], -1)
    relations += map(rel_to_vec, poset_edges)
    
    Poly = _Polyhedron(ieqs=relations)
    R = _PolynomialRing(_QQ, 'x', n)
    sm = _Zeta_smurf.from_polyhedron(Poly, R)
    T = _var('t')
    z = sm.evaluate(variables=tuple([T]*n))
    N, D = z.numerator_denominator()

    stan_denom = reduce(lambda x, y: x*(1 - T**y), range(1, n+1), 1)
    fact = stan_denom / D
    QT = _PolynomialRing(_QQ, T)
    assert fact in QT
    return (N*QT(fact)).expand()