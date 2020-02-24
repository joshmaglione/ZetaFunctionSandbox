#
#   Copyright 2020 Joshua Maglione 
#
#   Distributed under MIT License
#

from sage.all import PolynomialRing as _Poly_ring
from sage.all import QQ as _QQ
from sage.all import vector as _vec


# Get the variables for a row vector.
def _row_vector_vars(P, n, i):
    return _vec(P.gens()[i*n - i*(i - 1)//2:(i + 1)*n - (i + 1)*i//2])

# My own dot product
def _dot_product(u, v):
    w = zip(u.list(), v.list())
    return reduce(lambda x, y: x + y[0]*y[1], w, 0)

# Given a polynomial ring, integers i and j, multiply row i with row j at the
# matrix M (to obtain the kth coefficient). 
def _multiply_rows(P, i, j, M):
    n = M.ncols()
    X = M[i:]
    varbs_i = _row_vector_vars(P, n, i)
    varbs_j = _row_vector_vars(P, n, j)
    X_cols = [X[:,i] for i in range(n)]
    u = map(lambda x: _dot_product(varbs_i, x), X_cols)
    return _dot_product(_vec(u[j:]), varbs_j)

def _Gaussian_steps(P, n, v, conds=[]):
    i = 0
    while v[i] != 0:
        i += 1
        if i >= len(v):
            return conds
    varbs_i = _row_vector_vars(P, n, i)
    c = v[i] / varbs_i[0]
    if c in P:
        # The first nonzero entry is a multiple
        v_new = v[:i] + map(lambda x: x[0] - c*x[1], zip(v[i:], varbs_i))
        return _Gaussian_steps(P, n, v_new, conds=conds)
    else:
        # The first nonzero entry is not a multiple
        # Figure out how to properly handle the denominators.

# Given a tensor as a sequence of matrices, return the cone conditions 
# (assuming upper triangular).
def ConeConditions(t):
    # initial setup
    n = t[0].ncols()
    m = len(t)
    P = _Poly_ring(_QQ, (n + 1)*n//2, "X")

    # build vectors
    vecs = [[_multiply_rows(P, i, j, t[k]) for k in range(m)] for i in range(n) for j in range(i, n)]

    # Gaussian steps

    return vecs