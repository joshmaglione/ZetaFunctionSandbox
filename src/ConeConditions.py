#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from sage.all import PolynomialRing as _Poly_ring
from sage.all import QQ as _QQ


# Get the variables for a row vector.
def _row_vector_vars(P, n, i):
    return P.gens()[i*n - i*(i - 1)//2:(i + 1)*n - (i + 1)*i//2]

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
    X_cols = [X[:][i] for i in range(n)]
    u = map(lambda x: _dot_product(varbs_i, x), X_cols)
    return _dot_product(u[j:], varbs_j)

# Given a tensor as a sequence of matrices, return the cone conditions 
# (assuming upper triangular).
def ConeConditions(t):
    n = t[0].ncols()
    m = len(t)
    P = _Poly_ring(_QQ, (n + 1)*n//2, "X")
    vecs = [[_multiply_rows(P, i, j, t[k]) for k in range(m)] for i in range(n) for j in range(i, n)]
    return vecs