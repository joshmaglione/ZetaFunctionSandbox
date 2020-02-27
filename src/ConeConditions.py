#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from sage.all import Matrix as _Mat
from sage.all import PolynomialRing as _Poly_ring
from sage.all import QQ as _QQ
from sage.all import vector as _vec


# Get the variables for a row vector.
def _row_vector_vars(P, n, i, UT=True):
    gens = P.gens()
    if UT:
        return _vec(gens[i*n - i*(i - 1)//2:(i + 1)*n - (i + 1)*i//2])
    else:
        gens = gens[::-1]
        j = n - i - 1
        return _vec(gens[j*n - j*(j - 1)//2:(j + 1)*n - (j + 1)*j//2][::-1])

# My own dot product
def _dot_product(u, v):
    w = zip(u.list(), v.list())
    return reduce(lambda x, y: x + y[0]*y[1], w, 0)

# Given a polynomial ring, integers i and j, multiply row i with row j at the
# matrix M (to obtain the kth coefficient). 
def _multiply_rows(P, i, j, M, UT=True):
    n = M.ncols()
    varbs_i = _row_vector_vars(P, n, i)
    varbs_j = _row_vector_vars(P, n, j)
    if UT:
        X = M[i:]
        X_cols = [X[:,i] for i in range(n)]
        u = map(lambda x: _dot_product(varbs_i, x), X_cols)
        return _dot_product(_vec(u[j:]), varbs_j)
    else:
        X = M[:i + 1]
        X_cols = [X[:,i] for i in range(n)]
        u = map(lambda x: _dot_product(varbs_i, x), X_cols)
        return _dot_product(_vec(u[:j + 1]), varbs_j)

# Given the polynomial ring P the dimension n, construct the top part of the 
# matrix to determine the cone conditions. 
def _build_mat(P, n, UT=True):
    M = [[0 for _ in range(k)] for k in range(n)]
    if UT: 
        merge = lambda x: _vec(
            x + list(_row_vector_vars(P, n, len(x)))
        )
    else:
        merge = lambda x: _vec(
            list(_row_vector_vars(P, n, n - len(x) - 1, UT=False)) + x
        )
        M = M[::-1]
    return map(merge, M)

# Given a tensor as a sequence of matrices, return the cone conditions 
# (assuming upper triangular).
def ConeConditions(t, upper_triangular=True):
    up = upper_triangular
    n = t[0].ncols()
    m = len(t)
    P = _Poly_ring(_QQ, (n + 1)*n//2, "X")

    # Build the matrix
    vecs = [[_multiply_rows(P, i, j, t[k], UT=up) 
        for k in range(m)] for i in range(n) for j in range(i, n)]
    top = _build_mat(P, n, UT=up)
    print vecs
    return _Mat(top + vecs)
