#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from sage.all import Matrix as _Matrix
from sage.all import Polyhedron as _Polyhedron
from sage.all import PolynomialRing as _PolynomialRing
from sage.all import QQ as _QQ
from sage.all import var as _var
from sage.rings.integer import Integer as _Sage_int
from Zeta.smurf import SMURF as _Zeta_smurf

def ThinZeta_An(word, leq_char="0", verbose=False, variable='t', sub=True):
    # Make sure we understand the input.
    if isinstance(word, int) or isinstance(word, _Sage_int):
        word = str(word.binary()[1:])[::-1]
        if verbose:
            print word
    if not isinstance(word, str):
        raise TypeError('Expected the word to be a string.')
    if len({w for w in word}) > 2:
        raise ValueError('Expected word to be a 2-letter alphabet.')
    if not isinstance(leq_char, str):
        raise TypeError('Expected leq_char to be a string.')
    if not isinstance(verbose, bool):
        raise TypeError('Expected "verbose" to be either True or False.')
    if not isinstance(variable, str):
        raise TypeError('Expected "variable" to be a string.')
    
    # Initial values.
    n = len(word) + 1
    relations = []
    zero_vec = tuple([0 for i in range(n + 1)]) 

    # Basic function: add k to the i-th component of v.
    def add_k_i(v, i, k):
        u = list(v)
        u[i] += k
        return tuple(u)

    # nonnegative relations.
    relations += [add_k_i(zero_vec, i, 1) for i in range(1, n + 1)]

    # word relations.
    if n > 1:
        for x in zip(word, range(1, n)):
            if x[0] == leq_char:
                v = add_k_i(zero_vec, x[1], -1)
                u = add_k_i(v, x[1] + 1, 1)
            else:
                v = add_k_i(zero_vec, x[1], 1)
                u = add_k_i(v, x[1] + 1, -1)
            relations.append(u)

    # In case the user wants to verify the matrix.
    if verbose:
        print "The matrix corresponding to the polyhedral cone:"
        print "%s" % (_Matrix(relations))
    
    # Define the polyhedral cone and corresponding polynomial ring.
    P = _Polyhedron(ieqs=relations)
    R = _PolynomialRing(_QQ, 'x', n)

    # Define substitution.
    if sub:
        t = _var(variable)
        if n > 1:
            subs = {_var('x' + str(i)) : t for i in range(n)}
        else:
            subs = {_var('x') : t}
        # Apply Zeta
        sm = _Zeta_smurf.from_polyhedron(P, R)
        Z = sm.evaluate().subs(subs).factor().simplify()
    else:
        # Apply Zeta
        sm = _Zeta_smurf.from_polyhedron(P, R)
        Z = sm.evaluate().factor().simplify()

    return Z
