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

# Make sure we understand the input to the main functions.
def _input_check(word, leq_char, verbose, variable, sub):
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
    pass 

# Given a word and a leq_char, construct the matrix whose rows give the 
# inequalities for the Polyhedron function in Sage. 
def _build_ineqs(word, leq_char):
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
    return relations

def _eval_relations(relations, verbose, variable, sub):
    n = len(relations[0]) - 1

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


def ThinZeta_An(word, leq_char="0", verbose=False, variable='t', sub=True):
    # Make sure we understand the input.
    if isinstance(word, int) or isinstance(word, _Sage_int):
        word = str(word.binary()[1:])[::-1]
        if verbose:
            print word
    
    _input_check(word, leq_char, verbose, variable, sub)
    relations = _build_ineqs(word, leq_char)
    return _eval_relations(relations, verbose, variable, sub)


def ThinZeta_Dn(word, leq_char="0", verbose=False, variable='t', sub=True):
    # Make sure we understand the input.
    if isinstance(word, int) or isinstance(word, _Sage_int):
        word = str(word.binary()[1:])[::-1]
        if verbose:
            print word
    # If this should be type An instead, we use that function instead.
    if len(word) <= 2:
        return ThinZeta_An(word, leq_char=leq_char, verbose=verbose, variable=variable, sub=sub)
    _input_check(word, leq_char, verbose, variable, sub)
    # Finish this! 