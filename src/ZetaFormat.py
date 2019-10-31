#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from RatFunc import _get_terms
from RatFunc import RatFunc as _RatFunc

# Given a generating function Z, print the string that gets Z into a nicer 
# format than the simplified Sage version of Z. (We cannot return Z in this 
# nicer format because Sage will reduce and factor back to how it likes its 
# generating functions.)
def CleanZeta(Z, numerator_factor=False, denominator=None):
    F = _RatFunc(Z)
    return F.format(numerator_factor=numerator_factor, denominator=denominator)

# Given a generating function, return a LaTeX string that prints the given 
# rational function as an align environment. 
def LaTeX_Zeta(Z, numerator_factor=False, LHS="", numbered=False):
    F = _RatFunc(Z)
    return F.LaTeX(LHS="", numbered=numbered)

# Given a generating function Z, decide if it satisfies a functional equation 
# and return the (potential) functional equation. 
def FunctionalEquation(Z):
    v = Z.variables()
    subs = {x : x**-1 for x in v}
    inv_Z = Z.subs(subs)
    FE = inv_Z / Z
    FE_clean = FE.simplify().factor().simplify()
    numer, denom = FE_clean.numerator_denominator()
    if len(_get_terms(numer, v)) == 1 and len(_get_terms(denom, v)) == 1:
        return True, FE_clean
    return False, FE_clean