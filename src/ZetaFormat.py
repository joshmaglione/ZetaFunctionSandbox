#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

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
