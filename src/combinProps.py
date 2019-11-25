#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from GenFunc import _get_terms
from GenFunc import GenFunc as _GenFunc
from sage.all import symbolic_expression as _symb
from sage.all import RR as _RR
from sage.all import PolynomialRing as _PolyRing

# Given a rational function Z, decide if it satisfies a functional equation 
# and return the (potential) functional equation. 
def FunctionalEquation(Z):
    if isinstance(Z, _GenFunc):
        Z = Z._numer/Z._denom
    v = Z.variables()
    subs = {x : x**-1 for x in v}
    inv_Z = Z.subs(subs)
    FE = inv_Z / Z
    FE_clean = FE.simplify().factor().simplify()
    numer, denom = FE_clean.numerator_denominator()
    if len(_get_terms(numer, v)) == 1 and len(_get_terms(denom, v)) == 1:
        return True, FE_clean
    return False, FE_clean

# Given a rational function Z, return information about its nonnegative 
# numerator. We require Z to be univariate and an instance of GenFunc. This 
# will help make things smoother.
def NonnegativityData(Z):
    if not isinstance(Z, _GenFunc):
        raise TypeError("Expected a rational function (class GenFunc).")
    if len(Z._vars) > 1:
        raise ValueError("Expected a univariate rational function.")
    if Z._fnumer == None:
        numer = str(Z._numer)
    else:
        numer = Z._fnumer
    coeffs = _symb(numer).coefficients()

    # First test: check everything is nonnegative
    is_neg = lambda x: x[0] < 0
    if any(filter(is_neg, coeffs)):
        print "Numerator is not nonnegative."
        return None

    # Our record
    nonneg_data = {
        "Gamma-nonnegative" : None,
        "Log-concave" : None,
        "Palindromic" : None,
        "Real-rooted" : None,
        "Unimodular" : None
    }

    # Normalize the data
    shift = coeffs[0][1]
    inflat_coeffs = []
    for k in range(len(coeffs)):
        inflat_coeffs.append(coeffs[k][0]) 
        if k < len(coeffs) - 1:
            d = coeffs[k+1][1] - coeffs[k][1] - 1
            inflat_coeffs += [0 for _ in range(d)]
    n = len(inflat_coeffs)

    # Check if palindromic
    palin = zip(inflat_coeffs[::-1], inflat_coeffs[:(n + 1)//2])
    if all(map(lambda x: x[0] == x[1], palin)):
        nonneg_data["Palindromic"] = True
    else:
        nonneg_data["Gamma-nonnegative"] = False
        nonneg_data["Log-concave"] = False
        nonneg_data["Palindromic"] = False

    # Check if Real-rooted
    f = _PolyRing(_RR, Z._vars[0])(_symb(numer))
    roots = f.roots()
    count = reduce(lambda x, y: x + y, map(lambda x: x[1], roots), 0)
    if count == n + shift:
        nonneg_data["Real-rooted"] = True
        if nonneg_data["Palindromic"]:
            nonneg_data["Gamma-nonnegative"] = True
            nonneg_data["Log-concave"] = True
            nonneg_data["Unimodular"] = True
    else:
        nonneg_data["Real-rooted"] = False

    # Check if unimodular
    if nonneg_data["Unimodular"] == None:
        m = max(inflat_coeffs)
        k = inflat_coeffs.index(m)
        lhs = inflat_coeffs[:k+1]
        rhs = inflat_coeffs[k:]
        lhs_sorted = [k for k in lhs]
        rhs_sorted = [k for k in rhs]
        lhs_sorted.sort()
        rhs_sorted.sort()
        if lhs == lhs_sorted and rhs[::-1] == rhs_sorted:
            nonneg_data["Unimodular"] = True
        else:
            nonneg_data["Gamma-nonnegative"] = False
            nonneg_data["Log-concave"] = False
            nonneg_data["Real-rooted"] = False
            nonneg_data["Unimodular"] = False
        
    # Check if Log-concave
    if nonneg_data["Log-concave"] == None: 
        log_test = lambda A, k: bool(A[k]**2 >= A[k - 1]*A[k + 1])
        if all(log_test(inflat_coeffs, k) for k in range(1, n - 1)):
            nonneg_data["Log-concave"] = True
        else: 
            nonneg_data["Log-concave"] = False

    # Check if Gamma-nonnegative
    if nonneg_data["Gamma-nonnegative"] == None: 
        pass
        # TODO: Finish this!

    return nonneg_data