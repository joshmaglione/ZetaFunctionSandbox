#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#

from sage.all import expand as _expand
from sage.all import PolynomialRing as _PolynomialRing
from sage.all import QQ as _QQ

# Given a polynomial f, returns the terms of f as polynomials in a list. 
def _get_terms(f):
    varbs = f.variables()
    P = _PolynomialRing(_QQ, varbs, len(varbs))
    f_str = str(_expand(f)).replace(' ', '').replace('-', '+(-1)*')
    if f_str[0] == '+':
        f_str = f_str[1:]
    terms = f_str.split('+')
    induce = lambda x: P(x)
    return list(map(induce, terms))

# Given a polynomial f, decide if it is a finite geometric series, and if so 
# return the numerator and denominator of the form (1 - r^n, 1 - r). We assume 
# that monomials are not finite geometric series.
def _is_fin_geo(f):
    terms = _get_terms(f)
    n = len(terms)
    if n == 1: 
        return (False, 0, 0)
    tot_degs = list(map(lambda x: x.degree(), terms))
    sorted_degs, sorted_terms = zip(*sorted(zip(tot_degs, terms)))
    t = filter(lambda x: x.degree() == sorted_degs[1], terms)[0]
    pattern_check = lambda x: x[0] == t**(x[1])
    if all(map(pattern_check, zip(sorted_terms, range(n)))):
        return (True, 1 - t**n, 1 - t)
    return (False, 0, 0)

# Given a numerator and a denominator, we apply two simplifications to the 
# data. First, we group together the same factors in the numerator. Second we 
# reduce factors that occur in both the numerator and the denominator. Here, we 
# do not require that the factors be exactly the same---only the same up to a 
# rational number. 
def _simplify(numer, denom):
    # First group similar terms together in the numerator
    i = 0 
    sim_numer = list(numer)
    while i < len(sim_numer):
        j = i + 1
        while j < len(sim_numer):
            if sim_numer[i][0] == sim_numer[j][0]:
                sim_numer[i][1] += sim_numer[j][1]
                sim_numer[j] = [1, 0]
            j += 1
        i += 1
    # Reduce the numerator and denominator together
    i = 0
    sim_denom = list(denom)
    while i < len(sim_numer):
        j = 0
        while j < len(sim_denom):
            quo = sim_numer[i][0]/sim_denom[j][0]
            if quo in _QQ:
                const = quo
            else:
                const = 0
            if const != 0:
                diff = sim_numer[i][1] - sim_denom[j][1]
                if diff >= 0:
                    sim_numer[i] = [(const**diff)*sim_numer[i][0], diff]
                    sim_denom[j] = [1, 0]
                else:
                    sim_denom[j] = [(const**(-diff))*sim_denom[j][0], -diff]
                    sim_numer[i] = [1, 0]
            j += 1
        i += 1
    return sim_numer, sim_denom


def _good_gen_func_format(Z, num_fact=False):
    # Clean up Z
    f = Z.simplify().factor().simplify()
    n, d = f.numerator_denominator()
    d_facts = d.factor_list()
    # A function to convert the factors in the denominator to fin geo quotients
    def convert(fact):
        data = _is_fin_geo(fact[0])
        if data[0]:
            return ([data[2], fact[1]], [data[1], fact[1]])
        return ([1, 1], fact)
    converted_facts = list(map(convert, d_facts))
    # Get the new data
    num_facts, denom_facts = zip(*converted_facts)
    clean_num, clean_denom = _simplify(num_facts, denom_facts)
    # Build strings
    cat = lambda x, y: x + y
    def exponentiate(tup):
        if tup[1] == 0 or tup[0] == 1:
            return ""
        else:
            if tup[1] == 1:
                return "(%s)" % (tup[0])
            else:
                return "(%s)^%s" % (tup[0], tup[1])
    if num_fact:
        if n == 1:
            old_numer = ""
        else:
            old_numer = "(%s)" % (n)
        new_numer = old_numer + reduce(cat, map(exponentiate, clean_num), "")
        if new_numer == "":
            new_numer = "1"
    else:
        P = _PolynomialRing(_QQ, Z.variables(), len(Z.variables()))
        mult = lambda x, y: x*y
        new_numer = reduce(mult, map(lambda x: P(x[0])**(x[1]), clean_num), 1)
        new_numer = _expand(n * new_numer)
    new_denom = reduce(cat, map(exponentiate, clean_denom), "")
    if new_denom == "":
        new_denom = "1"
    return (new_numer, new_denom)

# Given a string of an expression, make the exponents TeX-friendly. 
def _TeX_exp(s):
    k = 0
    while k < len(s):
        if s[k] == "^":
            i = s.find("*", k)
            j = s.find(" ", k)
            l = s.find("(", k+1)
            inds = filter(lambda x: x != -1, [i, j, l])
            if inds == []:
                s = s[:k+1] + "{" + s[k+1:] + "}"
                k = len(s)
            else:
                m = min(inds)
                s = s[:k+1] + "{" + s[k+1:m] + "}" + s[m:]
                k = m + 2
        else:
            k += 1
    return s

# Given a generating function Z, print the string that gets Z into a nicer 
# format than the simplified Sage version of Z. (We cannot return Z in this 
# nicer format because Sage will reduce and factor back to how it likes its 
# generating functions.)
def CleanZeta(Z, numerator_factor=False):
    new_numer, new_denom = _good_gen_func_format(Z, num_fact=numerator_factor)
    print "Numerator:\n%s\n\nDenominator:\n%s" % (new_numer, new_denom)
    return new_numer, new_denom

# Given a generating function, return a LaTeX string that prints the given 
# rational function as an align environment. 
def TeX_Zeta(Z, numerator_factor=False, LHS="", numbered=False):
    new_numer, new_denom = _good_gen_func_format(Z, num_fact=numerator_factor)
    denom_str = _TeX_exp(new_denom.replace("*", " "))
    numer_str = _TeX_exp(str(new_numer).replace("*", " "))
    varbs = Z.variables()
    if numbered:
        latex_str = "\\begin{align}\n"
    else:
        latex_str = "\\begin{align*}\n"
    if LHS == "":
        latex_str += "  Z("
    else:
        latex_str += "  " + LHS + "("
    for x in varbs:
        latex_str += str(x) + ", "
    latex_str = latex_str[:-2] + ") &= \\dfrac{" 
    latex_str += numer_str + "}{" + denom_str + "}"
    if numbered:
        latex_str += "\n\\end{align}\n"
    else:
        latex_str += "\n\\end{align*}\n"
    return latex_str


# Given a generating function Z, decide if it satisfies a functional equation 
# and return the (potential) functional equation. 
def FunctionalEquation(Z):
    varbs = Z.variables()
    subs = {x : x**-1 for x in varbs}
    inv_Z = Z.subs(subs)
    FE = inv_Z / Z
    FE_clean = FE.simplify().factor().simplify()
    numer, denom = FE_clean.numerator_denominator()
    if len(_get_terms(numer)) == 1 and len(_get_terms(denom)) == 1:
        return True, FE_clean
    return False, FE_clean