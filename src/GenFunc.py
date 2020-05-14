#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#


from sage.all import ceil as _ceil
from sage.all import expand as _expand
from sage.all import PolynomialRing as _PolynomialRing
from sage.all import symbolic_expression as _symb
from sage.all import var as _var
from sage.all import SR as _SR
from sage.all import QQ as _QQ
from sage.all import ZZ as _ZZ
from os import popen as _popen

# Given a polynomial f, returns the terms of f as polynomials in a list. 
def _get_terms(f, varbs):
    P = _PolynomialRing(_QQ, varbs, len(varbs))
    f_str = str(_expand(f)).replace(' ', '').replace('-', '+(-1)*')
    if f_str[0] == '+':
        f_str = f_str[1:]
    terms = f_str.split('+')
    induce = lambda x: P(x)
    return list(map(induce, terms))

# Return a string corresponding to f, written in ascending degree order. 
def _format_poly(f, varbs):
    terms = sorted(_get_terms(f, varbs), key=lambda g: g.total_degree())
    def addup(x, y):
        if str(y)[0] == "-":
            return x + " - " + str(-y).replace("*", "")
        else:
            return x + " + " + str(y).replace("*", "")
    return reduce(addup, terms[1:], str(terms[0]))

# Given a polynomial f, decide if it is a finite geometric series, and if so 
# return the numerator and denominator of the form (1 - r^n, 1 - r). We assume 
# that monomials are not finite geometric series.
def _is_fin_geo(f, varbs):
    terms = _get_terms(f, varbs)
    n = len(terms)
    if n == 1: 
        return (False, 0, 0)
    
    # Determine any constant factors
    a = terms[-1].coefficients()[0]
    assert a != 0
    P = _PolynomialRing(_QQ, varbs)
    check = lambda x: bool(_symb(f/x) in P)
    if a < 0:
        D = sorted(_ZZ(-a).divisors())[::-1]
        c = -filter(check, D)[0]
    else:
        D = sorted(_ZZ(a).divisors())[::-1]
        c = filter(check, D)[0]
    
    # Factor out the constant and check if it is already a finite geo series. 
    g = P(c**-1 * _symb(f))
    terms = _get_terms(1 - g, varbs)
    if len(terms) == 1:
        if terms[0].coefficients()[0] > 0:
            assert bool(f == g/c), "Something happened while determining geometric series."
            return (True, g, c)
        else: 
            assert bool(f == (1 - terms[0]**2)/(2 - g)), "Something happened while determining geometric series."
            return (True, 1 - terms[0]**2, 2 - g)
    
    # Now check if it could be one. 
    terms = _get_terms(g, varbs)
    tot_degs = list(map(lambda x: x.degree(), terms))
    sorted_degs, sorted_terms = zip(*sorted(zip(tot_degs, terms)))
    t = filter(lambda x: x.degree() == sorted_degs[1], terms)[0]
    pattern_check = lambda x: x[0] == t**(x[1])
    if all(map(pattern_check, zip(sorted_terms, range(n)))):
        assert bool(f == (1 - t**n)/(1 - t)), "Something happened while determining geometric series."
        return (True, 1 - t**n, 1 - t)
    return (False, 0, 0)



# Given two polynomials f, g, with f not equal to 0, decide if f/g is a 
# rational number by returning its rational quotient if f/g is rational. 
# Otherwise, 0 is returned.
def _decide_if_same(f, g):
    assert f != 0 and g != 0
    quo = (f/g).factor().simplify()
    if quo in _QQ:
        return _QQ(quo)
    return 0

# Given a list of factors, simplify them into like factors.
def _simplify_factors(fact_list):
    f = reduce(lambda x, y: x*y[0]**y[1], fact_list, 1)
    try:
        return list(_symb(f).factor_list())
    except AttributeError:
        return list([tuple([f, 1])])

# Given a numerator and a denominator, we apply two simplifications to the 
# data. First, we group together the same factors in the numerator. Second we 
# reduce factors that occur in both the numerator and the denominator. Here, we 
# do not require that the factors be exactly the same---only the same up to a 
# rational number. 
def _simplify(numer, denom):
    # Our sanity check
    merge = lambda X: reduce(lambda x, y: x*y[0]**y[1], X, 1)

    # First group similar terms together in the numerator and denominator
    sim_numer = _simplify_factors(numer)
    sim_denom = list(denom)

    # Reduce just the non-rational number factors of the numerator and 
    # denominator together
    i = 0
    while i < len(sim_numer) and not sim_numer[i][0] in _QQ:
        j = 0
        while j < len(sim_denom) and not sim_denom[j][0] in _QQ:
            const = _decide_if_same(sim_numer[i][0], sim_denom[j][0])
            if const != 0:
                diff = sim_numer[i][1] - sim_denom[j][1]
                if diff >= 0: # at least as many terms in numer
                    sim_numer[i] = [sim_numer[i][0], diff]
                    sim_denom[j] = [const**(sim_denom[j][1]), 1]
                else: # more terms in denom
                    sim_denom[j] = [sim_denom[j][0], -diff]
                    sim_numer[i] = [const**(sim_numer[i][1]), 1]
            j += 1
        i += 1

    # Split off the polynomial factors
    is_poly = lambda f: not f[0] in _QQ
    numer_final = filter(is_poly, sim_numer)
    denom_final = filter(is_poly, sim_denom)

    # Split off the rational factors
    is_rat = lambda f: f[0] in _QQ
    numer_rat = filter(is_rat, sim_numer)
    denom_rat = filter(is_rat, sim_denom)

    # Merge the rationals into one factor
    mult = lambda x, y: x*y[0]**y[1]
    rat_fact = _QQ(reduce(mult, numer_rat, 1) / reduce(mult, denom_rat, 1))

    # Incorporate rational factor
    if rat_fact.numerator() != 1:
        numer_final = [[rat_fact.numerator(), 1]] + numer_final
    if rat_fact.denominator() != 1:
        denom_final = [[rat_fact.denominator(), 1]] + denom_final

    assert bool(merge(numer)/merge(denom) == merge(numer_final)/merge(denom_final)), "Something happened while simplifying."

    return numer_final, denom_final


# Given the factor list of a polynomial and its variables, return a fraction of 
# geometric series.
def _simplify_to_finite_geo(d_facts, varbs):
    # Our sanity check
    merge = lambda X: reduce(lambda x, y: x*y[0]**y[1], X, 1)
    def convert(fact):
        data = _is_fin_geo(fact[0], varbs)
        if data[0]:
            return ([data[2], fact[1]], [data[1], fact[1]])
        return ([1, 1], fact)
    converted_facts = list(map(convert, d_facts))
    # Get the new data
    num_facts, denom_facts = zip(*converted_facts)
    assert bool(merge(d_facts) == merge(denom_facts)/merge(num_facts)), "Something happened in the finite geometric series function."
    return _simplify(num_facts, denom_facts)


# Given a polynomial f, write it as 
#   f = g * \prod_{i\in I} (1 - t^{a_i})/(1 - t^{b_i})
def _product_of_fin_geo(f):
    fl = f.factor_list()
    varbs = f.variables()
    merge = lambda X: reduce(lambda x, y: x*y[0]**y[1], X, 1)
    data = [[], []]
    new_data = [[(1, 0)], fl]
    while new_data[1] != data[1]:
        data = [data[0] + new_data[0], new_data[1]]
        new_data = _simplify_to_finite_geo(data[1], varbs)
    # Verify we haven't done something stupid at each step
    assert bool(f == merge(data[1])/merge(data[0]))
    return data

# Given a list of factors already in geo series form, find the best factor to 
# reduce by f. At this stage, we know f divides the numerator.
def _find_factor(denom_facts, f, P):
    varbs = P.gens()
    N = len(denom_facts)

    # First we decide if there is a rationally equivalent factor 
    for i in range(N):
        quo = _decide_if_same(denom_facts[i][0], f)
        if quo != 0:
            denom_facts[i][1] = denom_facts[i][1] - 1
            return quo, denom_facts

    # Now we look at the factors that are divisible by f and yield geo's
    for i in range(N):
        quo = denom_facts[i][0] / f
        if quo in P:
            geo_dat = _is_fin_geo(P(quo), varbs)
            if geo_dat[0] and geo_dat[2] in _QQ:
                denom_facts[i][1] = denom_facts[i][1] - 1
                for j in range(N):
                    if geo_dat[1] == denom_facts[j][0]:
                        denom_facts[j][1] = denom_facts[j][1] + 1
                        return geo_dat[2], denom_facts
                denom_facts += [[geo_dat[1], 1]]
                return geo_dat[2], denom_facts

    # Now we just look at the factors that are just divisible by f.
    for i in range(N):
        quo = denom_facts[i][0]/ f
        if quo in P:
            data = _product_of_fin_geo(quo)
            # TODO: Finish

    raise AssertionError("Something unexpected happened during formatting.")

# Given a denominator and data of two lists of factors corresponding to 
# numerator and denominator, clean up the data.
def _clean_denom_data(denom, data):
    merge = lambda X: reduce(lambda x, y: x*y[0]**y[1], X, 1)
    c = _decide_if_same(denom, merge(data[1]))
    if c != 0 :
        return data

    # In this case, we know that the data does not match the denominator
    P = _PolynomialRing(_QQ, denom.variables(), len(denom.variables()))
    f = merge(data[1])/denom
    if f in P:
        # Now we need to factor f out from both the denominator and numerator
        f = _symb(P(f))
        fl = f.factor_list()
        num_fact = 1
        denom_temp = data[1]
        for fact_dat in fl:
            g = fact_dat[0]
            for _ in range(fact_dat[1]):
                num, denom_temp = _find_factor(denom_temp, g, P)
                num_fact *= num
        numerator = (merge(data[0])*_symb(num_fact) / f).factor()
        return [numerator.factor_list(), denom_temp]
    else:
        raise AssertionError("Something unexpected happened while formatting.")


def _format(Z, denom=None, num_fact=False):
    # Clean up Z
    Z = Z.simplify()
    n = Z.numerator()
    d = Z.denominator()
    varbs = Z.variables()
    P = _PolynomialRing(_ZZ, varbs, len(varbs))

    # If it's a string do not change it.
    if isinstance(denom, str):
        denom_str = denom
        denom = _symb(denom)
    else: 
        denom_str = None
    
    # If there is a prescribed denominator, make sure we can handle it.
    given_denom = denom != None
    if given_denom:
        Q = denom/d
        if not Q in P: 
            raise ValueError("Expected the denominator to divide the prescribed denominator.")
        n *= P(Q)
    else:
        denom = d

    # Two steps now. Get the denominator into a nice form: a product of (1 - M),
    # where M is monomial, and second is to format the numerator. 
    # Step 1: denominator
    data = _product_of_fin_geo(denom)
    # If the denominator was prescribed, then we need to make sure we still 
    # match it
    if given_denom:
        clean_data = _clean_denom_data(denom, data)
    else:
        clean_data = data
    denom_facts = clean_data[1]
    numer_facts = n.factor_list() + clean_data[0]

    # Step 2: numerator
    numer_clean = _simplify_factors(numer_facts)

    # Now we build strings

    # Some functions
    cat = lambda X: reduce(lambda x, y: x + y, X, "")
    deg_key = lambda X: P(X[0]).total_degree()
    merge = lambda X: reduce(lambda x, y: x*y[0]**y[1], X, 1)

    # Given a tuple of the form (f, e), return a formatted string for the 
    # expression f^e.
    def _expo(tup):
        if tup[1] == 0 or tup[0] == 1:
            return ""
        else:
            if tup[1] == 1:
                return "(%s)" % (_format_poly(tup[0], varbs))
            else:
                return "(%s)^%s" % (_format_poly(tup[0], varbs), tup[1])
    
    # Last sanity check
    assert bool(merge(numer_clean) / merge(denom_facts) == Z), "Something went wrong with the formatting process at the end."

    # Format strings now
    if denom_str == None:
        denom_str = cat(map(_expo, sorted(denom_facts, key=deg_key)))
    if num_fact:
        numer_str = cat(map(_expo, sorted(numer_clean, key=deg_key)))
    else:
        numer_str = _format_poly(merge(numer_clean), varbs)

    return (numer_str, denom_str)


# Given a string of an expression, make the exponents LaTeX-friendly. 
def _TeX_exp(s):
    k = 0
    while k < len(s):
        if s[k] == "^":
            j = k + 1
            while j < len(s) and s[j].isdigit():
                j += 1
            if j - k > 2:
                s = s[:k+1] + "{" + s[k+1:j] + "}" + s[j:]
                k = j + 2
            else:
                k = j
        else:
            k += 1
    return s

def _TeX_output(F, 
    formatted=True, 
    LHS="", 
    numbered=False, 
    chars_per_line=80, 
    expression=False,
    print_out=True):

    if formatted:
        if F._fnumer == None:
            num, den = _format(F)
        else:
            num = F._fnumer
            den = F._fdenom
    else:
        num = F._numer
        den = F._denom
    denom_str = _TeX_exp(str(den).replace("*", " "))
    if len(denom_str) > chars_per_line:
        print "Warning: length of denominator exceeds chars_per_line."
    numer_str = _TeX_exp(str(num).replace("*", " "))
    if numbered:
        latex_str = "\\begin{equation}\\begin{aligned}\n"
    else:
        latex_str = "\\begin{align*}\n"
    if LHS == "":
        latex_str += "  Z"
    else:
        latex_str += "  " + LHS
    if len(F._vars) > 0:
        latex_str += "("
        for x in F._vars:
            latex_str += str(x) + ", "
        latex_str = latex_str[:-2] + ")"
    latex_str += " &= "
    express = "\\dfrac{" 
    
    # Determine if we need to break it up into multiple lines.
    lines = _ceil(len(numer_str)/chars_per_line)
    ind = 0
    if lines > 1:
        for k in range(lines):
            p_ind = numer_str[ind:(k+1)*chars_per_line].rfind("+")
            m_ind = numer_str[ind:(k+1)*chars_per_line].rfind("-")
            if p_ind > m_ind:
                express += numer_str[ind:ind+p_ind-1] + "}{" + denom_str + "} \\\\\n  &\\quad + \\dfrac{"
                ind += p_ind+2
            else:
                express += numer_str[ind:ind+m_ind-1] + "}{" + denom_str + "} \\\\\n  &\\quad + \\dfrac{"
                ind += m_ind
    express += numer_str[ind:] + "}{" + denom_str + "}"

    if expression:
        return express
    else:
        latex_str += express

    if numbered:
        latex_str += "\n\\end{aligned}\\end{equation}\n"
    else:
        latex_str += "\n\\end{align*}\n"

    if print_out:
        print latex_str[:-1]
    else:
        return latex_str


# A nicely formatted printing function. Inputs can be symbolic or strings.
def _format_print(num, den):
    num_l = len(str(num))
    num_d = len(str(den))
    m = max(num_l, num_d)
    _, cols = _popen('stty size', 'r').read().split()
    n = min(m, int(cols) - 1)
    line = "-"*n
    nspc = " "*max(0, (n - num_l)//2)
    dspc = " "*max(0, (n - num_d)//2)
    return "%s%s\n%s\n%s%s" % (nspc, num, line, dspc, den)


# My class of rational generating functions
class GenFunc():
    def __init__(self, *args):
        if len(args) == 0 or len(args) > 2:
            raise TypeError("Expected either 1 or 2 inputs.")
        if len(args) == 1:
            F = args[0].simplify()
            self._numer = F.numerator()
            self._denom = F.denominator()
        else:
            self._numer = args[0]
            self._denom = args[1]
        self._vars = (self._numer/self._denom).variables()
        self._fnumer = None
        self._fdenom = None

    def __repr__(self):
        if self._fnumer == None:
            num = self._numer
            den = self._denom
        else:
            num = self._fnumer
            den = self._fdenom
        return _format_print(num, den)

    def __add__(self, other):
        if isinstance(other, GenFunc):
            if self._fdenom != None and self._fdenom == other._fdenom:
                F = GenFunc(self._numer/self._denom + other._numer/other._denom)
                return F.format(denominator=_SR(
                    self._fdenom.replace('(', '*(')[1:]
                ))
            other = other._numer / other._denom
        return GenFunc(self._numer / self._denom + other)

    def __div__(self, other):
        if isinstance(other, GenFunc):
            other = other._numer / other._denom
        return GenFunc(self._numer / self._denom * other**-1)

    def __eq__(self, other):
        if isinstance(other, GenFunc): 
            other = other._numer / other._denom
        return bool(self._numer / self._denom == other)

    def __mul__(self, other):
        if isinstance(other, GenFunc):
            other = other._numer / other._denom
        return GenFunc(self._numer / self._denom * other)

    def denominator(self):
        return self._denom

    def denominator_format(self):
        return self._fdenom

    def factor(self):
        return GenFunc(self._numer.factor(), self._denom.factor())

    def format(self, numerator_factor=False, denominator=None):
        # Type checking
        if not isinstance(numerator_factor, bool):
            raise TypeError("Expected 'numerator_factor' to be a boolean.")
        
        n, d = _format(self, denom=denominator, num_fact=numerator_factor)
        self._fnumer = n
        self._fdenom = d
        return self

    def latex(self, formatted=True, LHS="", numbered=False, chars_per_line=80, expression=False):
        # Type checking
        if not isinstance(formatted, bool):
            raise TypeError("Expected 'formatted' to be a boolean.")
        if not isinstance(LHS, str):
            raise TypeError("Expected 'LHS' to be a string.")
        if not isinstance(numbered, bool):
            raise TypeError("Expected 'numbered' to be a boolean.")

        return _TeX_output(self, 
            formatted=formatted, 
            LHS=LHS, 
            numbered=numbered, 
            chars_per_line=chars_per_line, 
            expression=expression)

    def numerator(self):
        return self._numer

    def numerator_format(self):
        return self._fnumer

    def plain(self):
        return GenFunc(self._numer, self._denom)

    def reduced(self, X):
        # Make sure X makes sense 
        if not X in self._vars:
            raise ValueError("Expected variable to occur in rational function.")
        F = self._numer.subs({X : 1})/self._denom.subs({X : 1})
        R = GenFunc(F.simplify().factor().simplify())
        return R

    def simplify(self):
        f = (self._numer / self._denom).simplify().factor().simplify()
        return GenFunc(f)

    def subs(self, **kwargs):
        input_vars = map(lambda x: _var(x), kwargs.keys())
        if not all(map(lambda x: x in list(self._vars), input_vars)):
            raise ValueError("Unknown variable given.")
        cleaned_dict = {x : kwargs[str(x)] for x in input_vars}
        red_n = self._numer.subs(cleaned_dict)
        red_d = self._denom.subs(cleaned_dict)
        if red_d == 0:
            raise ValueError("Division by 0.")
        return GenFunc(red_n, red_d)

    def symbolic(self):
        return self._numer / self._denom

    def taylor(self, t, a, n):
        return (self._numer / self._denom).taylor(t, a, n)

    def variables(self):
        return self._vars
