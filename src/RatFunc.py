#
#   Copyright 2019 Joshua Maglione 
#
#   Distributed under MIT License
#


from sage.all import ceil as _ceil
from sage.all import expand as _expand
from sage.all import PolynomialRing as _PolynomialRing
from sage.all import symbolic_expression as _symb
from sage.all import QQ as _QQ
from sage.all import ZZ as _ZZ
from os import popen as _popen

# Given a polynomial f, returns the terms of f as polynomials in a list. 
def _get_terms(f, varbs):
    P = _PolynomialRing(_ZZ, varbs, len(varbs))
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
            return x + " - " + str(-y)
        else:
            return x + " + " + str(y)
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
            return (True, g, c)
        else: 
            return (True, 1 - terms[0]**2, 2 - g)
    
    # Now check if it could be one. 
    terms = _get_terms(g, varbs)
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

def _simplify_to_finite_geo(d_facts, varbs):
    def convert(fact):
        data = _is_fin_geo(fact[0], varbs)
        if data[0]:
            return ([data[2], fact[1]], [data[1], fact[1]])
        return ([1, 1], fact)
    converted_facts = list(map(convert, d_facts))
    # Get the new data
    num_facts, denom_facts = zip(*converted_facts)
    return _simplify(num_facts, denom_facts)

def _good_format_denom(Z, denom, num_fact=False):
    # Clean up Z
    Z = Z.simplify()
    n = Z.numerator()
    d = Z.denominator()

    numer = (denom / d).simplify().factor().simplify()
    if not numer in _QQ:
        assert numer in _PolynomialRing(_QQ, numer.variables()), "Expected denominator to divide given denominator."
    n *= numer
    d = denom
    d_facts = d.factor_list()
    varbs = Z.variables()
    clean_num1, inter_denom = _simplify_to_finite_geo(d_facts, varbs)
    clean_num2, clean_denom = _simplify_to_finite_geo(inter_denom, varbs)
    mult = lambda x, y: x*y
    P = _PolynomialRing(_ZZ, Z.variables(), len(Z.variables()))

    # Divide out the numerator. Something must factor. 
    new_fact1 = reduce(mult, map(lambda x: P(x[0])**(x[1]), clean_num1), 1)
    new_fact2 = reduce(mult, map(lambda x: P(x[0])**(x[1]), clean_num2), 1)
    new_fact = new_fact1 * new_fact2
    if new_fact != 1:
        k = 0
        cont = True
        while k < len(clean_denom) and cont:
            f = clean_denom[k][0] / new_fact
            if f in P:
                T = _is_fin_geo(P(f), Z.variables())
                if T[0] and T[2] == 1:
                    clean_denom[k][1] -= 1
                    clean_denom += [[T[1], 1]]
                    cont = False
            k += 1
    
    # Build strings
    cat = lambda x, y: x + y
    def exponentiate(tup):
        if tup[1] == 0 or tup[0] == 1:
            return ""
        else:
            if tup[1] == 1:
                return "(%s)" % (_format_poly(tup[0], Z.variables()))
            else:
                return "(%s)^%s" % (_format_poly(tup[0], Z.variables()), tup[1])
    if num_fact:
        if n == 1:
            old_numer = ""
        else:
            old_numer = "(%s)" % (_format_poly(n, Z.variables()))
    else:
        new_numer = _format_poly(_expand(n), Z.variables())
    clean_denom = sorted(clean_denom, key=lambda X: P(X[0]).total_degree())
    new_denom = reduce(cat, map(exponentiate, clean_denom), "")
    return (new_numer.replace("*", ""), new_denom)


def _good_gen_func_format(Z, num_fact=False):
    # Clean up Z
    Z = Z.simplify()
    n = Z.numerator()
    d = Z.denominator()
    d_facts = d.factor_list()

    # A function to convert the factors in the denominator to fin geo quotients
    def convert(fact):
        data = _is_fin_geo(fact[0], Z.variables())
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
                return "(%s)" % (_format_poly(tup[0], Z.variables()))
            else:
                return "(%s)^%s" % (_format_poly(tup[0], Z.variables()), tup[1])
    if num_fact:
        if n == 1:
            old_numer = ""
        else:
            old_numer = "(%s)" % (_format_poly(n, Z.variables()))
        new_numer = old_numer + reduce(cat, map(exponentiate, clean_num), "")
        if new_numer == "":
            new_numer = "1"
    else:
        P = _PolynomialRing(_QQ, Z.variables(), len(Z.variables()))
        mult = lambda x, y: x*y
        new_numer = reduce(mult, map(lambda x: P(x[0])**(x[1]), clean_num), 1)
        new_numer = _format_poly(_expand(n * new_numer), Z.variables())
    new_denom = reduce(cat, map(exponentiate, clean_denom), "")
    if new_denom == "":
        new_denom = "1"
    return (new_numer.replace("*", ""), new_denom)

# Given a string of an expression, make the exponents LaTeX-friendly. 
def _TeX_exp(s):
    k = 0
    while k < len(s):
        if s[k] == "^":
            i = s.find("*", k)
            j = s.find(" ", k)
            a = s.find("(", k+1)
            b = s.find(")", k+1)
            inds = filter(lambda x: x != -1, [i, j, a, b])
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


# My class of rational functions
class RatFunc():
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
        self._vars = tuple(set(self._numer.variables()).union(
            set(self._denom.variables())))
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

    def numerator(self):
        return self._numer

    def numerator_format(self):
        return self._fnumer

    def denominator(self):
        return self._denom

    def denominator_format(self):
        return self._fdenom

    def variables(self):
        return self._vars

    def factor(self):
        return RatFunc(self._numer.factor(), self._denom.factor())

    def simplify(self):
        f = (self._numer / self._denom).simplify().factor().simplify()
        return RatFunc(f)

    def plain(self):
        print _format_print(self._numer, self._denom)
        pass

    def format(self, numerator_factor=False, denominator=None):
        # Type checking
        if not isinstance(numerator_factor, bool):
            raise TypeError("Expected 'numerator_factor' to be a boolean.")
        if denominator == None:
            n, d = _good_gen_func_format(self, num_fact=numerator_factor)
        else:
            n, d = _good_format_denom(self, denominator, num_fact=numerator_factor)
        self._fnumer = n
        self._fdenom = d
        return self

    def reduced(self, X):
        # Make sure X makes sense 
        if not X in self._vars:
            raise ValueError("Expected variable to occur in rational function.")
        F = self._numer.subs({X : 1})/self._denom.subs({X : 1})
        R = RatFunc(F.simplify().factor().simplify())
        return R

    def LaTeX(self, formatted=True, LHS="", numbered=False, chars_per_line=60):
        # Type checking
        if not isinstance(formatted, bool):
            raise TypeError("Expected 'formatted' to be a boolean.")
        if not isinstance(LHS, str):
            raise TypeError("Expected 'LHS' to be a string.")
        if not isinstance(numbered, bool):
            raise TypeError("Expected 'numbered' to be a boolean.")

        if formatted:
            if self._fnumer == None:
                num, den = _good_gen_func_format(self)
            else:
                num = self._fnumer
                den = self._fdenom
        else:
            num = self._numer
            den = self._denom
        denom_str = _TeX_exp(str(den).replace("*", " "))
        numer_str = _TeX_exp(str(num).replace("*", " "))
        if numbered:
            latex_str = "\\begin{equation}\\begin{aligned}\n"
        else:
            latex_str = "\\begin{align*}\n"
        if LHS == "":
            latex_str += "  Z("
        else:
            latex_str += "  " + LHS + "("
        for x in self._vars:
            latex_str += str(x) + ", "
        latex_str = latex_str[:-2] + ") &= \\dfrac{" 
        
        # Determine if we need to break it up into multiple lines.
        lines = _ceil(len(numer_str)/chars_per_line)
        ind = 0
        for k in range(lines - 1):
            p_ind = numer_str[ind:(k+1)*chars_per_line].rfind("+")
            m_ind = numer_str[ind:(k+1)*chars_per_line].rfind("-")
            if p_ind > m_ind:
                latex_str += numer_str[ind:ind+p_ind-1] + "}{" + denom_str + "} \\\\\n  &\\quad + \\dfrac{"
                ind += p_ind+2
            else:
                latex_str += numer_str[ind:ind+m_ind-1] + "}{" + denom_str + "} \\\\\n  &\\quad + \\dfrac{"
                ind += m_ind
        latex_str += numer_str[ind:] + "}{" + denom_str + "}"

        if numbered:
            latex_str += "\n\\end{aligned}\\end{equation}\n"
        else:
            latex_str += "\n\\end{align*}\n"
        return latex_str