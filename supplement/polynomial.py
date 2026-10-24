"""Exact sparse multivariate polynomials with rational coefficients.

Standard library only. Coefficients are fractions.Fraction, so there is no rounding and no
overflow. A monomial is a tuple of (variable_name, exponent) pairs sorted by name.
"""
from fractions import Fraction
import numbers

__all__ = ["Poly", "V", "const"]


def _mono_mul(m1, m2):
    exps = dict(m1)
    for v, e in m2:
        exps[v] = exps.get(v, 0) + e
    return tuple(sorted((v, e) for v, e in exps.items() if e))


class Poly:
    """Immutable-by-convention polynomial. Use V('x') for a variable and ints for constants."""

    __slots__ = ("terms",)

    def __init__(self, terms=None):
        clean = {}
        if terms:
            for mono, c in terms.items():
                c = Fraction(c)
                if c:
                    clean[mono] = clean.get(mono, 0) + c
            clean = {m: c for m, c in clean.items() if c}
        self.terms = clean

    # ------------------------------------------------------------------ construction
    @staticmethod
    def coerce(x):
        if isinstance(x, Poly):
            return x
        if isinstance(x, (numbers.Rational,)):
            return Poly({(): Fraction(x)})
        raise TypeError("cannot use %r as a polynomial (floats are not allowed)" % (x,))

    # ------------------------------------------------------------------ arithmetic
    def __add__(self, other):
        other = Poly.coerce(other)
        t = dict(self.terms)
        for m, c in other.terms.items():
            t[m] = t.get(m, 0) + c
        return Poly(t)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly.coerce(other))

    def __rsub__(self, other):
        return Poly.coerce(other) - self

    def __mul__(self, other):
        other = Poly.coerce(other)
        t = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                m = _mono_mul(m1, m2)
                t[m] = t.get(m, 0) + c1 * c2
        return Poly(t)

    __rmul__ = __mul__

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError("only nonnegative integer powers")
        r = Poly.coerce(1)
        for _ in range(n):
            r = r * self
        return r

    def __eq__(self, other):
        try:
            other = Poly.coerce(other)
        except TypeError:
            return NotImplemented
        return (self - other).terms == {}

    def __ne__(self, other):
        r = self.__eq__(other)
        return r if r is NotImplemented else not r

    def __hash__(self):
        return hash(frozenset(self.terms.items()))

    # ------------------------------------------------------------------ queries
    def is_zero(self):
        return not self.terms

    def is_constant(self):
        return all(m == () for m in self.terms)

    def constant(self):
        return self.terms.get((), Fraction(0))

    def variables(self):
        return sorted({v for m in self.terms for v, _ in m})

    def degree(self):
        return max((sum(e for _, e in m) for m in self.terms), default=0)

    def has_integer_coefficients(self):
        return all(c.denominator == 1 for c in self.terms.values())

    def evaluate(self, values):
        total = Fraction(0)
        for m, c in self.terms.items():
            term = c
            for v, e in m:
                term *= Fraction(values[v]) ** e
            total += term
        return total

    def substitute(self, mapping):
        """Replace variables by polynomials (or numbers)."""
        mapping = {k: Poly.coerce(v) for k, v in mapping.items()}
        out = Poly()
        for m, c in self.terms.items():
            term = Poly({(): c})
            for v, e in m:
                term = term * (mapping[v] ** e if v in mapping else Poly({((v, e),): 1}))
            out = out + term
        return out

    def __repr__(self):
        if not self.terms:
            return "0"
        parts = []
        for m in sorted(self.terms, key=lambda m: (-sum(e for _, e in m), m)):
            c = self.terms[m]
            mono = "*".join(v if e == 1 else "%s^%d" % (v, e) for v, e in m)
            if not mono:
                parts.append(str(c))
            elif c == 1:
                parts.append(mono)
            elif c == -1:
                parts.append("-" + mono)
            else:
                parts.append("%s*%s" % (c, mono))
        return " + ".join(parts).replace("+ -", "- ")


def V(name):
    return Poly({((name, 1),): 1})


def const(c):
    return Poly.coerce(c)
