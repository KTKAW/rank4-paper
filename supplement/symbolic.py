"""Symbolic rank-four quivers: tuples of polynomials, mutation under certified sign hypotheses,
Markov values and Pfaffians, and sign-pattern enumeration.

Mutation is piecewise polynomial: b'_ij = b_ij + [b_ik]_+[b_kj]_+ - [-b_ik]_+[-b_kj]_+.
On a set where each entry incident to k has a known weak sign, it is a polynomial. A symbolic
mutation therefore needs, for each entry b_ik (i != k), a proof that b_ik >= 0 or b_ik <= 0 on
the case under consideration; these proofs are positivity certificates (see certificates.py).
At b_ik = 0 both formulas agree, so weak signs suffice.
"""
from itertools import combinations, product
from polynomial import Poly
import quiver4 as Q

PAIRS = Q.PAIRS


def as_poly_tuple(t):
    return tuple(Poly.coerce(x) for x in t)


def sentry(t, i, j):
    if i == j:
        return Poly()
    if i < j:
        return t[PAIRS.index((i, j))]
    return -t[PAIRS.index((j, i))]


def incident_entries(t, k):
    """[(i, b_ik)] for the three vertices i != k, in increasing order of i (None if unknown)."""
    return [(i, sentry_or_none(t, i, k)) for i in Q.VERTICES if i != k]


def sentry_or_none(t, i, j):
    if i == j:
        return Poly()
    x = t[PAIRS.index((i, j))] if i < j else t[PAIRS.index((j, i))]
    if x is None:
        return None
    return x if i < j else -x


def smutate(t, k, signs):
    """Mutate the polynomial tuple t at vertex k. `signs` maps each i != k to '+' (b_ik >= 0),
    '-' (b_ik <= 0) or '?' (unknown); the caller is responsible for having certified the known
    signs. An entry whose new value depends on an unknown sign becomes None (unknown), and so
    does any entry that was already unknown, except those incident to k, which only change sign."""
    new = {}
    for (i, j) in PAIRS:
        old = sentry_or_none(t, i, j)
        if k in (i, j):
            new[(i, j)] = None if old is None else -old
            continue
        if old is None or signs[i] == '?' or signs[j] == '?':
            new[(i, j)] = None
            continue
        bik, bkj = sentry_or_none(t, i, k), sentry_or_none(t, k, j)
        si, sj = signs[i], ('-' if signs[j] == '+' else '+')   # sign of b_kj = -b_jk
        if si == '+' and sj == '+':
            corr = bik * bkj
        elif si == '-' and sj == '-':
            corr = -(bik * bkj)
        else:
            corr = Poly()
        new[(i, j)] = old + corr
    return tuple(new[p] for p in PAIRS)


def srelabel(t, pi):
    return tuple(sentry(t, pi[i - 1], pi[j - 1]) for i, j in PAIRS)


def sreverse(t):
    return tuple(-x for x in t)


def smarkov(t, order):
    v = tuple(order)
    a, b, c = sentry(t, v[0], v[1]), sentry(t, v[0], v[2]), sentry(t, v[0], v[3])
    d, e = sentry(t, v[1], v[2]), sentry(t, v[1], v[3])
    f = sentry(t, v[2], v[3])
    return a * a + b * b + c * c + d * d + e * e + f * f + a * b * d + a * c * e + b * c * f + d * e * f + a * c * d * f


def spfaffian(t):
    a, b, c, d, e, f = t
    return a * f - b * e + c * d


# ----------------------------------------------------------------------------- sign patterns
SIGN_SETS = {"+": (1,), "-": (-1,), "0": (0,), "+0": (0, 1), "-0": (-1, 0), "+-": (-1, 1), "*": (-1, 0, 1)}


def sign_patterns(spec):
    """spec: 6 strings from SIGN_SETS (one per entry b12..b34). Yields tuples of -1/0/1."""
    return product(*[SIGN_SETS[s] for s in spec])


def pattern_property(pattern, prop):
    """Evaluate a sign-only property on the representative quiver with entries in {-1,0,1}.
    Valid because wiggle classes, properness, acyclicity, vortices and directed triangles
    depend only on the signs of the entries."""
    q = tuple(int(s) for s in pattern)
    return prop(q)
