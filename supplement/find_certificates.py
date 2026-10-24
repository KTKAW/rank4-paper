"""Search for positivity certificates by linear programming (development tool).

This module is NOT needed to verify the paper: the certificates it finds are written to
certificates.json and checked exactly by certificates.check_certificate, which uses only the
standard library. Here we use scipy's HiGHS solver to find candidate certificates, then
reconstruct exact rational coefficients and verify them exactly before saving.
"""
from fractions import Fraction
from itertools import combinations_with_replacement
from polynomial import Poly
from certificates import check_certificate, CertificateError

try:
    import numpy as np
    from scipy.optimize import linprog
except ImportError:  # pragma: no cover
    np = None
    linprog = None


def _monomials_upto(variables, deg):
    out = [()]
    for d in range(1, deg + 1):
        for combo in combinations_with_replacement(variables, d):
            exps = {}
            for v in combo:
                exps[v] = exps.get(v, 0) + 1
            out.append(tuple(sorted(exps.items())))
    return out


def find_certificate(hyps, eqs, goal, depth=2, hints=(), hint_times_hyps=True,
                     extra_terms=(), eq_mult_deg=None, max_terms=60000):
    """Return an exact certificate dict or None.

    hyps: dict name -> Poly (>= 0); eqs: dict name -> Poly (== 0)
    goal: ("ge0", g) | ("contra",)
    depth: products of up to `depth` hypotheses are candidate terms
    hints: polynomials s whose squares s^2 are candidate terms (optionally times one hypothesis)
    extra_terms: list of (tuple_of_hyp_names, sq_poly_or_None) added verbatim
    """
    if linprog is None:
        raise RuntimeError("scipy is required to search for certificates")
    names = sorted(hyps)
    cands = []  # (hyps tuple, sq)
    for d in range(1, depth + 1):
        for combo in combinations_with_replacement(names, d):
            cands.append((combo, None))
    for s in hints:
        cands.append(((), s))
        if hint_times_hyps:
            for n in names:
                cands.append(((n,), s))
    cands.extend(extra_terms)
    if len(cands) > max_terms:
        raise RuntimeError("too many candidate terms (%d)" % len(cands))
    polys = []
    for hs, sq in cands:
        p = Poly.coerce(1)
        for h in hs:
            p = p * hyps[h]
        if sq is not None:
            p = p * sq * sq
        polys.append(p)
    g = Poly.coerce(-1) if goal[0] == "contra" else goal[1]
    allvars = sorted(set(g.variables()).union(*[set(p.variables()) for p in polys])
                     .union(*[set(e.variables()) for e in eqs.values()]))
    eq_terms = []
    if eqs:
        maxdeg = max([g.degree()] + [p.degree() for p in polys])
        for en, e in sorted(eqs.items()):
            md = eq_mult_deg if eq_mult_deg is not None else max(0, maxdeg - e.degree())
            for mono in _monomials_upto(allvars, md):
                eq_terms.append((en, Poly({mono: 1})))
    # monomial index
    mono_index = {}

    def idx(m):
        if m not in mono_index:
            mono_index[m] = len(mono_index)
        return mono_index[m]

    cols = []
    for p in polys:
        cols.append({idx(m): float(c) for m, c in p.terms.items()})
    for en, mult in eq_terms:
        q = mult * eqs[en]
        cols.append({idx(m): float(c) for m, c in q.terms.items()})
    cols.append({idx(()): 1.0})  # the constant
    for m in g.terms:
        idx(m)
    nrow, ncol = len(mono_index), len(cols)
    from scipy.sparse import lil_matrix
    A = lil_matrix((nrow, ncol))
    for j, col in enumerate(cols):
        for i, v in col.items():
            A[i, j] = v
    b = np.zeros(nrow)
    for m, c in g.terms.items():
        b[mono_index[m]] = float(c)
    npoly = len(polys)
    neq = len(eq_terms)
    bounds = [(0, None)] * npoly + [(None, None)] * neq + [(0, None)]
    cost = np.concatenate([np.ones(npoly), np.zeros(neq), np.zeros(1)])
    res = linprog(cost, A_eq=A.tocsr(), b_eq=b, bounds=bounds, method="highs")
    if res.status != 0:
        return None
    x = res.x
    # exact reconstruction: rationalize, then verify; fall back to exact solve on the support
    for denom in (1, 2, 4, 6, 12, 24, 120, 720, 5040, 10 ** 4, 10 ** 6):
        cert = _build(cands, eq_terms, x, npoly, neq, denom)
        try:
            check_certificate(hyps, eqs, goal, cert)
            return cert
        except CertificateError:
            pass
    cert = _exact_on_support(hyps, eqs, goal, cands, eq_terms, polys, x, npoly, neq)
    return cert


def _build(cands, eq_terms, x, npoly, neq, denom):
    terms = []
    for j in range(npoly):
        if x[j] > 1e-9:
            c = Fraction(x[j]).limit_denominator(denom)
            if c > 0:
                hs, sq = cands[j]
                terms.append({"c": c, "hyps": list(hs), "sq": sq})
    eqs = []
    for j in range(neq):
        v = x[npoly + j]
        if abs(v) > 1e-9:
            en, mult = eq_terms[j]
            eqs.append({"mult": mult * Fraction(v).limit_denominator(denom), "eq": en})
    c0 = Fraction(max(0.0, x[-1])).limit_denominator(denom)
    return {"kind": "sum", "terms": terms, "eqs": eqs, "const": c0}


def _exact_on_support(hyps, eqs_dict, goal, cands, eq_terms, polys, x, npoly, neq):
    """Solve the identity exactly using only the columns in the LP support."""
    support = [j for j in range(npoly) if x[j] > 1e-9]
    esupport = [j for j in range(neq) if abs(x[npoly + j]) > 1e-9]
    g = Poly.coerce(-1) if goal[0] == "contra" else goal[1]
    columns = [polys[j] for j in support] + [eq_terms[j][1] * eqs_dict[eq_terms[j][0]] for j in esupport]
    columns.append(Poly.coerce(1))
    monos = sorted(set(m for p in columns for m in p.terms) | set(g.terms))
    # Gaussian elimination over Q for A y = b (least-norm not needed; any exact solution)
    A = [[p.terms.get(m, Fraction(0)) for p in columns] for m in monos]
    bvec = [g.terms.get(m, Fraction(0)) for m in monos]
    y = _solve_exact(A, bvec)
    if y is None:
        return None
    k = len(support)
    if any(v < 0 for v in y[:k]) or y[-1] < 0:
        return None
    terms = [{"c": y[i], "hyps": list(cands[j][0]), "sq": cands[j][1]} for i, j in enumerate(support) if y[i] != 0]
    eqterms = [{"mult": eq_terms[j][1] * y[k + i], "eq": eq_terms[j][0]} for i, j in enumerate(esupport) if y[k + i] != 0]
    cert = {"kind": "sum", "terms": terms, "eqs": eqterms, "const": y[-1]}
    try:
        check_certificate(hyps, eqs_dict, goal, cert)
        return cert
    except CertificateError:
        return None


def _solve_exact(A, b):
    rows, cols = len(A), len(A[0]) if A else 0
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    pivots = []
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [v / pv for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    for i in range(r, rows):
        if M[i][-1] != 0:
            return None
    y = [Fraction(0)] * cols
    for i, c in enumerate(pivots):
        y[c] = M[i][-1]
    return y
