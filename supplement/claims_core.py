"""Claim objects for the appendix calculations and the machinery to check them.

Kinds of claims
  Ineq      : hypotheses h >= 0 (and equations e = 0) on integer variables imply a goal
              ("ge0", g), ("gt0", g) or ("contra",). Checked by an exact certificate.
  Tuple     : starting from a polynomial tuple, a mutation word produces the stated tuples
              (or stated entries). Each mutation needs certified weak signs of the incident
              entries under the hypotheses; the checker verifies those sign certificates.
  Identity  : two polynomials are identical (exact expansion), e.g. a Markov value.
  Pattern   : a sign-only property (proper classes, acyclicity, vortex, ...) holds for every
              sign pattern allowed by `spec`; the allowed signs of each entry are certified
              from the hypotheses where they are not trivially true.
Certificates not written by hand are found by build_certificates.py (linear programming) and
stored in certificates.json; check_proofs.py verifies all of them exactly.
"""
from polynomial import Poly, V
from certificates import check_certificate, CertificateError
import symbolic as S
import quiver4 as Q

REGISTRY = []


def lookup(cid):
    cid = norm_id(cid)
    for cl in REGISTRY:
        if cl.id == cid:
            return cl
    raise KeyError(cid)


def norm_id(cid):
    """Claim identifiers use hyphens (so that they can be typeset in TeX); underscores in the
    source are converted."""
    return cid.replace("_", "-")


def register(claim):
    claim.id = norm_id(claim.id)
    if any(c.id == claim.id for c in REGISTRY):
        raise ValueError("duplicate claim id %s" % claim.id)
    REGISTRY.append(claim)
    return claim


class Ineq:
    kind = "ineq"

    def __init__(self, id, ref, text, hyps, goal, eqs=None, cert=None, hints=(), depth=2,
                 extra_terms=(), eq_mult_deg=None, uses=()):
        self.id, self.ref, self.text = id, ref, text
        self.hyps = {k: Poly.coerce(v) for k, v in hyps.items()}
        # Conclusions of earlier claims may be used as hypotheses ("modus ponens"), provided the
        # earlier claim's hypotheses and equations are among this claim's.
        self.uses = tuple(uses)
        for uid in self.uses:
            lemma = lookup(uid)
            if lemma.kind != "ineq" or lemma.goal[0] not in ("ge0", "gt0"):
                raise ValueError("%s can only use inequality claims" % id)
            for hn, hp in lemma.hyps.items():
                if hn not in self.hyps or not (self.hyps[hn] - hp).is_zero():
                    raise ValueError("%s uses %s but lacks its hypothesis %s" % (id, uid, hn))
            for en, ep in lemma.eqs.items():
                if en not in (eqs or {}) or not (Poly.coerce((eqs or {})[en]) - ep).is_zero():
                    raise ValueError("%s uses %s but lacks its equation %s" % (id, uid, en))
            self.hyps["use:" + uid] = lemma.goal[1]
        self.eqs = {k: Poly.coerce(v) for k, v in (eqs or {}).items()}
        if goal[0] != "contra":
            goal = (goal[0], Poly.coerce(goal[1]))
        self.goal = goal
        self.cert = cert
        self.hints = tuple(Poly.coerce(h) for h in hints)
        self.depth = depth
        self.extra_terms = tuple(extra_terms)
        self.eq_mult_deg = eq_mult_deg
        register(self)

    def check(self, store):
        cert = self.cert if self.cert is not None else store.get(self.id)
        if cert is None:
            raise CertificateError("%s: no certificate" % self.id)
        check_certificate(self.hyps, self.eqs, self.goal, cert)
        return 1


class Identity:
    kind = "identity"

    def __init__(self, id, ref, text, lhs, rhs):
        self.id, self.ref, self.text = id, ref, text
        self.lhs, self.rhs = Poly.coerce(lhs), Poly.coerce(rhs)
        register(self)

    def check(self, store):
        if not (self.lhs - self.rhs).is_zero():
            raise CertificateError("%s: identity fails, difference %r" % (self.id, self.lhs - self.rhs))
        return 1


class Tuple:
    """steps: list of (vertex, expected) where expected is a full tuple, a dict {pair: poly},
    or None. relabel: optional (pi, X), asserting that (final tuple)^pi == X."""
    kind = "tuple"

    def __init__(self, id, ref, text, hyps, start, steps, eqs=None, relabel=None):
        self.id, self.ref, self.text = id, ref, text
        self.hyps = {k: Poly.coerce(v) for k, v in hyps.items()}
        self.eqs = {k: Poly.coerce(v) for k, v in (eqs or {}).items()}
        self.start = S.as_poly_tuple(start)
        self.steps = []
        for k, exp in steps:
            if isinstance(exp, (tuple, list)):
                exp = S.as_poly_tuple(exp)
            elif isinstance(exp, dict):
                exp = {p: Poly.coerce(v) for p, v in exp.items()}
            self.steps.append((k, exp))
        self.relabel = None if relabel is None else (relabel[0], S.as_poly_tuple(relabel[1]))
        register(self)

    def run(self, signs):
        """Compute the path using the given signs {(step, i): '+'|'-'}."""
        t = self.start
        path = [t]
        for s, (k, _) in enumerate(self.steps):
            sg = {i: signs[(s, i)] for i in Q.VERTICES if i != k}
            t = S.smutate(t, k, sg)
            path.append(t)
        return path

    def check(self, store):
        data = store.get(self.id)
        if data is None:
            raise CertificateError("%s: no sign certificates" % self.id)
        signs = {}
        t = self.start
        path = [t]
        for s, (k, exp) in enumerate(self.steps):
            sg = {}
            for i, x in S.incident_entries(t, k):
                key = "%d,%d" % (s, i)
                entry = data[key]
                sign, cert = entry["sign"], entry["cert"]
                if sign == '?':
                    sg[i] = '?'
                    continue
                if x is None:
                    raise CertificateError("%s: sign of an unknown entry used at step %d" % (self.id, s))
                goal = ("ge0", x if sign == '+' else -x)
                check_certificate(self.hyps, self.eqs, goal, cert)
                sg[i] = sign
            t = S.smutate(t, k, sg)
            path.append(t)
            if exp is None:
                continue
            if isinstance(exp, tuple):
                for a, b in zip(t, exp):
                    if a is None or not _equal_mod_eqs(a, b, self.eqs):
                        raise CertificateError("%s: step %d gives %r, expected %r" % (self.id, s, t, exp))
            else:
                for pair, val in exp.items():
                    got = S.sentry_or_none(t, *pair)
                    if got is None or not _equal_mod_eqs(got, val, self.eqs):
                        raise CertificateError("%s: step %d entry %s is %r, expected %r" % (self.id, s, pair, got, val))
        if self.relabel is not None:
            pi, exp = self.relabel
            if any(x is None for x in t):
                raise CertificateError("%s: endpoint has unknown entries" % self.id)
            r = S.srelabel(t, pi)
            for a, b in zip(r, exp):
                if not _equal_mod_eqs(a, b, self.eqs):
                    raise CertificateError("%s: relabeled endpoint %r, expected %r" % (self.id, r, exp))
        return 1


def _equal_mod_eqs(a, b, eqs):
    # Only exact equality is used; tuples are stated after substituting all equations by hand.
    return (a - b).is_zero()


class Pattern:
    """spec: list of 6 sign-set strings (see symbolic.SIGN_SETS) for b12..b34.
    entries: the 6 polynomial entries of the case (used to certify the sign sets).
    prop: function of a {-1,0,1} quiver returning True when the property holds."""
    kind = "pattern"

    def __init__(self, id, ref, text, hyps, entries, spec, prop, prop_name, eqs=None):
        self.id, self.ref, self.text = id, ref, text
        self.hyps = {k: Poly.coerce(v) for k, v in hyps.items()}
        self.eqs = {k: Poly.coerce(v) for k, v in (eqs or {}).items()}
        self.entries = S.as_poly_tuple(entries)
        self.spec = list(spec)
        self.prop, self.prop_name = prop, prop_name
        register(self)

    def sign_goals(self):
        """Goals that certify each entry's sign set. '+' needs x-1>=0, '-' needs -x-1>=0,
        '+0' needs x>=0, '-0' needs -x>=0, '0' needs x identically 0, '*' and '+-' need nothing
        ('+-' is only used for entries that are nonzero by the case statement, certified as a split)."""
        goals = []
        for n, (x, s) in enumerate(zip(self.entries, self.spec)):
            if s == "+":
                goals.append((n, ("ge0", x - 1)))
            elif s == "-":
                goals.append((n, ("ge0", -x - 1)))
            elif s == "+0":
                goals.append((n, ("ge0", x)))
            elif s == "-0":
                goals.append((n, ("ge0", -x)))
            elif s == "0":
                if not x.is_zero():
                    raise CertificateError("%s: entry %d declared zero but is %r" % (self.id, n, x))
            elif s in ("*",):
                pass
            else:
                raise CertificateError("%s: unsupported sign set %r" % (self.id, s))
        return goals

    def check(self, store):
        data = store.get(self.id, {})
        for n, goal in self.sign_goals():
            cert = data.get(str(n))
            if cert is None:
                raise CertificateError("%s: no sign certificate for entry %d" % (self.id, n))
            check_certificate(self.hyps, self.eqs, goal, cert)
        count = 0
        for pat in S.sign_patterns(self.spec):
            if not S.pattern_property(pat, self.prop):
                raise CertificateError("%s: property %s fails for sign pattern %r" % (self.id, self.prop_name, pat))
            count += 1
        return count


# ------------------------------------------------------------------------- common properties
def prop_at_most_one_proper_class_containing(order):
    order = Q.normalize_cyclic(order)

    def prop(q):
        cls = Q.proper_classes(q)
        return len(cls) == 0 or (len(cls) == 1 and order in cls[0])
    return prop


def prop_acyclic(q):
    return Q.is_acyclic(q)


def prop_vortex(q):
    return Q.is_vortex(q)


def prop_oriented_triangle(i, j, k):
    def prop(q):
        x, y, z = Q.entry(q, i, j), Q.entry(q, j, k), Q.entry(q, k, i)
        return (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0)
    return prop


class TupleEq:
    """Two polynomial tuples are equal entrywise (e.g. a relabeling identity)."""
    kind = "identity"

    def __init__(self, id, ref, text, lhs, rhs):
        self.id, self.ref, self.text = id, ref, text
        self.lhs, self.rhs = S.as_poly_tuple(lhs), S.as_poly_tuple(rhs)
        register(self)

    def check(self, store):
        for n, (x, y) in enumerate(zip(self.lhs, self.rhs)):
            if not (x - y).is_zero():
                raise CertificateError("%s: entry %d differs: %r vs %r" % (self.id, n, x, y))
        return 1


class SymmetryCheck:
    """A simultaneous substitution of variables permutes a system of hypotheses (as a multiset
    of polynomials). Used to justify 'without loss of generality' reductions."""
    kind = "identity"

    def __init__(self, id, ref, text, hyps, substitution):
        self.id, self.ref, self.text = id, ref, text
        self.hyps = [Poly.coerce(v) for v in hyps.values()]
        self.substitution = {k: Poly.coerce(v) for k, v in substitution.items()}
        register(self)

    def check(self, store):
        key = lambda p: repr(sorted(p.terms.items()))
        before = sorted(key(p) for p in self.hyps)
        after = sorted(key(p.substitute(self.substitution)) for p in self.hyps)
        if before != after:
            raise CertificateError("%s: the substitution does not permute the hypotheses" % self.id)
        return 1


def fit_eq_multipliers(hyps, eqs, goal, ps, deg=2):
    """Given a positive combination `ps` (certificates.PS) whose identity holds only modulo the
    equations, find polynomial multipliers for the equations by exact linear algebra and return a
    complete certificate. Used only while writing claims; the checker verifies the result."""
    from fractions import Fraction
    from certificates import check_certificate as _chk
    from find_certificates import _monomials_upto, _solve_exact
    cert = ps.cert()
    total = Poly()
    for t in cert["terms"]:
        p = Poly.coerce(t["c"])
        for hn in t["hyps"]:
            p = p * hyps[hn]
        if t["sq"] is not None:
            p = p * t["sq"] * t["sq"]
        total = total + p
    g = Poly.coerce(-1) if goal[0] == "contra" else goal[1]
    resid = g - total            # must equal sum mult_l * eq_l + nonneg constant
    names = sorted(eqs)
    allvars = sorted(set(resid.variables()).union(*[set(e.variables()) for e in eqs.values()]))
    cols, keys = [], []
    for en in names:
        for mono in _monomials_upto(allvars, deg):
            keys.append((en, mono))
            cols.append(Poly({mono: 1}) * eqs[en])
    for cconst in range(0, 200):
        target = resid - cconst
        monos = sorted(set(m for p in cols for m in p.terms) | set(target.terms))
        A = [[p.terms.get(m, Fraction(0)) for p in cols] for m in monos]
        bvec = [target.terms.get(m, Fraction(0)) for m in monos]
        sol = _solve_exact(A, bvec)
        if sol is not None:
            break
    else:
        raise ValueError("no equation multipliers found")
    eqterms = {}
    for (en, mono), val in zip(keys, sol):
        if val:
            eqterms[en] = eqterms.get(en, Poly()) + Poly({mono: val})
    cert["eqs"] = [{"mult": m, "eq": en} for en, m in sorted(eqterms.items())]
    _chk(hyps, eqs, goal, cert)
    return cert


def prop_exactly_one_proper_class_containing(order):
    order = Q.normalize_cyclic(order)

    def prop(q):
        cls = Q.proper_classes(q)
        return len(cls) == 1 and order in cls[0]
    return prop
