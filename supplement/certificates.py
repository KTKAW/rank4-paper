"""Exact checker for positivity certificates (standard library only).

A claim says: if the integer variables satisfy every hypothesis h >= 0 (and every equation e = 0),
then a goal holds. Goals:
    ("ge0", g)  : g >= 0
    ("gt0", g)  : g > 0
    ("contra",) : the hypotheses are inconsistent (no integer point satisfies them)

A certificate is one of
    Sum certificate  {"kind": "sum", "terms": [...], "eqs": [...], "const": c}
        terms: each {"c": coefficient >= 0, "hyps": [names, repetition allowed], "sq": poly or None}
        eqs:   each {"mult": poly, "eq": name}
        It certifies   g = sum_k c_k * prod(hyps_k) * sq_k^2 + sum_l mult_l * eq_l + const
        identically, with every c_k >= 0 and const >= 0 (const > 0 for "gt0").
        For "contra" the goal polynomial is taken to be -1, so the identity says that a
        nonnegative quantity equals -1 - const < 0.
    Split certificate {"kind": "split", "on": x, "ge1": cert, "le0": cert}
        x must have integer coefficients, so it is integer valued on integer points.
        Every integer point satisfies x - 1 >= 0 or -x >= 0; each branch adds that hypothesis
        and must certify the same goal.

Polynomials are polynomial.Poly objects. When certificates are stored as JSON, they are encoded
with encode_poly/decode_poly.
"""
from fractions import Fraction
from polynomial import Poly

__all__ = ["check_certificate", "CertificateError", "encode_poly", "decode_poly",
           "encode_cert", "decode_cert", "PS", "H", "Sq", "Split"]


class CertificateError(Exception):
    pass


def _goal_poly(goal):
    if goal[0] == "contra":
        return Poly.coerce(-1)
    if goal[0] in ("ge0", "gt0"):
        return goal[1]
    raise CertificateError("unknown goal kind %r" % (goal[0],))


def check_certificate(hyps, eqs, goal, cert, _depth=0):
    """Return True or raise CertificateError explaining what failed."""
    if _depth > 50:
        raise CertificateError("split nesting too deep")
    kind = cert.get("kind")
    if kind == "split":
        x = cert["on"]
        if not isinstance(x, Poly) or not x.has_integer_coefficients():
            raise CertificateError("split polynomial must have integer coefficients")
        name = "__split%d" % _depth
        h1 = dict(hyps)
        h1[name + "_ge1"] = x - 1
        h2 = dict(hyps)
        h2[name + "_le0"] = -x
        # branch certificates may refer to the added hypothesis by the generic names
        check_certificate(_alias(h1, name + "_ge1"), eqs, goal, cert["ge1"], _depth + 1)
        check_certificate(_alias(h2, name + "_le0"), eqs, goal, cert["le0"], _depth + 1)
        return True
    if kind != "sum":
        raise CertificateError("unknown certificate kind %r" % (kind,))
    total = Poly()
    for t in cert.get("terms", []):
        c = Fraction(t["c"])
        if c < 0:
            raise CertificateError("negative coefficient %s" % c)
        p = Poly.coerce(c)
        for h in t.get("hyps", []):
            if h not in hyps:
                raise CertificateError("unknown hypothesis %r" % (h,))
            p = p * hyps[h]
        sq = t.get("sq")
        if sq is not None:
            p = p * sq * sq
        total = total + p
    for e in cert.get("eqs", []):
        if e["eq"] not in eqs:
            raise CertificateError("unknown equation %r" % (e["eq"],))
        total = total + e["mult"] * eqs[e["eq"]]
    g = _goal_poly(goal)
    if cert.get("const", 0) == "auto":
        # the constant is whatever remains; it must be a constant of the right sign
        resid = g - total
        if not resid.is_constant():
            raise CertificateError("identity fails; non-constant residual %r" % (resid,))
        c0 = resid.constant()
    else:
        c0 = Fraction(cert.get("const", 0))
    if c0 < 0:
        raise CertificateError("negative constant %s" % c0)
    if goal[0] == "gt0" and c0 <= 0:
        raise CertificateError("strict goal needs a positive constant")
    total = total + c0
    diff = g - total
    if not diff.is_zero():
        raise CertificateError("identity fails; residual %r" % (diff,))
    return True


def _alias(hyps, name):
    h = dict(hyps)
    h["SPLIT"] = hyps[name]
    return h


# ---------------------------------------------------------------------- JSON encoding
def encode_poly(p):
    return [[str(c), [[v, e] for v, e in m]] for m, c in sorted(p.terms.items())]


def decode_poly(data):
    return Poly({tuple((v, e) for v, e in m): Fraction(c) for c, m in data})


def encode_cert(cert):
    if cert["kind"] == "split":
        return {"kind": "split", "on": encode_poly(cert["on"]),
                "ge1": encode_cert(cert["ge1"]), "le0": encode_cert(cert["le0"])}
    c0 = cert.get("const", 0)
    out = {"kind": "sum", "const": "auto" if c0 == "auto" else str(Fraction(c0)), "terms": [], "eqs": []}
    for t in cert.get("terms", []):
        out["terms"].append({"c": str(Fraction(t["c"])), "hyps": list(t.get("hyps", [])),
                             "sq": None if t.get("sq") is None else encode_poly(t["sq"])})
    for e in cert.get("eqs", []):
        out["eqs"].append({"mult": encode_poly(e["mult"]), "eq": e["eq"]})
    return out


def decode_cert(data):
    if data["kind"] == "split":
        return {"kind": "split", "on": decode_poly(data["on"]),
                "ge1": decode_cert(data["ge1"]), "le0": decode_cert(data["le0"])}
    return {"kind": "sum", "const": "auto" if data["const"] == "auto" else Fraction(data["const"]),
            "terms": [{"c": Fraction(t["c"]), "hyps": t["hyps"],
                       "sq": None if t["sq"] is None else decode_poly(t["sq"])} for t in data["terms"]],
            "eqs": [{"mult": decode_poly(e["mult"]), "eq": e["eq"]} for e in data["eqs"]]}


# ---------------------------------------------------------------------- building certificates
class PS:
    """A nonnegative combination of products of hypotheses, each optionally times a square,
    used to write certificates by hand, e.g.  4*H('m3') + H('b2')*H('c2') + Sq(2*c - F) + 3.
    Convert with .cert(eqs=[(multiplier_poly, eq_name), ...]).
    Internally: a list of (coef >= 0, hyp-name tuple, square-poly or None) and a constant."""

    def __init__(self, terms=(), const=0):
        self.terms = list(terms)
        self.const = Fraction(const)
        if self.const < 0 or any(c < 0 for c, _, _ in self.terms):
            raise CertificateError("negative coefficient in a positive combination")

    @staticmethod
    def lift(x):
        return x if isinstance(x, PS) else PS(const=Fraction(x))

    def __add__(self, other):
        other = PS.lift(other)
        return PS(self.terms + other.terms, self.const + other.const)

    __radd__ = __add__

    def __mul__(self, other):
        other = PS.lift(other)
        a = self.terms + ([(self.const, (), None)] if self.const else [])
        b = other.terms + ([(other.const, (), None)] if other.const else [])
        terms, const = [], Fraction(0)
        for c1, h1, s1 in a:
            for c2, h2, s2 in b:
                hs = tuple(sorted(h1 + h2))
                sq = s2 if s1 is None else (s1 if s2 is None else s1 * s2)
                if not hs and sq is None:
                    const += c1 * c2
                else:
                    terms.append((c1 * c2, hs, sq))
        return PS(terms, const)

    __rmul__ = __mul__

    def cert(self, eqs=(), auto=True):
        merged = {}
        for c, hs, sq in self.terms:
            key = (hs, None if sq is None else repr(sorted(sq.terms.items())))
            if key in merged:
                merged[key][0] += c
            else:
                merged[key] = [c, hs, sq]
        terms = [{"c": c, "hyps": list(hs), "sq": sq} for key, (c, hs, sq) in sorted(merged.items(), key=lambda kv: repr(kv[0])) if c]
        if self.const:
            terms.append({"c": self.const, "hyps": [], "sq": None})
        # the remaining constant is computed by the checker and must be >= 0 (> 0 for strict goals)
        return {"kind": "sum", "terms": terms, "eqs": [{"mult": Poly.coerce(m), "eq": e} for m, e in eqs],
                "const": "auto"}


def H(name):
    return PS([(Fraction(1), (name,), None)])


def Sq(poly):
    return PS([(Fraction(1), (), Poly.coerce(poly))])


def Split(on, ge1, le0):
    return {"kind": "split", "on": Poly.coerce(on), "ge1": ge1, "le0": le0}
