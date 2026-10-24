"""The calculations of Appendices A and B of the paper, and those cited in Sections 2 to 5, as
machine-checkable claims.

Each claim has an identifier (cited in the paper and in APPENDIX_CALCULATIONS.md), a pointer to
the place in the paper where it is used, a one-line statement, hypotheses (polynomials that are
>= 0 at the integer point under consideration), and a goal. All variables are integers.
Notation follows the paper: F = T + 1 is the height of a high quiver, so "low" means height
<= F - 1, and the standing hypotheses are F >= 4, 3 <= m <= F - 1 and 2|p| < m, i.e.
m - 2p - 1 >= 0 and m + 2p - 1 >= 0. Strict integer inequalities are written as >= 1.
"""
from polynomial import V, Poly
from certificates import H, Sq, Split
from claims_core import Ineq, Identity, Tuple, Pattern, TupleEq, SymmetryCheck, fit_eq_multipliers
import claims_core as CC
import symbolic as S
import quiver4 as Q

a, b, c, d, e, E, f, F = (V(n) for n in "a b c d e E f F".split())
t, u, v, r, s, x, y, z, D, L = (V(n) for n in "t u v r s x y z D L".split())
X, Y, U, Sv, K, w, h, g, beta, gamma = (V(n) for n in "X Y U S K w h g beta gamma".split())


def rng(name, var, lo, hi):
    """lo <= var <= hi as two hypotheses."""
    return {name + "_lo": var - lo, name + "_hi": hi - var}


def low(name, expr):
    """|expr| <= F - 1 (the entry belongs to a low quiver)."""
    return {name + "_lo": expr + (F - 1), name + "_hi": (F - 1) - expr}


def atmostF(name, expr):
    """|expr| <= F (the entry belongs to a quiver on a route of height F)."""
    return {name + "_lo": expr + F, name + "_hi": F - expr}


def markov_hyps(m_expr, p_expr, upper=True):
    hy = {"m3": m_expr - 3, "m_2p": m_expr - 2 * p_expr - 1, "m_p2": m_expr + 2 * p_expr - 1}
    if upper:
        hy["mT"] = (F - 1) - m_expr
    return hy


def merge(*ds):
    out = {}
    for dd in ds:
        for k, val in dd.items():
            if k in out:
                raise ValueError("duplicate hypothesis name %s" % k)
            out[k] = val
    return out


F4 = {"F4": F - 4}

# =============================================================================== A0: general lemmas
Pattern("A0.ord1", "Lemma A.1, case (i)",
        "If a>=0, b,c,f>0 and d>=0, then (a,b,-c,d,E,f) has at most one proper wiggle class, "
        "and it contains <1,2,3,4>.",
        hyps={}, entries=(0, 1, -1, 0, 0, 1), spec=["+0", "+", "-", "+0", "*", "+"],
        prop=CC.prop_at_most_one_proper_class_containing((1, 2, 3, 4)), prop_name="unique class <1234>")
Pattern("A0.ord2", "Lemma A.1, case (ii)",
        "If a=0, b,c,f>0, d<0 and E<=0, then (0,b,-c,d,E,f) has at most one proper wiggle class, "
        "and it contains <1,2,3,4>.",
        hyps={}, entries=(0, 1, -1, -1, 0, 1), spec=["0", "+", "-", "-", "-0", "+"],
        prop=CC.prop_at_most_one_proper_class_containing((1, 2, 3, 4)), prop_name="unique class <1234>")

_pb = merge(rng("r", r, 1, F - 1), rng("s", s, 1, F - 1), F4)
Ineq("A0.pb1", "Lemma A.2", "1<=r,s<=F-1 and rs=2F rule out r<=2.",
     hyps=merge(_pb, {"r_le2": 2 - r}), eqs={"rs": r * s - 2 * F}, goal=("contra",))
Ineq("A0.pb2", "Lemma A.2", "If 3<=r,s<=F-1 and rs=2F then 3(r^2+s^2) <= 2F^2-5F+36.",
     hyps=merge(rng("r", r, 3, F - 1), rng("s", s, 3, F - 1), {"F2": F + 2}), eqs={"rs": r * s - 2 * F},
     goal=("ge0", 2 * F ** 2 - 5 * F + 36 - 3 * (r ** 2 + s ** 2)),
     cert=(3 * H("r_lo") * H("r_hi") + 3 * H("s_lo") * H("s_hi") + H("F2") * H("r_lo") * H("s_lo"))
     .cert(eqs=[(-(F + 2), "rs")]))
Ineq("A0.rect", "Section 4, eq. (9)", "For 1<=r,s<=F-1: r^2+s^2-Frs <= 2-F.",
     hyps=merge(rng("r", r, 1, F - 1), rng("s", s, 1, F - 1), {"F0": F}),
     goal=("ge0", (2 - F) - (r ** 2 + s ** 2 - F * r * s)),
     cert=(H("r_lo") * H("r_hi") + H("s_lo") * H("s_hi") + H("F0") * H("r_lo") * H("s_lo")).cert())

# =============================================================================== A1: Lemma 4.2
# Normal form P = (0, b, -c, d, E, F) with 1 <= b, c <= F-1 and |d|, |E| <= F-1.
P1 = (0, b, -c, d, E, F)
_P1 = merge(rng("b", b, 1, F - 1), rng("c", c, 1, F - 1), low("d", d), low("E", E), F4)

Tuple("A1.mu2_dneg_Epos", "App. A.1", "If d<=0<=E, mutation at 2 makes b34 = F - dE.",
      hyps=merge(_P1, {"dneg": -d, "Epos": E}), start=P1, steps=[(2, {(3, 4): F - d * E})])
Ineq("A1.dneg_Epos", "App. A.1", "d<0<E is impossible: mu_2 P would have b34 = F-dE > F.",
     hyps=merge(_P1, {"d_neg": -d - 1, "E_pos": E - 1, "ht": F - (F - d * E)}), goal=("contra",))
Identity("A1.markov", "eq. (zeroMarkov)", "Markov value of P in the order 1<2<3<4.",
         S.smarkov(S.as_poly_tuple(P1), (1, 2, 3, 4)),
         b ** 2 + c ** 2 + d ** 2 + E ** 2 + F ** 2 - b * c * F + d * E * F)
Tuple("A1.mu3_dpos", "App. A.1", "Mutation at 3 creates b14 = bF - c and b24 = E + Fd when d >= 0.",
      hyps=merge(_P1, {"dpos": d}), start=P1, steps=[(3, {(1, 4): b * F - c, (2, 4): E + F * d})])
Tuple("A1.mu3_dneg", "App. A.1", "Mutation at 3 creates b14 = bF - c and b24 = E when d <= 0.",
      hyps=merge(_P1, {"dneg": -d}), start=P1, steps=[(3, {(1, 4): b * F - c, (2, 4): E})])
Ineq("A1.mu3_b1", "App. A.1", "If mutation at 3 stays within height F then b = 1 (b>=2 impossible).",
     hyps=merge(_P1, {"b2": b - 2, "ht": F - (b * F - c)}), goal=("contra",))
Ineq("A1.mu3_d1", "App. A.1", "If mutation at 3 stays within height F then d <= 1 (d>=2 impossible).",
     hyps=merge(_P1, {"d2": d - 2, "ht": F - (E + F * d)}), goal=("contra",))
Ineq("A1.mu3_E", "App. A.1", "If d = 1 and mutation at 3 stays within height F then E <= 0.",
     hyps=merge(_P1, {"E_pos": E - 1, "ht": F - (E + F)}), goal=("contra",))
_m1 = 1 + c ** 2 + d ** 2 + E ** 2 + F ** 2 - c * F + d * E * F   # b = 1
Identity("A1.id_dnonpos", "App. A.1", "4(m-F) = (2c-F)^2+3(F-1)^2+2F+1+4d^2+4E^2+4dEF when b=1.",
         4 * (_m1 - F), (2 * c - F) ** 2 + 3 * (F - 1) ** 2 + 2 * F + 1 + 4 * d ** 2 + 4 * E ** 2 + 4 * d * E * F)
Ineq("A1.dzero", "App. A.1", "b=1, d=0: m > F, contradicting m <= F-1.",
     hyps=merge(rng("c", c, 1, F - 1), low("E", E), F4, {"mT": (F - 1) - _m1.substitute({"d": 0})}),
     goal=("contra",),
     cert=(4 * H("mT") + Sq(2 * c - F) + 3 * Sq(F - 1) + 2 * H("F4") + 4 * Sq(E)).cert())
Ineq("A1.dneg_Enonpos", "App. A.1", "b=1, d<0, E<=0: m > F, contradicting m <= F-1.",
     hyps=merge(rng("c", c, 1, F - 1), {"d_neg": -d - 1, "E_np": -E}, F4, {"mT": (F - 1) - _m1}),
     goal=("contra",),
     cert=(4 * H("mT") + Sq(2 * c - F) + 3 * Sq(F - 1) + 2 * H("F4") + 4 * Sq(d) + 4 * Sq(E)
           + 4 * H("d_neg") * H("E_np") * H("F4") + 16 * H("d_neg") * H("E_np")
           + 4 * H("E_np") * H("F4") + 16 * H("E_np")).cert())
_m1d1 = _m1.substitute({"d": 1})
Identity("A1.id_d1", "App. A.1", "4(m-F) = (2c-F)^2+(2E+F)^2+2(F-1)^2+6 when b=d=1.",
         4 * (_m1d1 - F), (2 * c - F) ** 2 + (2 * E + F) ** 2 + 2 * (F - 1) ** 2 + 6)
Ineq("A1.d1", "App. A.1", "b=d=1: m > F, contradicting m <= F-1.",
     hyps={"mT": (F - 1) - _m1d1}, goal=("contra",),
     cert=(4 * H("mT") + Sq(2 * c - F) + Sq(2 * E + F) + 2 * Sq(F - 1)).cert())
TupleEq("A1.sym34", "App. A.1",
        "Reversing all arrows and exchanging 3,4 sends P(b,c,d,E) to P(c,b,-E,-d).",
        S.srelabel(S.sreverse(S.as_poly_tuple(P1)), Q.PI34), (0, c, -b, -E, -d, F))
for name, hy, val in [("A1.mu2_dpos_Eneg", {"dpos": d, "Eneg": -E}, F + d * E),
                      ("A1.mu2_dpos_Epos", {"dpos": d, "Epos": E}, F),
                      ("A1.mu2_dneg_Eneg", {"dneg": -d, "Eneg": -E}, F)]:
    Tuple(name, "App. A.1", "Mutation at 2: the b34 entry stays F unless d > 0 > E, when it is F + dE.",
          hyps=merge(_P1, hy), start=P1, steps=[(2, (0, b, -c, -d, -E, val))])
_mm = b ** 2 + c ** 2 + d ** 2 + e ** 2 + F ** 2 - b * c * F - d * e * F   # E = -e
Ineq("A1.minusF", "App. A.1",
     "If mu_2 P has b34 = -F then de = 2F, and then 3m <= 42-8F-F^2 < 9, contradicting m >= 3.",
     hyps=merge(rng("b", b, 1, F - 1), rng("c", c, 1, F - 1), rng("d", d, 3, F - 1), rng("e", e, 3, F - 1),
                {"F0": F, "F2": F + 2, "F4": F - 4, "m3": _mm - 3}),
     eqs={"de": d * e - 2 * F}, goal=("contra",),
     cert=(3 * (H("b_lo") * H("b_hi") + H("c_lo") * H("c_hi") + H("F0") * H("b_lo") * H("c_lo"))
           + 3 * H("d_lo") * H("d_hi") + 3 * H("e_lo") * H("e_hi") + H("F2") * H("d_lo") * H("e_lo")
           + 3 * H("m3") + H("F4") * H("F4") + 16 * H("F4"))
     .cert(eqs=[(-(F + 2) + 3 * F, "de")]))
Ineq("A1.minusF_d3", "App. A.1", "In that case d >= 3 and e >= 3 (Lemma A.2 with r=d, s=e): d<=2 impossible.",
     hyps=merge(rng("d", d, 1, 2), rng("e", e, 1, F - 1), F4), eqs={"de": d * e - 2 * F}, goal=("contra",))
Ineq("A1.minusF_e3", "App. A.1", "Likewise e <= 2 is impossible.",
     hyps=merge(rng("e", e, 1, 2), rng("d", d, 1, F - 1), F4), eqs={"de": d * e - 2 * F}, goal=("contra",))
P1b = (0, b, -c, -d, -E, F)
for name, hy in [("A1.second_dneg_Eneg", {"dneg": -d, "Eneg": -E}), ("A1.second_dpos_Epos", {"dpos": d, "Epos": E})]:
    Tuple(name, "App. A.1", "From the second high quiver (0,b,-c,-d,-E,F), mutation at 1 gives b34 = F - bc.",
          hyps=merge(_P1, hy), start=P1b, steps=[(1, {(3, 4): F - b * c})])
Tuple("A1.mu1P", "App. A.1", "Mutation at 1 of P gives b34 = F - bc.",
      hyps=_P1, start=P1, steps=[(1, {(3, 4): F - b * c})])

# ----------------------------------------------------------------- A1, second assertion (commuting square)
# P = (0, b, -c, d, -e, f), 1 <= b,c,d,e <= F-1, f >= F; its neighbours mu_1 P, mu_2 P are low, so
# |f - bc| <= F-1 and |f - de| <= F-1; the failure assumption is bc + de >= f + F.
P2 = (0, b, -c, d, -e, f)
_m2 = b ** 2 + c ** 2 + d ** 2 + e ** 2 + f ** 2 - f * (b * c + d * e)
_p2 = b * e - c * d
Identity("A1.sq_markov", "App. A.1", "Markov value of P = (0,b,-c,d,-e,f) in the order 1<2<3<4.",
         S.smarkov(S.as_poly_tuple(P2), (1, 2, 3, 4)), _m2)
Identity("A1.sq_pf", "App. A.1", "Pfaffian of P = (0,b,-c,d,-e,f).", S.spfaffian(S.as_poly_tuple(P2)), _p2)
_sqbase = merge(rng("b", b, 1, F - 1), rng("c", c, 1, F - 1), rng("d", d, 1, F - 1), rng("e", e, 1, F - 1),
                {"f_lo": f - F}, low("nb1", f - b * c), low("nb2", f - d * e), F4)
Tuple("A1.sq_paths", "App. A.1",
      "The corners of the commuting square: b34 = f-bc, then f-bc-de after mutating at 1 then 2.",
      hyps=_sqbase, start=P2, steps=[(1, {(3, 4): f - b * c}), (2, {(3, 4): f - b * c - d * e})])
Tuple("A1.sq_paths2", "App. A.1", "Mutation at 2 first: b34 = f-de.",
      hyps=_sqbase, start=P2, steps=[(2, {(3, 4): f - d * e})])
_sqfail = merge(_sqbase, {"fail": b * c + d * e - f - F}, markov_hyps(_m2, _p2))
for tag, order in [("rs", b * c - d * e), ("sr", d * e - b * c)]:
    # all four entries >= 2; s <= r (tag rs) or r <= s (tag sr)
    B2 = H("b2") * H("b2") + 4 * H("b2")           # b^2 - 4
    C2 = H("c2") * H("c2") + 4 * H("c2")
    D2 = H("d2") * H("d2") + 4 * H("d2")
    E2 = H("e2") * H("e2") + 4 * H("e2")
    E2b = E2 + 2                                    # e^2 - 2
    B2b = B2 + 2
    if tag == "rs":
        Sm = H("d2") * H("e2") + 2 * H("d2") + 2 * H("e2") + 4      # s = de
        Sm4 = H("d2") * H("e2") + 2 * H("d2") + 2 * H("e2")         # s - 4
        Xm1 = H("nb1_lo") + H("f_lo")                                 # 2f - r - 1
        Ym1 = H("fail") + H("nb2_hi")                                 # r + 2s - 2f - 1
        cert = (4 * H("m3") + B2 * C2 + 2 * D2 * E2b + 4 * E2 + 2 * Sm * H("ord") + Xm1 * Ym1 + 2 * Sm4).cert()
    else:
        Sm = H("b2") * H("c2") + 2 * H("b2") + 2 * H("c2") + 4      # r = bc plays the role of s
        Sm4 = H("b2") * H("c2") + 2 * H("b2") + 2 * H("c2")
        Xm1 = H("nb2_lo") + H("f_lo")
        Ym1 = H("fail") + H("nb1_hi")
        cert = (4 * H("m3") + D2 * E2 + 2 * B2 * (C2 + 2) + 4 * C2 + 2 * Sm * H("ord") + Xm1 * Ym1 + 2 * Sm4).cert()
    Ineq("A1.sq_all2_" + tag, "App. A.1",
         "All four incident entries >= 2: 4m <= 16-(2s-1) <= 9 < 12, where s = min(bc,de).",
         hyps=merge(_sqfail, {"b2": b - 2, "c2": c - 2, "d2": d - 2, "e2": e - 2, "ord": order}),
         goal=("contra",), cert=cert)
TupleEq("A1.sq_sym1_relabel", "App. A.1",
        "(b,c,d,e) -> (c,b,e,d) is realized by reversing all arrows and exchanging 3,4.",
        S.srelabel(S.sreverse(S.as_poly_tuple(P2)), Q.PI34), (0, c, -b, e, -d, f))
TupleEq("A1.sq_sym2_relabel", "App. A.1",
        "(b,c,d,e) -> (d,e,b,c) is realized by exchanging 1,2.",
        S.srelabel(S.as_poly_tuple(P2), Q.PI12), (0, d, -e, b, -c, f))
SymmetryCheck("A1.sq_sym1", "App. A.1", "(b,c,d,e) -> (c,b,e,d) permutes the hypotheses of the commuting square.",
              _sqfail, {"b": c, "c": b, "d": e, "e": d})
SymmetryCheck("A1.sq_sym2", "App. A.1", "(b,c,d,e) -> (d,e,b,c) permutes the hypotheses of the commuting square.",
              _sqfail, {"b": d, "c": e, "d": b, "e": c})


def sub_hyps(hy, mapping, drop=()):
    return {k: val.substitute(mapping) for k, val in hy.items() if k not in drop}


# unit entry b = 1
_U = sub_hyps(_sqfail, {"b": 1}, drop=("b_lo", "b_hi"))
uu = f - c
vv = d * e - f
_mU = _m2.substitute({"b": 1})
Ineq("A1.u_d1", "App. A.1", "With b=1, d=1 is impossible (it would force e > F-1).",
     hyps=sub_hyps(_U, {"d": 1}, drop=("d_lo", "d_hi")), goal=("contra",))
Ineq("A1.u_e1", "App. A.1", "With b=1, e=1 is impossible.",
     hyps=sub_hyps(_U, {"e": 1}, drop=("e_lo", "e_hi")), goal=("contra",))
_U1 = sub_hyps(_U, {"c": 1}, drop=("c_lo", "c_hi"))
Ineq("A1.u_c1_f", "App. A.1", "With b=c=1, f >= F+1 is impossible, so f = F.",
     hyps=merge(_U1, {"fbig": f - F - 1}), goal=("contra",))
_U1F = sub_hyps(_U1, {"f": F}, drop=("f_lo",))
Ineq("A1.u_c1_dehi", "App. A.1", "With b=c=1 and f=F, de >= 2F is impossible.",
     hyps=merge(_U1F, {"dehi": d * e - 2 * F}), goal=("contra",))
Ineq("A1.u_c1_delo", "App. A.1", "With b=c=1 and f=F, de <= 2F-2 is impossible; hence de = 2F-1.",
     hyps=merge(_U1F, {"delo": 2 * F - 2 - d * e}), goal=("contra",))
for name, sub, other in [("A1.u_c1_d2", {"d": 2}, e), ("A1.u_c1_e2", {"e": 2}, d)]:
    hy = sub_hyps(_U1F, sub, drop=("d_lo", "d_hi") if "d" in sub else ("e_lo", "e_hi"))
    Ineq(name, "App. A.1", "de = 2F-1 is odd, so neither d nor e equals 2 (integer parity).",
         hyps=hy, eqs={"de": 2 * other - 2 * F + 1}, goal=("contra",),
         cert=Split(other - F + 1, ({"kind": "sum", "terms": [{"c": 2, "hyps": ["SPLIT"], "sq": None}],
                                 "eqs": [{"mult": Poly.coerce(-1), "eq": "de"}], "const": "auto"}),
                    ({"kind": "sum", "terms": [{"c": 2, "hyps": ["SPLIT"], "sq": None}],
                      "eqs": [{"mult": Poly.coerce(1), "eq": "de"}], "const": "auto"})))
_U1Fm = sub_hyps(merge(_U1F, {"d3": d - 3, "e3": e - 3}), {}, drop=())
W3 = (H("d3") * H("d3") + 6 * H("d3")) * (H("e3") * H("e3") + 6 * H("e3")) + 5 * (H("d3") * H("d3") + 6 * H("d3")) \
    + 5 * (H("e3") * H("e3") + 6 * H("e3"))
Ineq("A1.u_c1_main", "App. A.1",
     "With b=c=1, f=F, de=2F-1 and d,e>=3: (d^2-4)(e^2-4)>=25 gives m <= -F < 3.",
     hyps=_U1Fm, eqs={"de": d * e - 2 * F + 1}, goal=("contra",),
     cert=(4 * H("m3") + W3 + 4 * H("F4")).cert(eqs=[(-(d * e - 2 * F - 1), "de")]))
# c >= 2, d, e >= 2
_U2 = merge(_U, {"c2": c - 2, "d2": d - 2, "e2": e - 2})
Um1 = H("f_lo") + H("c_hi")
Vm1 = H("fail") + H("c_hi")
Ineq("A1.u_common", "App. A.1, eq. (zeroCommon)", "With b=1 and c,d,e>=2: m <= (d-e)^2 + 4.",
     hyps=_U2, goal=("ge0", (d - e) ** 2 + 4 - _mU),
     cert=Split(vv - uu,
                ((H("nb2_lo") + H("f_lo")) * (Um1 + Vm1) + Sq(uu - 1) + 3 * Um1 * (H("SPLIT") + 1) + Sq(vv - uu)).cert(),
                ((H("fail") + H("nb1_hi")) * (Um1 + Vm1) + Sq(vv - 1) + 3 * Vm1 * H("SPLIT") + Sq(uu - vv)).cert()))
Pu = H("f_lo") + H("d_hi")
Pv = H("fail") + H("d_hi")
Ineq("A1.u_case1_d", "App. A.1, case 1", "b=1, 2<=c<d, e<=d: m <= 4-(e-2)^2-2z < 3 with z=d-c.",
     hyps=merge(_U2, {"cd": d - 1 - c, "de_ord": d - e}), goal=("contra",),
     cert=(H("m3") + Sq(e - 2) + 2 * H("cd") + H("c2") * (H("d_lo") + 1) * H("e2") + 2 * H("de_ord") * H("e2")
           + (H("cd") + 2) * Pu + (H("cd") + 2) * Pv + Pu * Pv).cert())
Pu2 = H("f_lo") + H("e_hi")
Pv2 = H("fail") + H("e_hi")
Ineq("A1.u_case1_e", "App. A.1, case 1", "b=1, 2<=c<e, d<=e: the same estimate with d and e exchanged.",
     hyps=merge(_U2, {"ce": e - 1 - c, "ed_ord": e - d}), goal=("contra",),
     cert=(H("m3") + Sq(d - 2) + 2 * H("ce") + H("c2") * (H("e_lo") + 1) * H("d2") + 2 * H("ed_ord") * H("d2")
           + (H("ce") + 2) * Pu2 + (H("ce") + 2) * Pv2 + Pu2 * Pv2).cert())
Ineq("A1.u_case2", "App. A.1, case 2", "b=1, e<=d<=c: 2|p| = 2(cd-e) >= (d-e)^2+4 >= m, contradicting 2|p|<m.",
     hyps=merge(_U2, {"de_ord": d - e, "cd_ord": c - d}), goal=("contra",), uses=["A1.u_common"],
     cert=(H("use:A1.u_common") + H("m_p2") + Sq(d - e) + 4 * (H("e2") + 2) * H("de_ord")
           + 2 * H("e2") * (H("e2") + 3) + 2 * (H("d_lo") + 1) * H("cd_ord")).cert())
_U3 = sub_hyps(merge(_U2, {"ed": e - d - 1}), {"c": e})
Ineq("A1.u_case3_d2", "App. A.1, case 3", "b=1, d=2 < e=c: m <= 4 < 2e+1 <= 2|p|+1.",
     hyps=sub_hyps(_U3, {"d": 2}, drop=("d_lo", "d_hi", "d2")), goal=("contra",))
_U3b = merge(_U3, {"d3": d - 3})
Dp, Ep = H("d3"), H("ed")
um1 = H("f_lo") + H("c_hi")          # u - 1 = f - e - 1 (c = e)
vm1 = H("fail") + H("c_hi")          # v - 1
Ineq("A1.u_case3_d3", "App. A.1, case 3", "b=1, 3<=d<e=c: m - 2|p| < 0.",
     hyps=_U3b, goal=("contra",),
     cert=(H("m_p2") + (Dp + 1) * Ep * (Ep + 2 * Dp + 8) + um1 * vm1 + um1 + vm1 + 2 * (Ep + Dp + 4) * (Dp + 2)
           + Dp * Dp * Dp + 8 * Dp * Dp + 18 * Dp + 7).cert())
Ineq("A1.u_case4", "App. A.1, case 4", "b=1, d<e<c: f < de < 2(cd-e) < m <= F-1 < f.",
     hyps=merge(_U2, {"ed": e - d - 1, "ec": c - e - 1}), goal=("contra",))

# =============================================================================== A2: Lemma 4.3
# P = (1, b, -c, d, -e, f), b,c,d,e >= 1, f >= K+1; both neighbours have height <= K.
P3 = (1, b, -c, d, -e, f)
D3 = b * c + d * e + c * d
_m3 = 1 + b ** 2 + c ** 2 + d ** 2 + e ** 2 + b * d + c * e + f ** 2 - f * D3
_p3 = f + b * e - c * d


def lowK(name, expr):
    return {name + "_lo": expr + K, name + "_hi": K - expr}


_A2 = merge({"b1": b - 1, "c1": c - 1, "d1": d - 1, "e1": e - 1, "f_lo": f - K - 1, "K0": K,
             "Kb": K - b - d, "Kc": K - c - e}, lowK("nb1", f - b * c), lowK("nb2", f - d * e),
            markov_hyps(_m3, _p3, upper=False))
Identity("A2.markov", "App. A.2", "Markov value of P = (1,b,-c,d,-e,f) in the order 1<2<3<4.",
         S.smarkov(S.as_poly_tuple(P3), (1, 2, 3, 4)), _m3)
Identity("A2.pf", "App. A.2", "Pfaffian of P = (1,b,-c,d,-e,f).", S.spfaffian(S.as_poly_tuple(P3)), _p3)
_A2base = {k: val for k, val in _A2.items() if k in ("b1", "c1", "d1", "e1", "f_lo", "K0")}
Tuple("A2.neighbours1", "App. A.2", "mu_1 P = (-1,-b,c,d,-c-e,f-bc).",
      hyps=_A2base, start=P3, steps=[(1, (-1, -b, c, d, -c - e, f - b * c))])
Tuple("A2.neighbours2", "App. A.2", "mu_2 P = (-1,b+d,-c,-d,e,f-de).",
      hyps=_A2base, start=P3, steps=[(2, (-1, b + d, -c, -d, e, f - d * e))])
mu2P3 = S.as_poly_tuple((-1, b + d, -c, -d, e, f - d * e))
Tuple("A2.detour", "App. A.2",
      "From mu_1 P the detour [2,1,2] passes (1,-b,-e,-d,c+e,f-D), (-1,b,e,-b-d,c,f-D) and ends at (mu_2 P)^{pi_12}.",
      hyps=_A2base, start=(-1, -b, c, d, -c - e, f - b * c),
      steps=[(2, (1, -b, -e, -d, c + e, f - D3)), (1, (-1, b, e, -b - d, c, f - D3)), (2, None)],
      relabel=(Q.PI12, mu2P3))  # final^{pi_12} = mu_2 P, i.e. final = (mu_2 P)^{pi_12}
_A2f = merge(_A2, {"fail": D3 - f - K - 1})
for tag, XY in [("SU", ("b", "d", "c", "e")), ("US", ("c", "e", "b", "d"))]:
    x1, x2, y1, y2 = XY  # X = x1 + x2 (the larger of b+d, c+e), Y = y1 + y2
    hx = {"b": "b1", "d": "d2", "c": "c2", "e": "e1"}
    lows = {"b": 1, "d": 2, "c": 2, "e": 1}
    # Y - 3, Y + 1, 2Y - 4, X + 1 in terms of the hypotheses b1=b-1, d2=d-2, c2=c-2, e1=e-1
    Ym3 = H(hx[y1]) + H(hx[y2])
    Yp1 = Ym3 + 4
    Y2m4 = 2 * Ym3 + 2
    Xp1 = H(hx[x1]) + H(hx[x2]) + 4
    KX = "Kb" if x1 == "b" else "Kc"
    fX = H("f_lo") + H(KX)
    DfX = H("fail") + H(KX)
    bdce = H("b1") * H("d2") + 2 * H("b1") + H("d2") + H("c2") * H("e1") + H("c2") + 2 * H("e1")
    Dbound = H("b1") * H("c2") + H("e1") * H("d2") + H("c2") * (H("d2") + 1) + H("d2")
    Ineq("A2.cd2_" + tag, "App. A.2, case c,d >= 2",
         "c,d >= 2 and f - D < -K: m <= 2 + 2Y - Y^2 - (bd+ce-4) <= -1, contradicting m >= 3.",
         hyps=merge(_A2f, {"c2": c - 2, "d2": d - 2, "ord": (V(x1) + V(x2)) - (V(y1) + V(y2))}), goal=("contra",),
         cert=(H("m3") + Ym3 * Yp1 + bdce + H("ord") * Y2m4 + fX * DfX + Xp1 * Dbound).cert())
TupleEq("A2.sym_relabel", "App. A.2",
        "(b,c,d,e) -> (e,d,c,b) is realized by reversing all arrows and relabeling by (1 2)(3 4).",
        S.srelabel(S.sreverse(S.as_poly_tuple(P3)), (2, 1, 4, 3)), (1, e, -d, c, -b, f))
SymmetryCheck("A2.sym", "App. A.2", "(b,c,d,e) -> (e,d,c,b) permutes the hypotheses, so c=1 reduces to d=1.",
              _A2f, {"b": e, "c": d, "d": c, "e": b})

# ------------------------------------------------------------------ App. A.2, the case d = 1 (Appendix C of an earlier version)
_C = sub_hyps(_A2f, {"d": 1}, drop=("d1",))
Ineq("A2.d1_b1", "App. A.2, case d = 1", "d=1, b=1: D = 2c+e <= 2(c+e) <= 2K < 2K+2 <= D.",
     hyps=sub_hyps(_C, {"b": 1}, drop=("b1",)), goal=("contra",))
Ineq("A2.d1_c1", "App. A.2, case d = 1", "d=1, c=1: D = b+e+1 <= 2K-1 < 2K+2 <= D.",
     hyps=sub_hyps(_C, {"c": 1}, drop=("c1",)), goal=("contra",))
_C2 = merge(_C, {"b2": b - 2, "c2": c - 2})
Sb = b + 1
Uc = c + e
fXS = H("f_lo") + H("Kb")          # f - S - 1 with S = b+1
DfXS = H("fail") + H("Kb")
B2 = H("b2")
Ineq("A2.d1_SU", "App. A.2, case d = 1", "d=1, S=b+1 >= U=c+e: m - 2p <= -5, contradicting 2|p| < m.",
     hyps=merge(_C2, {"ord": Sb - Uc}), goal=("contra",),
     cert=(H("m_2p") + 6 * B2 + (H("c2") + H("e1")) * (H("ord") + 2 * B2 + 2) + H("c2") * (B2 + 3) * (B2 + 1)
           + (H("c2") + 2) * H("e1") + fXS * DfXS + 2 * fXS).cert())
fXU = H("f_lo") + H("Kc")
DfXU = H("fail") + H("Kc")
Dm = H("f_lo") + H("fail") + 2 * H("Kc")     # c(S-1) - U - 2 = D - 2U - 2
Ssum = B2 + 3                                # S = b + 1
cS = H("c2") + 2                             # c
Ineq("A2.d1_US_i", "App. A.2, case d = 1", "d=1, U >= S, c <= S-1: m - 2p <= B(S) <= -5.",
     hyps=merge(_C2, {"ord": Uc - Sb, "cS": Sb - 1 - c}), goal=("contra",),
     cert=(H("m_2p") + H("ord") * (Dm + cS + Ssum + 1) + fXU * DfXU + 2 * fXU + cS * H("cS")
           + H("c2") * Ssum * (B2 + 1) + 2 * B2 * (B2 + 4)).cert())
S3 = B2  # S - 3 = b - 2
Ineq("A2.d1_US_ii", "App. A.2, case d = 1", "d=1, U >= S, c >= S-1: m - 2p <= B(c+1) <= -5.",
     hyps=merge(_C2, {"ord": Uc - Sb, "Sc": c + 1 - Sb}), goal=("contra",),
     cert=(H("m_2p") + H("e1") * (Dm + 2 * Ssum) + fXU * DfXU + 2 * fXU
           + (B2 + 1) * H("Sc") * (H("Sc") + 2 * Ssum) + S3 * S3 * S3 + 6 * S3 * S3 + 11 * S3).cert())

# =============================================================================== A3: Lemma 4.4
x3, x4, y3, y4, q, mm_ = (V(n) for n in "x3 x4 y3 y4 q m".split())
_gen = merge({"a2": a - 2, "F4": F - 4})
# entries incident to 2 cannot equal F: if b23 = F becomes low at mu_1 then b13 < 0, and mu_2 gives b13 + aF > F
P0 = (a, y, z, F, w, q)
Tuple("A3.b23_mu1_ypos", "App. A.3", "If b13 >= 0, mutation at 1 leaves b23 = F unchanged.",
      hyps=merge(_gen, {"y0": y}), start=P0, steps=[(1, {(2, 3): F})])
Tuple("A3.b23_mu1_yneg", "App. A.3", "If b13 <= 0, mutation at 1 replaces b23 = F by F + a*b13.",
      hyps=merge(_gen, {"y0": -y}), start=P0, steps=[(1, {(2, 3): F + a * y})])
Tuple("A3.b23_mu2", "App. A.3", "Mutation at 2 replaces b13 by b13 + aF.",
      hyps=_gen, start=P0, steps=[(2, {(1, 3): y + a * F})])
Ineq("A3.b23_big", "App. A.3", "If b13 >= -(F-1) then b13 + aF > F, so mu_2 leaves height F.",
     hyps=merge(_gen, {"y_lo": y + F - 1, "ht": F - (y + a * F)}), goal=("contra",))
Tuple("A3.b23m_mu1_ypos", "App. A.3", "b23 = -F is unchanged by mutation at 1 when b13 >= 0.",
      hyps=merge(_gen, {"y0": y}), start=(a, y, z, -F, w, q), steps=[(1, {(2, 3): -F})])
Tuple("A3.b23m_mu1", "App. A.3", "b23 = -F stays <= -F after mutation at 1 (case b13 <= 0).",
      hyps=merge(_gen, {"y0": -y}), start=(a, y, z, -F, w, q), steps=[(1, {(2, 3): -F + a * y})])
P4 = (a, b, -c, d, E, F)
_m4 = S.smarkov(S.as_poly_tuple(P4), (1, 2, 3, 4))
_p4 = a * F - b * E - c * d
Identity("A3.pf", "App. A.3", "p = aF - bE - cd.", S.spfaffian(S.as_poly_tuple(P4)), _p4)
_A3 = merge({"a2": a - 2, "a_hi": F - 1 - a, "b1": b - 1, "c1": c - 1, "b_hi": F - 1 - b, "c_hi": F - 1 - c,
             "F4": F - 4}, low("d", d), low("E", E))
_A3m = merge(_A3, {"mT": F - 1 - mm_, "m_2p": mm_ - 2 * _p4 - 1, "m_p2": mm_ + 2 * _p4 - 1})
Tuple("A3.nb1", "App. A.3", "mu_1 P has b24 = E - ac.", hyps=_A3, start=P4, steps=[(1, {(2, 4): E - a * c})])
Tuple("A3.nb2", "App. A.3", "mu_2 P has b13 = b + ad when d >= 0.", hyps=merge(_A3, {"d0": d}), start=P4,
      steps=[(2, {(1, 3): b + a * d})])
Tuple("A3.mu2_dneg_Epos", "App. A.3", "If d <= 0 <= E, mutation at 2 makes b34 = F - dE.",
      hyps=merge(_A3, {"dn": -d, "Ep": E}), start=P4, steps=[(2, {(3, 4): F - d * E})])
Ineq("A3.dneg_Epos", "App. A.3", "d<0<E is impossible.",
     hyps=merge(_A3, {"dn": -d - 1, "Ep": E - 1, "ht": F - (F - d * E)}), goal=("contra",))
Ineq("A3.dneg_Enonpos", "App. A.3", "d<0, E<=0 give p >= aF >= 2F, contradicting 2|p| < m <= F-1.",
     hyps=merge(_A3m, {"dn": -d - 1, "Enp": -E}), goal=("contra",))
Ineq("A3.d0_Eneg", "App. A.3", "d=0, E<0 give p >= 2F as well.",
     hyps=sub_hyps(merge(_A3m, {"Eneg": -E - 1}), {"d": 0}, drop=("d_lo", "d_hi")), goal=("contra",))
xx_ = b + (a - 1) * d
yy_ = c - E
Bk = d * (b + a * d) + c * E + F * d * E
Identity("A3.identity1", "App. A.3", "m = a^2+x^2+y^2-Fxy-(a-1)F^2+Fp-(a-2)(d(b+ad)+cE+FdE), x=b+(a-1)d, y=c-E.",
         _m4, a ** 2 + xx_ ** 2 + yy_ ** 2 - F * xx_ * yy_ - (a - 1) * F ** 2 + F * _p4 - (a - 2) * Bk)
_A3c1 = merge(sub_hyps(_A3, {}, ()), {"E0": E, "Ec": c - 1 - E, "nb": F - b - a * d},
              markov_hyps(_m4, _p4))
al = H("a2")
Gpos = (2 * al + 1) * H("a_hi") * (H("a_hi") + 2 * al + 6) + 4 * H("a_hi") + 2 * al * al * al + 11 * al * al + 20 * al
for tag, extra, sub in [("d1", {"d1": d - 1}, {}), ("d0", {}, {"d": 0})]:
    hy = sub_hyps(merge(_A3c1, extra), sub, drop=("d_lo", "d_hi") if sub else ())
    if tag == "d1":
        dd = H("d1") + 1
        xm1 = H("b1") + (al + 1) * dd                 # x - 1
        Fx = H("nb") + H("d1")                         # F - 1 - x
        Bkp = dd * (H("b1") + 1 + (al + 2) * dd) + (H("c1") + 1) * H("E0") + (H("F4") + 4) * dd * H("E0")
    else:
        xm1 = H("b1")
        Fx = H("b_hi")
        Bkp = (H("c1") + 1) * H("E0")
    ym1 = H("Ec")
    Fy = H("c_hi") + H("E0")
    Rect = xm1 * Fx + ym1 * Fy + (H("F4") + 4) * xm1 * ym1
    Ineq("A3.case_Esmall_" + tag, "App. A.3",
         "d>=0, 0<=E<c: the rectangle bound and 2p <= F-2 give 2m <= 2a^2+4-4F-(2a-3)F^2 < 6.",
         hyps=hy, goal=("contra",),
         cert=(2 * H("m3") + 2 * Rect + (H("F4") + 4) * (H("m_2p") + H("mT")) + 2 * al * Bkp + Gpos).cert())
# case d >= 1, E = -e < 0
P4e = (a, b, -c, d, -e, F)
_m4e = S.smarkov(S.as_poly_tuple(P4e), (1, 2, 3, 4))
_p4e = a * F + b * e - c * d
_A3c2 = merge({"a2": a - 2, "a_hi": F - 1 - a, "b1": b - 1, "c1": c - 1, "d1": d - 1, "e1": e - 1, "F4": F - 4,
               "nb": F - b - a * d, "n1": F - 1 - a * c - e}, markov_hyps(_m4e, _p4e))
Identity("A3.identity2", "App. A.3",
         "m = a^2+(b^2+d^2+abd)+(c^2+e^2+ace)-(a^2-1)F^2+apF-F(bc+de+abe) for E=-e.",
         _m4e, a ** 2 + (b ** 2 + d ** 2 + a * b * d) + (c ** 2 + e ** 2 + a * c * e) - (a ** 2 - 1) * F ** 2
         + a * _p4e * F - F * (b * c + d * e + a * b * e))
dd = H("d1") + 1
cc = H("c1") + 1
ee = H("e1") + 1
bb = H("b1") + 1
FF = H("F4") + 4
xv = bb + (al + 1) * dd                       # x = b + (a-1)d
wv = (al + 2) * cc + ee                       # w = ac + e
Fx = H("nb") + H("d1")                        # F-1-x
Fw = H("n1")                                  # F-1-w
G2 = al * (2 * al + 7) * Sq(F) + (2 * al + 12) * H("a_hi") + 10 * al
Ineq("A3.case_Eneg", "App. A.3", "d>0>E: 2m <= -(2a^2-a-6)F^2+2a^2-8F-2aF+4 < 6.",
     hyps=_A3c2, goal=("contra",),
     cert=(2 * H("m3") + 2 * Fx * (Fx + 2 * xv) + 2 * Fw * (Fw + 2 * wv) + 2 * al * dd * (bb + (al + 2) * dd)
           + 2 * (al + 1) * (al + 3) * cc * cc + 2 * (al + 2) * cc * ee + (al + 2) * FF * (H("m_2p") + H("mT"))
           + 2 * FF * (bb * cc + dd * ee + (al + 2) * bb * ee) + G2).cert())
# remaining case d >= 0, E >= c
_A3r = merge(_A3, {"d0": d, "Ec": E - c})
Tuple("A3.mu2_rest", "App. A.3", "For d>=0, E>=c: mu_2 P = (-a, b+ad, aE-c, -d, -E, F).",
      hyps=_A3r, start=P4, steps=[(2, (-a, b + a * d, a * E - c, -d, -E, F))])
Ineq("A3.gamma_ge_E", "App. A.3", "gamma = aE - c >= E.", hyps=_A3r, goal=("ge0", a * E - c - E))
mu2P4 = (-a, b + a * d, a * E - c, -d, -E, F)
Tuple("A3.mu2_then3", "App. A.3", "Then mutation at 3 creates b14 = gamma + beta*F.",
      hyps=_A3r, start=mu2P4, steps=[(3, {(1, 4): a * E - c + (b + a * d) * F})])
Ineq("A3.mu2_then3_big", "App. A.3", "gamma + beta*F > F.",
     hyps=merge(_A3r, {"ht": F - (a * E - c + (b + a * d) * F)}), goal=("contra",),
     cert=(H("ht") + (al + 1) * (H("Ec") + H("c1")) + al + H("Ec") + (H("b1") + (al + 2) * H("d0")) * (H("F4") + 4)).cert())
Tuple("A3.mu2_then4", "App. A.3", "Mutation at 4 instead creates b23 = -d - EF.",
      hyps=_A3r, start=mu2P4, steps=[(4, {(2, 3): -d - E * F})])
Ineq("A3.mu2_then4_d", "App. A.3", "If d >= 1 then |b23| = d + EF > F.",
     hyps=merge(_A3r, {"d1": d - 1, "ht": F - (d + E * F)}), goal=("contra",))
Ineq("A3.mu2_then4_E", "App. A.3", "If E >= 2 then |b23| = d + EF > F.",
     hyps=merge(_A3r, {"E2": E - 2, "ht": F - (d + E * F)}), goal=("contra",))
_mexc = _m4.substitute({"d": 0, "E": 1, "c": 1})
Identity("A3.exception_m", "App. A.3", "For d=0, E=c=1: m = a^2+b^2+F^2-a-bF+2.", _mexc,
         a ** 2 + b ** 2 + F ** 2 - a - b * F + 2)
Ineq("A3.exception", "App. A.3", "For d=0, E=c=1: 4m = 4a^2-4a+8+(2b-F)^2+3F^2 > 4F, contradicting m <= F-1.",
     hyps={"a2": a - 2, "mT": F - 1 - _mexc, "F4": F - 4}, goal=("contra",),
     cert=(4 * H("mT") + Sq(2 * b - F) + 4 * (H("a2") + 2) * (H("a2") + 1) + 3 * H("F4") * H("F4") + 20 * H("F4")).cert())
Tuple("A3.mu1_after", "App. A.3", "Mutation at 1 then gives (a, -beta, -gamma, a*beta-d, a*gamma-E, F).",
      hyps=_A3r, start=mu2P4, steps=[(1, (a, -(b + a * d), -(a * E - c), a * (b + a * d) - d, a * (a * E - c) - E, F))])
Ineq("A3.form_beta", "App. A.3", "a*beta - d >= beta >= 1.", hyps=_A3r, goal=("ge0", a * (b + a * d) - d - (b + a * d)),
     cert=((al + 1) * (H("b1") + 1) + (al * al + 3 * al + 1) * H("d0")).cert())
Ineq("A3.form_gamma", "App. A.3", "a*gamma - E >= gamma >= 1.", hyps=_A3r,
     goal=("ge0", a * (a * E - c) - E - (a * E - c)), uses=["A3.gamma_ge_E"])
# the invariant form W = (a, -x3, -x4, y3, y4, F) with a >= 2 and 1 <= x_k <= y_k
Wf = (a, -x3, -x4, y3, y4, F)
_W = {"a2": a - 2, "x3": x3 - 1, "x4": x4 - 1, "y3x3": y3 - x3, "y4x4": y4 - x4, "F4": F - 4}
Tuple("A3.W_mu3", "App. A.3", "From W, mutation at 3 creates b24 = y4 + y3 F.", hyps=_W, start=Wf,
      steps=[(3, {(2, 4): y4 + y3 * F})])
Ineq("A3.W_mu3_big", "App. A.3", "y4 + y3 F > F.", hyps=merge(_W, {"ht": F - (y4 + y3 * F)}), goal=("contra",))
Tuple("A3.W_mu4", "App. A.3", "From W, mutation at 4 creates b13 = -x3 - x4 F.", hyps=_W, start=Wf,
      steps=[(4, {(1, 3): -x3 - x4 * F})])
Ineq("A3.W_mu4_big", "App. A.3", "x3 + x4 F > F.", hyps=merge(_W, {"ht": F - (x3 + x4 * F)}), goal=("contra",))
Tuple("A3.W_mu2", "App. A.3", "Mutation at 2 and the swap of 1,2 give (a, -y3, -y4, a y3 - x3, a y4 - x4, F).",
      hyps=_W, start=Wf, steps=[(2, None)], relabel=(Q.PI12, (a, -y3, -y4, a * y3 - x3, a * y4 - x4, F)))
for k_, (X_, Y_) in (("3", (x3, y3)), ("4", (x4, y4))):
    Ineq("A3.W_form" + k_, "App. A.3", "a*y - x >= y >= 1, so the new columns have the same form.",
         hyps=_W, goal=("ge0", a * Y_ - X_ - Y_))

# =============================================================================== B1: the prefix is [1,2]
# Normal form C = (1, -b, c, d, -E, F - bc) with b, c, d, E >= 1 and d <= b - 1.
CB = (1, -b, c, d, -E, F - b * c)
_B1t = {"b1": b - 1, "c1": c - 1, "d1": d - 1, "E1": E - 1, "db": b - 1 - d, "F4": F - 4}
Tuple("B1.prefix", "App. B.1", "The quivers after [1], [1,2], [1,2,1].", hyps=_B1t, start=CB,
      steps=[(1, (-1, b, -c, d - b, -E, F)), (2, (1, d, -c - E, b - d, E, F)),
             (1, (-1, -d, c + E, b - d, -c, F - d * (c + E)))])
Cgen = (1, x, c, d, -E, f)
Tuple("B1.mu2C", "App. B.1", "For d >= 0 >= -E, mu_2 C has b13 = x+d, b14 = c, b34 = f - dE.",
      hyps={"d0": d, "E0": E}, start=Cgen, steps=[(2, {(1, 3): x + d, (1, 4): c, (3, 4): f - d * E})])
Tuple("B1.mu1C", "App. B.1", "For x = -b <= 0 and c >= 0, mu_1 C has b34 = f + bc.",
      hyps={"b0": b, "c0": c}, start=(1, -b, c, d, -E, f), steps=[(1, {(3, 4): f + b * c})])
Pattern("B1.order", "App. B.1 and B.2.1",
        "C = (1,-b,c,d,-E,f) with b,c,d,E > 0 (any f) has at most one proper wiggle class, containing <1,4,2,3>.",
        hyps={"b1": b - 1, "c1": c - 1, "d1": d - 1, "E1": E - 1}, entries=(1, -b, c, d, -E, f),
        spec=["+", "-", "+", "+", "-", "*"],
        prop=CC.prop_at_most_one_proper_class_containing((1, 4, 2, 3)), prop_name="unique class <1423>")
_mB1 = S.smarkov(S.as_poly_tuple(CB), (1, 4, 2, 3))
_pB1 = S.spfaffian(S.as_poly_tuple(CB))
Identity("B1.markov", "App. B.1", "m = 1+b^2+c^2+d^2+E^2+cE-bd+F^2-F(bc+dE) in the order <1,4,2,3>.",
         _mB1, 1 + b ** 2 + c ** 2 + d ** 2 + E ** 2 + c * E - b * d + F ** 2 - F * (b * c + d * E))
Identity("B1.pf", "App. B.1", "p = F - b(c+E) + cd.", _pB1, F - b * (c + E) + c * d)
_B1 = merge(_B1t, low("f", F - b * c), {"mu2C": b * c + d * E - 2 * F - 1, "q2": F - c - E},
            markov_hyps(_mB1, _pB1))
Ineq("B1.ce_b2", "App. B.1", "c+E=F and b=2 (so d=1): bc+dE = F+c < 2F, contradiction.",
     hyps={"c_hi": F - 1 - c, "mu2C": 2 * c + (F - c) - 2 * F - 1}, goal=("contra",))
_B1ce = merge(sub_hyps(_B1, {"E": F - c}, drop=("q2",)), {"b3": b - 3})
Identity("B1.ce_identity", "App. B.1", "b(-2p-F) = F(2b^2-3b-4d) + 2d(2F-bc) when E = F-c.",
         (b * (-2 * _pB1 - F)).substitute({"E": F - c}), F * (2 * b ** 2 - 3 * b - 4 * d) + 2 * d * (2 * F - b * c))
Ineq("B1.ce", "App. B.1", "c+E=F, b>=3: -2p > F, contradicting 2|p| < m <= F-1.",
     hyps=_B1ce, goal=("contra",),
     cert=((H("b3") + 3) * (H("m_p2") + H("mT")) + (H("F4") + 4) * (4 * H("db") + H("b3") * (2 * H("b3") + 5) + 1)
           + 2 * (H("d1") + 1) * (H("f_lo") + 1) + 2 * H("b3")).cert())
# case d(c+E) = 2F with L = c+E <= F-1; write b = d + z with z >= 1
_mz = _mB1.substitute({"b": d + z})
_B1dl = {"d3": d - 3, "d_hi": F - 1 - d, "L3": c + E - 3, "L_hi": F - 1 - c - E, "c1": c - 1, "E1": E - 1,
         "z1": z - 1, "b_hi": F - 1 - d - z, "F5": F - 5, "F2": F + 2, "m3": _mz - 3}
Ineq("B1.dl_F5", "App. B.1", "d, c+E >= 3 and d(c+E) = 2F force F >= 5.",
     hyps={"d3": d - 3, "L3": c + E - 3, "F4lo": F - 4, "F4hi": 4 - F}, eqs={"dl": d * (c + E) - 2 * F},
     goal=("contra",))
for nm, small in [("B1.dl_d3", "d"), ("B1.dl_L3", "L")]:
    hy = {"d1": d - 1, "L1": c + E - 1, "d_hi": F - 1 - d, "L_hi": F - 1 - c - E, "F4": F - 4}
    hy["small"] = (2 - d) if small == "d" else (2 - c - E)
    Ineq(nm, "App. B.1", "d(c+E) = 2F with d, c+E <= F-1 forces d, c+E >= 3 (Lemma A.2).",
         hyps=hy, eqs={"dl": d * (c + E) - 2 * F}, goal=("contra",))
Lp = c + E
Nz = (H("z1") + 1) * H("b_hi") + (H("F5") + 5) * (H("z1") + 1) * H("c1") + H("z1")   # -(1+z^2+dz-Fcz)
PB2v = 3 * H("d3") * H("d_hi") + 3 * H("L3") * H("L_hi") + H("F2") * H("d3") * H("L3")
_dleqs = {"dl": d * (c + E) - 2 * F}
_dlhy = dict(_B1dl)
Ineq("B1.dl", "App. B.1", "d(c+E) = 2F: 3m <= -F^2-5F+36-3cE < 9, contradicting m >= 3.",
     hyps=_dlhy, eqs=_dleqs, goal=("contra",),
     cert=fit_eq_multipliers(_dlhy, _dleqs, ("contra",),
                             3 * H("m3") + PB2v + 3 * (H("c1") + 1) * (H("E1") + 1) + 3 * Nz
                             + H("F5") * (H("F5") + 15), deg=2))

# =============================================================================== B2.1: x = -b < 0 < d
mf = mm_   # a free variable for the (unknown) transported Markov value where only 2|p| < m <= F-1 is used


def pbounds(p_expr):
    """2|p| < m <= F-1 with m free."""
    return {"mT": F - 1 - mf, "m_2p": mf - 2 * p_expr - 1, "m_p2": mf + 2 * p_expr - 1}


C21 = (1, -b, c, d, e, f)
_C21 = merge({"b1": b - 1, "d1": d - 1, "b_hi": F - 1 - b, "d_hi": F - 1 - d, "F4": F - 4},
             low("c", c), low("e", e), low("f", f))
Tuple("B21.P_cpos", "App. B.2.1", "For c > 0: mu_1 C = (-1, b, -c, d-b, e, f+bc).",
      hyps=merge(_C21, {"c1": c - 1}), start=C21, steps=[(1, (-1, b, -c, d - b, e, f + b * c))])
# --- c > 0, d = b - r < b
Pa = (-1, b, -c, -r, e, F)
_Pa = {"b1": b - 1, "c1": c - 1, "r1": r - 1, "F4": F - 4, "c_hi": F - 1 - c}
Tuple("B21.a_Q_epos", "App. B.2.1", "d<b, e>=0: Q = mu_2 P = (1, d, -c, r, -e, F+re).",
      hyps=merge(_Pa, {"e0": e}), start=Pa, steps=[(2, (1, b - r, -c, r, -e, F + r * e))])
Tuple("B21.a_Q_eneg", "App. B.2.1", "d<b, e<=0: Q = (1, d, -c+e, r, -e, F) and mu_3 Q = (1,-d,-c+e+dF,-r,-e+rF,-F).",
      hyps=merge(_Pa, {"e0": -e, "d1": b - r - 1}), start=Pa,
      steps=[(2, (1, b - r, -c + e, r, -e, F)), (3, (1, -(b - r), -c + e + (b - r) * F, -r, -e + r * F, -F))])
Ineq("B21.a_epos", "App. B.2.1", "e > 0 makes b34(Q) = F + re > F.",
     hyps=merge(_Pa, {"e1": e - 1, "ht": F - (F + r * e)}), goal=("contra",))
Ineq("B21.a_eneg", "App. B.2.1", "e < 0 makes b24(mu_3 Q) = -e + rF > F.",
     hyps=merge(_Pa, {"en": -e - 1, "ht": F - (-e + r * F)}), goal=("contra",))
Ineq("B21.a_r", "App. B.2.1", "e = 0: b24(mu_3 Q) = rF <= F forces r = 1.",
     hyps=merge(_Pa, {"r2": r - 2, "ht": F - r * F}), goal=("contra",))
Ineq("B21.a_d", "App. B.2.1", "e = 0, r = 1: b14(mu_3 Q) = dF - c <= F forces d = 1, so b = 2 and C = A_c.",
     hyps=merge(_Pa, {"d2": d - 2, "ht": F - (d * F - c)}), goal=("contra",))
# --- c > 0, d = b + r > b
_pC21 = S.spfaffian(S.as_poly_tuple(C21))
Identity("B21.b_pf", "App. B.2.1", "With d = b+r and f = F-bc: p = F + rc + be.",
         _pC21.substitute({"d": b + r, "f": F - b * c}), F + r * c + b * e)
Ineq("B21.b_epos", "App. B.2.1", "b<d, e>=0: p >= F, contradicting 2|p| < m <= F-1.",
     hyps=merge({"b1": b - 1, "c1": c - 1, "r1": r - 1, "e0": e}, pbounds(F + r * c + b * e)), goal=("contra",))
Pb = (-1, b, -c, r, -E, F)
_Pb = {"b1": b - 1, "c1": c - 1, "r1": r - 1, "E1": E - 1, "F4": F - 4}
Tuple("B21.b_Q", "App. B.2.1", "b<d, e=-E<0: Q = mu_2 P = (1, b, -c-E, -r, E, F-rE).",
      hyps=_Pb, start=Pb, steps=[(2, (1, b, -c - E, -r, E, F - r * E))])
Qb = (1, b, -c - E, -r, E, F - r * E)
Tuple("B21.b_mu3Q_a", "App. B.2.1", "If rE >= F: mu_3 Q has b12 = 1+br and b24 = E - r(rE-F).",
      hyps=merge(_Pb, {"rEF": r * E - F}), start=Qb, steps=[(3, {(1, 2): 1 + b * r, (2, 4): E - r * (r * E - F)})])
Tuple("B21.b_mu3Q_b", "App. B.2.1", "If rE <= F: mu_3 Q has b12 = 1+br and b24 = E.",
      hyps=merge(_Pb, {"rEF": F - r * E}), start=Qb, steps=[(3, {(1, 2): 1 + b * r, (2, 4): E})])
Ineq("B21.b_rE2", "App. B.2.1", "rE = 2F with E <= F-1 forces r >= 3.",
     hyps={"r1": r - 1, "r_le2": 2 - r, "E_hi": F - 1 - E, "E1": E - 1, "F4": F - 4}, eqs={"rE": r * E - 2 * F},
     goal=("contra",))
Ineq("B21.b_rE3", "App. B.2.1", "rE = 2F, r >= 3: b24(mu_3 Q) = E - rF < -F.",
     hyps={"r3": r - 3, "E_hi": F - 1 - E, "E1": E - 1, "F4": F - 4, "ht": E - r * F + F}, eqs={"rE": r * E - 2 * F},
     goal=("contra",))
_mpos = S.smarkov(S.as_poly_tuple((1, -b, c, d, -E, f)), (1, 4, 2, 3))
Identity("B21.markov_1423", "App. B.2.1, eq. (positive-order-markov)",
         "M in the order <1,4,2,3> for C = (1,-b,c,d,-E,f).",
         _mpos, 1 + b ** 2 + c ** 2 + d ** 2 + E ** 2 + f ** 2 + c * E + b * c * f - b * d - d * E * f - b * c * d * E)
_EF = F - c   # E = F - c in the remaining subcases
_mred = _mpos.substitute({"d": b + r, "E": _EF, "f": F - b * c})
_pred = S.spfaffian(S.as_poly_tuple((1, -b, c, d, -E, f))).substitute({"d": b + r, "E": _EF, "f": F - b * c})
Identity("B21.b_reduced", "App. B.2.1", "With d=b+r, E=F-c, f=F-bc: m = 1+b^2+br+r^2-(b-2)F^2-rFE-cE.",
         _mred, (1 + b ** 2 + b * r + r ** 2 - (b - 2) * F ** 2 - r * F * E - c * E).substitute({"E": _EF}))
Identity("B21.b_reduced_p", "App. B.2.1", "... and p = (r+1)c - (b-1)E.", _pred,
         ((r + 1) * c - (b - 1) * E).substitute({"E": _EF}))
_B21b = {"r1": r - 1, "c1": c - 1, "c_hi": F - 1 - c, "d_hi": F - 1 - b - r, "F4": F - 4}
Ineq("B21.b_b3", "App. B.2.1", "b >= 3: m <= 1+(b+r)^2-F^2 <= 2-2F < 3.",
     hyps=merge(_B21b, {"b3": b - 3, "m3": _mred - 3}), goal=("contra",),
     cert=(H("m3") + (H("b3") + 3) * (H("r1") + 1) + H("b3") * Sq(F) + (H("r1") + 1) * (H("F4") + 4) * H("c_hi")
           + (H("r1") + 1) * (H("F4") + 4) + (H("c1") + 1) * (H("c_hi") + 1)
           + H("d_hi") * (H("d_hi") + 2 * (H("b3") + 3) + 2 * (H("r1") + 1)) + 2 * H("F4")).cert())
_mb2 = _mred.substitute({"b": 2})
Identity("B21.b_b2_identity", "App. B.2.1", "b = 2: m = 6+2r+r^2-(r+1)F-(E-1)((r+1)F-E-1).",
         _mb2, (6 + 2 * r + r ** 2 - (r + 1) * F - (E - 1) * ((r + 1) * F - E - 1)).substitute({"E": _EF}))
Ineq("B21.b_b2", "App. B.2.1", "b = 2: m <= 3-2r <= 1.",
     hyps=merge(sub_hyps(_B21b, {"b": 2}), {"m3": _mb2 - 3}), goal=("contra",),
     cert=(H("m3") + 2 * H("r1") + (H("r1") + 2) * H("d_hi") + H("c_hi") * ((H("r1") + 1) * (H("F4") + 4) + H("c1"))).cert())
_pb1 = _pred.substitute({"b": 1})
Ineq("B21.b_b1_E", "App. B.2.1", "b = 1: p = (r+1)c > 0 and 2p < m <= F-1 = c+E-1 give E >= (2r+1)c + 2.",
     hyps=merge(sub_hyps(_B21b, {"b": 1}), pbounds(_pb1)), goal=("ge0", _EF - (2 * r + 1) * c - 2))
Pattern("B21.b_b1_triangle", "App. B.2.1",
        "b = 1: C = (1,-1,c,1+r,-E,E) contains the oriented triangle 2 -> 3 -> 4 -> 2.",
        hyps={"r1": r - 1, "E1": E - 1, "c1": c - 1}, entries=(1, -1, c, 1 + r, -E, E), spec=["+", "-", "+", "+", "-", "+"],
        prop=CC.prop_oriented_triangle(2, 3, 4), prop_name="oriented triangle 234")
Ineq("B21.b_b1_markov3", "App. B.2.1",
     "b = 1: the triangle (r+1, E, E) has Markov constant (r+1)^2-(r-1)E^2 <= 4 (all weights >= 2).",
     hyps={"r1": r - 1, "c1": c - 1, "Ebig": E - (2 * r + 1) * c - 2}, goal=("ge0", 4 - ((r + 1) ** 2 + 2 * E ** 2 - (r + 1) * E ** 2)),
     cert=(H("r1") * ((H("Ebig") + (2 * (H("r1") + 1) + 1) * H("c1"))
                      * (H("Ebig") + (2 * (H("r1") + 1) + 1) * (H("c1") + 1) + 2 * (H("r1") + 1) + 5)
                      + 4 * (H("r1") + 1) * (H("r1") + 1) + 11 * (H("r1") + 1) + 6)).cert())
# --- c > 0, d = b
Identity("B21.c_pf", "App. B.2.1", "d = b, f = F-bc: p = F + be.", _pC21.substitute({"d": b, "f": F - b * c}), F + b * e)
Ineq("B21.c_epos", "App. B.2.1", "d = b, e >= 0: p >= F, contradiction.",
     hyps=merge({"b1": b - 1, "e0": e}, pbounds(F + b * e)), goal=("contra",))
Pc = (-1, b, -c, 0, -E, F)
Tuple("B21.c_Q", "App. B.2.1", "d = b, e = -E: Q = (1, b, -c-E, 0, E, F) and b14(mu_3 Q) = bF - c - E.",
      hyps=_Pb, start=Pc, steps=[(2, (1, b, -c - E, 0, E, F)), (3, {(1, 4): b * F - c - E})])
Ineq("B21.c_b3", "App. B.2.1", "d = b: bF - c - E <= F forces b <= 2.",
     hyps={"b3": b - 3, "c_hi": F - 1 - c, "E_hi": F - 1 - E, "F4": F - 4, "ht": F - (b * F - c - E)}, goal=("contra",))
_mc1 = _mpos.substitute({"b": 1, "d": 1})
Identity("B21.c_b1_m", "App. B.2.1", "b = d = 1: m = 2+c^2+E^2+f^2+cf-Ef.", _mc1,
         2 + c ** 2 + E ** 2 + f ** 2 + c * f - E * f)
Ineq("B21.c_b1", "App. B.2.1", "b = d = 1 (F = c+f): m - F = 2+c(c-1)+cf+(E-f)^2+f(E-1) > 0.",
     hyps={"c1": c - 1, "f1": f - 1, "E1": E - 1, "mT": (c + f) - 1 - _mc1}, goal=("contra",),
     cert=(H("mT") + (H("c1") + 1) * H("c1") + (H("c1") + 1) * (H("f1") + 1) + Sq(E - f) + (H("f1") + 1) * H("E1")).cert())
_mc2 = _mpos.substitute({"b": 2, "d": 2, "E": F - c, "f": F - 2 * c})
Identity("B21.c_b2_m", "App. B.2.1", "b = d = 2, c+E = F: m = 5 - cE.", _mc2, (5 - c * E).substitute({"E": F - c}))
Ineq("B21.c_b2", "App. B.2.1", "b = d = 2: cE <= 2 forces c+E <= 3 < F.",
     hyps={"c1": c - 1, "E1": F - c - 1, "F4": F - 4, "m3": _mc2 - 3}, goal=("contra",))
# --- c = -t <= 0 (then e = -v, t + v = F)
_Cn = (1, -b, -t, d, -(F - t), f)
Tuple("B21.n_P", "App. B.2.1", "For c = -t <= 0: mu_1 C = (-1, b, t, d-b, e-t, f).",
      hyps={"b1": b - 1, "t0": t, "d1": d - 1}, start=(1, -b, -t, d, e, f), steps=[(1, (-1, b, t, d - b, e - t, f))])
Pattern("B21.n_vortex", "App. B.2.1", "If f < 0 then C = (1,-b,-t,d,-v,f) is a vortex (4 is a source).",
        hyps={"b1": b - 1, "t1": t - 1, "d1": d - 1, "v1": F - t - 1, "fneg": -f - 1}, entries=_Cn,
        spec=["+", "-", "-", "+", "-", "-"], prop=CC.prop_vortex, prop_name="vortex")
_Cnh = {"b1": b - 1, "t1": t - 1, "t_hi": F - 1 - t, "f0": f, "f_hi": F - 1 - f, "F4": F - 4}
Tuple("B21.n_dlt", "App. B.2.1", "d = b - r < b: Q = (1, d, -v, r, F, f) and b24(mu_3 Q) = F + rf.",
      hyps=merge(_Cnh, {"r1": r - 1, "d1": b - r - 1}), start=(-1, b, t, -r, -F, f),
      steps=[(2, (1, b - r, -(F - t), r, F, f)), (3, {(2, 4): F + r * f})])
Ineq("B21.n_dlt_f", "App. B.2.1", "f > 0 would give b24(mu_3 Q) = F + rf > F.",
     hyps={"r1": r - 1, "f1": f - 1, "ht": F - (F + r * f)}, goal=("contra",))
_pn = S.spfaffian(S.as_poly_tuple(_Cn))
Ineq("B21.n_dlt_p", "App. B.2.1", "f = 0: |p| = bv + td >= F, contradiction.",
     hyps=merge({"b1": b - 1, "t1": t - 1, "v1": F - t - 1, "d1": d - 1}, pbounds(_pn.substitute({"f": 0}))),
     goal=("contra",))
Identity("B21.n_deq_p", "App. B.2.1", "d = b: p = f - bF.", _pn.substitute({"d": b}), f - b * F)
Ineq("B21.n_deq_b2", "App. B.2.1", "d = b >= 2: |p| >= 2F-(F-1) > F.",
     hyps=merge({"b2": b - 2, "f0": f, "f_hi": F - 1 - f}, pbounds(f - b * F)), goal=("contra",))
for nm, sp in [("B21.n_deq_order0", "0"), ("B21.n_deq_order1", "+")]:
    Pattern(nm, "App. B.2.1", "b = d = 1, f >= 0: the unique proper wiggle class contains <1,2,3,4>.",
            hyps={"t1": t - 1, "v1": F - t - 1, "f0": f, "f1": f - 1}, entries=(1, -1, -t, 1, -(F - t), 0 if sp == "0" else f),
            spec=["+", "-", "-", "+", "-", sp], prop=CC.prop_at_most_one_proper_class_containing((1, 2, 3, 4)),
            prop_name="unique class <1234>")
_mn = S.smarkov(S.as_poly_tuple((1, -1, -t, 1, -v, f)), (1, 2, 3, 4))
Identity("B21.n_deq_m", "App. B.2.1", "b = d = 1: m = 2+t^2+v^2+f^2+tv-vf.", _mn, 2 + t ** 2 + v ** 2 + f ** 2 + t * v - v * f)
Ineq("B21.n_deq_b1", "App. B.2.1", "b = d = 1 (F = t+v): m - F > 0.",
     hyps={"t1": t - 1, "v1": v - 1, "f0": f, "mT": (t + v) - 1 - _mn}, goal=("contra",),
     cert=(4 * H("mT") + 4 * (H("t1") + 1) * H("t1") + 4 * H("t1") * (H("v1") + 1) + 3 * Sq(v) + Sq(2 * f - v)).cert())
Tuple("B21.n_dgt", "App. B.2.1", "d = b + r > b: Q = (1, b, -v, -r, F, f-rF) and b34(mu_3 Q) = rF - f.",
      hyps=merge(_Cnh, {"r1": r - 1}), start=(-1, b, t, r, -F, f),
      steps=[(2, (1, b, -(F - t), -r, F, f - r * F)), (3, {(3, 4): r * F - f})])
Ineq("B21.n_dgt_r", "App. B.2.1", "rF - f <= F with f <= F-1 forces r = 1.",
     hyps={"r2": r - 2, "f_hi": F - 1 - f, "F4": F - 4, "ht": F - (r * F - f)}, goal=("contra",))
Identity("B21.n_dgt_p", "App. B.2.1", "d = b+1, f = F-u: -p = bv + td - f = (b-1)F + t + u.",
         -_pn.substitute({"d": b + 1, "f": F - u}), (b - 1) * F + t + u)
Ineq("B21.n_dgt_b2", "App. B.2.1", "b >= 2: |p| >= F, contradiction.",
     hyps=merge({"b2": b - 2, "t1": t - 1, "u1": u - 1}, pbounds(-((b - 1) * F + t + u))), goal=("contra",))
Ineq("B21.n_dgt_b1", "App. B.2.1", "b = 1, d = 2: 2(t+u) < m <= F-1, so C = I_{t,u} with 2(t+u) <= F-2.",
     hyps=pbounds(-(t + u)), goal=("ge0", F - 2 - 2 * (t + u)))

# =============================================================================== B2.2: x = -b < 0, d = -D <= 0
C22 = (1, -b, c, -D, e, f)


def pos(expr, sign):
    return expr if sign == "+" else Poly()


for cs in "+-":
    hc = e if cs == "+" else e + c                       # h = e - [-c]_+
    gc = f + b * c if cs == "+" else f                   # g = f + b[c]_+
    for hs in "+-":
        zc = gc + (b + D) * pos(hc, hs)                  # z = g + (b+D)[h]_+
        for zs in "+-":
            hy = {"b1": b - 1, "D0": D, "csign": c if cs == "+" else -c, "hsign": hc if hs == "+" else -hc,
                  "zsign": zc if zs == "+" else -zc}
            Tuple("B22.paths_%s%s%s" % (cs, hs, zs), "App. B.2.2",
                  "P, Q and two entries of mu_3 Q, for sign case c%s0, h%s0, z%s0." % (cs, hs, zs),
                  hyps=hy, start=C22,
                  steps=[(1, (-1, b, -c, -D - b, hc, gc)),
                         (2, (1, -D, -c - pos(-hc, "+" if hs == "-" else "-"), D + b, -hc, zc)),
                         (3, {(1, 2): 1 - D * (D + b), (2, 4): -hc + (D + b) * pos(zc, zs)})])
_C22 = merge({"b1": b - 1, "b_hi": F - 1 - b, "D0": D, "D_hi": F - 1 - D, "F4": F - 4},
             low("c", c), low("e", e), low("f", f))
# case h = -F: c = -t < 0, e = -(F - t) < 0; then g = z = f and b24(mu_3 Q) = F + (b+D)[f]_+
Ineq("B22.hF_f", "App. B.2.2", "h = -F: f > 0 would make b24(mu_3 Q) = F + (b+D)f > F.",
     hyps={"b1": b - 1, "D0": D, "f1": f - 1, "ht": F - (F + (b + D) * f)}, goal=("contra",))
Pattern("B22.hF_acyclic", "App. B.2.2", "h = -F and f <= 0: C is acyclic (topological order 4<3<1<2).",
        hyps={"b1": b - 1, "t1": t - 1, "v1": F - t - 1, "D0": D, "f0": -f}, entries=(1, -b, -t, -D, -(F - t), f),
        spec=["+", "-", "-", "-0", "-", "-0"], prop=CC.prop_acyclic, prop_name="acyclic")
# case g = F (c > 0, f = F - bc)
Ineq("B22.gF_e", "App. B.2.2", "g = F: e > 0 would make b34(Q) = z = F + (b+D)e > F.",
     hyps={"b1": b - 1, "D0": D, "e1": e - 1, "ht": F - (F + (b + D) * e)}, goal=("contra",))
Ineq("B22.gF_bD", "App. B.2.2", "g = F, e <= 0: b24(mu_3 Q) = -e + (b+D)F <= F forces b + D = 1.",
     hyps={"b1": b - 1, "D0": D, "e0": -e, "bD2": b + D - 2, "F4": F - 4, "ht": F - (-e + (b + D) * F)}, goal=("contra",))
Ineq("B22.gF_e0", "App. B.2.2", "g = F, b = 1, D = 0: -e + F <= F forces e >= 0, so e = 0.",
     hyps={"en": -e - 1, "ht": F - (-e + F)}, goal=("contra",))
Pattern("B22.gF_acyclic", "App. B.2.2", "Then C = (1,-1,c,0,0,F-c) with 0<c<F is acyclic (3<1<2<4).",
        hyps={"c1": c - 1, "f1": F - c - 1}, entries=(1, -1, c, 0, 0, F - c), spec=["+", "-", "+", "0", "0", "+"],
        prop=CC.prop_acyclic, prop_name="acyclic")
# case b + D = F
Ineq("B22.bD_D", "App. B.2.2", "b + D = F: b12(mu_3 Q) = 1 - DF >= -F forces D = 1 (so b = F-1).",
     hyps={"D2": D - 2, "F4": F - 4, "ht": (1 - D * F) + F}, goal=("contra",))
Ineq("B22.bD_z", "App. B.2.2", "b24(mu_3 Q) = -h + F[z]_+ <= F with h <= F-1 forces z <= 1.",
     hyps={"z2": z - 2, "h_hi": F - 1 - h, "F4": F - 4, "ht": F - (-h + F * z)}, goal=("contra",))
T_ = F - 1
_pC22 = S.spfaffian(S.as_poly_tuple((1, -T_, c, -1, e, f)))
Identity("B22.bD_pf", "App. B.2.2", "With b = T = F-1 and D = 1: p = f + Te - c.", _pC22, f + T_ * e - c)
Ineq("B22.bD_cpos_e", "App. B.2.2", "c > 0: z = f + Tc + F[e]_+ <= 1 forces e <= 0.",
     hyps={"c1": c - 1, "e1": e - 1, "f_lo": f + F - 1, "F4": F - 4, "z1": 1 - (f + T_ * c + F * e)}, goal=("contra",))
Ineq("B22.bD_cpos_p", "App. B.2.2", "c > 0, e <= 0, f + Tc <= 1: p = f + Te - c <= -T, contradiction.",
     hyps=merge({"c1": c - 1, "e0": -e, "z1": 1 - (f + T_ * c), "F4": F - 4}, pbounds(f + T_ * e - c)), goal=("contra",))
Ineq("B22.bD_cneg_f2", "App. B.2.2", "c = -t <= 0, f > 0: z = f + F[e-t]_+ <= 1 forces f = 1 ...",
     hyps={"f2": f - 2, "z1": 1 - f}, goal=("contra",))
Ineq("B22.bD_cneg_et", "App. B.2.2", "... and e <= t.",
     hyps={"f1": f - 1, "et": e - t - 1, "F4": F - 4, "z1": 1 - (f + F * (e - t))}, goal=("contra",))
Tuple("B22.bD_cneg_b24", "App. B.2.2", "c = -t, f = 1, e <= t: b24(mu_3 Q) = F + t - e.",
      hyps={"t0": t, "te": t - e, "F4": F - 4}, start=(1, -T_, -t, -1, e, 1),
      steps=[(1, None), (2, None), (3, {(2, 4): F + t - e})])
Ineq("B22.bD_cneg_ete", "App. B.2.2", "F + t - e <= F forces e >= t, so e = t.",
     hyps={"te": t - e - 1, "ht": F - (F + t - e)}, goal=("contra",))
Pattern("B22.bD_vortex", "App. B.2.2", "e = t > 0, f = 1: C = (1,-T,-t,-1,t,1) is a vortex (3 is a source).",
        hyps={"t1": t - 1, "F4": F - 4}, entries=(1, -T_, -t, -1, t, 1), spec=["+", "-", "-", "-", "+", "+"],
        prop=CC.prop_vortex, prop_name="vortex")
Pattern("B22.bD_t0", "App. B.2.2", "e = t = 0, f = 1: C = (1,-T,0,-1,0,1) is acyclic.",
        hyps={"F4": F - 4}, entries=(1, -T_, 0, -1, 0, 1), spec=["+", "-", "0", "-", "0", "+"],
        prop=CC.prop_acyclic, prop_name="acyclic")
_pneg = S.spfaffian(S.as_poly_tuple((1, -T_, -t, -1, e, f)))
Identity("B22.bD_fneg_pf", "App. B.2.2", "c = -t: p = f + Te + t.", _pneg, f + T_ * e + t)
Ineq("B22.bD_fneg_e2", "App. B.2.2", "f <= 0, e >= 2: p >= T, contradiction.",
     hyps=merge({"t0": t, "e2": e - 2, "f_lo": f + F - 1, "f0": -f, "F4": F - 4}, pbounds(f + T_ * e + t)), goal=("contra",))
Pattern("B22.bD_fneg_e0", "App. B.2.2", "f <= 0, e <= 0: C is acyclic.",
        hyps={"t0": t, "e0": -e, "f0": -f, "F4": F - 4}, entries=(1, -T_, -t, -1, e, f), spec=["+", "-", "-0", "-", "-0", "-0"],
        prop=CC.prop_acyclic, prop_name="acyclic")
Pattern("B22.bD_fneg_e1_00", "App. B.2.2", "e = 1, t = f = 0: C is acyclic.",
        hyps={"F4": F - 4}, entries=(1, -T_, 0, -1, 1, 0), spec=["+", "-", "0", "-", "+", "0"],
        prop=CC.prop_acyclic, prop_name="acyclic")
for nm, tsp, fsp in [("tf", "-", "-"), ("t0", "-", "0"), ("f0", "0", "-")]:
    ent = (1, -T_, -t if tsp == "-" else 0, -1, 1, f if fsp == "-" else 0)
    Pattern("B22.bD_order_" + nm, "App. B.2.2", "e = 1, (t,f) != (0,0): the unique proper class contains <1,2,4,3>.",
            hyps={"t1": t - 1, "f1": -f - 1, "F4": F - 4}, entries=ent, spec=["+", "-", tsp, "-", "+", fsp],
            prop=CC.prop_at_most_one_proper_class_containing((1, 2, 4, 3)), prop_name="unique class <1243>")
_m22 = S.smarkov(S.as_poly_tuple((1, -T_, -t, -1, 1, f)), (1, 2, 4, 3))
Identity("B22.bD_m", "App. B.2.2", "m = T^2+T+3+t(t-1)+f^2+f(T+1-Tt).", _m22,
         T_ ** 2 + T_ + 3 + t * (t - 1) + f ** 2 + f * (T_ + 1 - T_ * t))
_mb = 4 * H("mT") + 3 * H("F4") * H("F4") + 16 * H("F4") + Sq(2 * f + F) + 4 * H("f0") * (H("F4") + 3) * H("t0")
Ineq("B22.bD_mbig", "App. B.2.2", "m >= T^2+T+3-(T+1)^2/4 > T, contradicting m <= T.",
     hyps={"t0": t, "f0": -f, "F4": F - 4, "mT": F - 1 - _m22}, goal=("contra",),
     cert=Split(t, (_mb + 4 * H("SPLIT") * (H("SPLIT") + 1)).cert(),
                (_mb + 4 * (H("SPLIT") * H("SPLIT") + H("SPLIT"))).cert()))

# =============================================================================== B2.3: x >= 0 (then c = -t < 0)
C23 = (1, x, -t, d, e, f)
w23 = f - x * t
for ds in "+-":
    for es in "+-":
        # z = w + [-d]_+[e-t]_+ - [d]_+[t-e]_+
        z23 = w23 + pos(-d, "+" if ds == "-" else "-") * pos(e - t, es) - pos(d, ds) * pos(t - e, "+" if es == "-" else "-")
        mn = t if es == "+" else e                         # min(t, e)
        xd = x + pos(-d, "+" if ds == "-" else "-")        # x + [-d]_+
        for zs in "+-":
            hy = {"x0": x, "t1": t - 1, "dsign": d if ds == "+" else -d, "esign": (e - t) if es == "+" else (t - e),
                  "zsign": z23 if zs == "+" else -z23}
            Tuple("B23.paths_%s%s%s" % (ds, es, zs), "App. B.2.3",
                  "P, Q and three entries of mu_3 Q, for sign case d%s0, e-t%s0, z%s0." % (ds, es, zs),
                  hyps=hy, start=C23,
                  steps=[(1, (-1, -x, t, d, e - t, w23)),
                         (2, (1, -xd, mn, -d, t - e, z23)),
                         (3, {(1, 2): 1 - xd * pos(-d, "+" if ds == "-" else "-"),
                              (1, 4): mn - xd * pos(-z23, "+" if zs == "-" else "-"),
                              (2, 4): t - e + pos(-d, "+" if ds == "-" else "-") * pos(z23, zs)
                                      - pos(d, ds) * pos(-z23, "+" if zs == "-" else "-")})])
_p23 = S.spfaffian(S.as_poly_tuple(C23))
Identity("B23.pf", "App. B.2.3", "p = f - xe - td.", _p23, f - x * e - t * d)
# ---- case e - t = -F (e = -u, u = F - t)
Ineq("B23.eF_dneg_w", "App. B.2.3", "d = -D < 0: b24(mu_3 Q) = F + D[w]_+ <= F forces w <= 0.",
     hyps={"D1": D - 1, "w1": w - 1, "ht": F - (F + D * w)}, goal=("contra",))
Ineq("B23.eF_dneg_x", "App. B.2.3", "d = -D < 0, w = -v <= 0, (x+D)v <= t: x >= 1 gives p = xF + tD - v >= F.",
     hyps=merge({"x1": x - 1, "D1": D - 1, "v0": v, "t1": t - 1, "xDv": t - (x + D) * v, "F4": F - 4},
                pbounds(x * F + t * D - v)), goal=("contra",))
Identity("B23.eF_dneg_pf", "App. B.2.3", "with d=-D, e=-u, f=w+xt, w=-v, u=F-t: p = xF + tD - v.",
         _p23.substitute({"d": -D, "e": -(F - t), "f": -v + x * t}), x * F + t * D - v)
Pattern("B23.eF_acyc1", "App. B.2.3", "x = 0, d < 0, f <= 0: C is acyclic.",
        hyps={"t1": t - 1, "D1": D - 1, "u1": F - t - 1, "f0": -f}, entries=(1, 0, -t, -D, -(F - t), f),
        spec=["+", "0", "-", "-", "-", "-0"], prop=CC.prop_acyclic, prop_name="acyclic")
Ineq("B23.eF_dpos_d", "App. B.2.3", "d >= 2: b34(Q) = w - dF >= -F would force w >= F, but w <= f <= F-1.",
     hyps={"d2": d - 2, "x0": x, "t1": t - 1, "f_hi": F - 1 - f, "F4": F - 4, "ht": (f - x * t - d * F) + F}, goal=("contra",))
Identity("B23.eF_d0_pf", "App. B.2.3", "d = 0, e = -u = t - F: p = w + xF.",
         _p23.substitute({"d": 0, "e": t - F, "f": w + x * t}), w + x * F)
Ineq("B23.eF_d0_x2a", "App. B.2.3", "d = 0, x >= 2, w >= 0: p >= 2F, contradiction.",
     hyps=merge({"x2": x - 2, "w0": w, "F4": F - 4}, pbounds(w + x * F)), goal=("contra",))
Ineq("B23.eF_d0_x2b", "App. B.2.3", "d = 0, x >= 2, w < 0 with x(-w) <= t: p = xF + w >= 2F - t > F.",
     hyps=merge({"x2": x - 2, "wn": -w - 1, "xw": t + x * w, "t_hi": F - 1 - t, "F4": F - 4}, pbounds(w + x * F)),
     goal=("contra",))
Ineq("B23.eF_d0_x1", "App. B.2.3", "d = 0, x = 1, -w <= t: f = t + w >= 0.",
     hyps={"xw": t + w}, goal=("ge0", t + w))
Ineq("B23.eF_d1_x", "App. B.2.3", "d = 1, x >= 1: F - w >= 1 + xt and x(F - w) <= t are incompatible.",
     hyps={"x1": x - 1, "t1": t - 1, "w0": w, "fT": (F - 1) - (x * t + w), "xFw": t - x * (F - w)}, goal=("contra",),
     cert=(H("xFw") + (H("x1") + 1) * H("fT") + H("x1") + (H("t1") + 1) * H("x1") * (H("x1") + 2)).cert())
Pattern("B23.eF_acyc2", "App. B.2.3", "x = d = 0: C = (1,0,-t,0,-u,f) is acyclic for any f.",
        hyps={"t1": t - 1, "u1": F - t - 1}, entries=(1, 0, -t, 0, -(F - t), f), spec=["+", "0", "-", "0", "-", "*"],
        prop=CC.prop_acyclic, prop_name="acyclic")
for nm, ent, sp in [("B23.eF_acyc3", (1, 0, -t, 1, -(F - t), 0), ["+", "0", "-", "+", "-", "0"]),
                    ("B23.eF_acyc4", (1, 1, -t, 0, -(F - t), 0), ["+", "+", "-", "0", "-", "0"])]:
    Pattern(nm, "App. B.2.3", "(x,d) = (0,1) or (1,0) with f = 0: C is acyclic.",
            hyps={"t1": t - 1, "u1": F - t - 1}, entries=ent, spec=sp, prop=CC.prop_acyclic, prop_name="acyclic")
for nm, ent, sp in [("B23.eF_ord01", (1, 0, -t, 1, -(F - t), f), ["+", "0", "-", "+", "-", "+"]),
                    ("B23.eF_ord10", (1, 1, -t, 0, -(F - t), f), ["+", "+", "-", "0", "-", "+"])]:
    Pattern(nm, "App. B.2.3", "f > 0: the unique proper wiggle class contains <1,2,3,4>.",
            hyps={"t1": t - 1, "u1": F - t - 1, "f1": f - 1}, entries=ent, spec=sp,
            prop=CC.prop_at_most_one_proper_class_containing((1, 2, 3, 4)), prop_name="unique class <1234>")
for nm, ent, lam in [("B23.eF_m01", (1, 0, -t, 1, -u, f), t + u), ("B23.eF_m10", (1, 1, -t, 0, -u, f), t)]:
    mval = S.smarkov(S.as_poly_tuple(ent), (1, 2, 3, 4))
    Identity(nm, "App. B.2.3", "m = 2+t^2+u^2+tu+f^2-lambda f with lambda = F or t.", mval,
             2 + t ** 2 + u ** 2 + t * u + f ** 2 - lam * f)
    Ineq(nm + "_big", "App. B.2.3", "m >= 2 + F^2/2 > F (F = t+u), contradicting m <= F-1.",
         hyps={"t1": t - 1, "u1": u - 1, "f1": f - 1, "mT": (t + u) - 1 - mval}, goal=("contra",),
         hints=(2 * f - t - u, t - u, 2 * f - t, f), depth=2)
# ---- case w = -F (f = xt - F), e - t > -F
mnv = V("mn")   # stands for min(t, e) <= t <= F-1
Ineq("B23.wF_x", "App. B.2.3", "w = -F: f = xt - F >= -(F-1) forces x >= 1.",
     hyps={"x0": -x, "xpos": x, "t1": t - 1, "f_lo": (x * t - F) + F - 1}, goal=("contra",))
Ineq("B23.wF_dneg_D", "App. B.2.3", "x + D = F: b12(mu_3 Q) = 1 - FD >= -F forces D = 1.",
     hyps={"D2": D - 2, "F4": F - 4, "ht": 1 - F * D + F}, goal=("contra",))
Ineq("B23.wF_dneg_z", "App. B.2.3", "x + D = F, D = 1: b14(mu_3 Q) = min(t,e) - F[-z]_+ >= -F forces z >= -1.",
     hyps={"zz": -z - 2, "mn_hi": F - 1 - mnv, "F4": F - 4, "ht": mnv - F * (-z) + F}, goal=("contra",))
Ineq("B23.wF_dneg_et", "App. B.2.3", "z = -F + [e-t]_+ >= -1 needs e - t >= F-1, but e - t <= F-2.",
     hyps={"et": (e - t) - (F - 1), "e_hi": F - 1 - e, "t1": t - 1}, goal=("contra",))
Ineq("B23.wF_dneg_zmF", "App. B.2.3", "z = -F: b14(mu_3 Q) = min(t,e) - (x+D)F <= F-1-2F < -F.",
     hyps={"x1": x - 1, "D1": D - 1, "mn_hi": F - 1 - mnv, "F4": F - 4, "ht": mnv - (x + D) * F + F}, goal=("contra",))
Ineq("B23.wF_dneg_zF_D", "App. B.2.3", "z = F: b24(mu_3 Q) = t - e + DF <= F with e - t <= F-2 forces D = 1.",
     hyps={"D2": D - 2, "et_hi": F - 2 - (e - t), "F4": F - 4, "ht": F - (t - e + D * F)}, goal=("contra",))
Ineq("B23.wF_dneg_zF", "App. B.2.3", "z = F, D = 1: -F + (e - t) = F is impossible since e - t <= F-2.",
     hyps={"et_hi": F - 2 - (e - t), "F4": F - 4}, eqs={"z": -F + (e - t) - F}, goal=("contra",))
Ineq("B23.wF_dpos_z", "App. B.2.3", "d >= 0: z = -F - d[t-e]_+ >= -F forces d[t-e]_+ = 0.",
     hyps={"d1": d - 1, "te": t - e - 1, "ht": (-F - d * (t - e)) + F}, goal=("contra",))
Ineq("B23.wF_dpos_x", "App. B.2.3", "z = -F: b14(mu_3 Q) = min(t,e) - xF >= -F forces x <= 1.",
     hyps={"x2": x - 2, "mn_hi": F - 1 - mnv, "F4": F - 4, "ht": mnv - x * F + F}, goal=("contra",))
Ineq("B23.wF_dpos_e", "App. B.2.3", "x = 1: min(t,e) - F >= -F forces e >= 0.",
     hyps={"en": -e - 1, "ht": e - F + F}, goal=("contra",))
Ineq("B23.wF_dpos_d", "App. B.2.3", "d > 0, e >= t: b24(mu_3 Q) = t - e - dF >= -F forces d = 1 ...",
     hyps={"d2": d - 2, "et": e - t, "F4": F - 4, "ht": (t - e - d * F) + F}, goal=("contra",))
Ineq("B23.wF_dpos_e2", "App. B.2.3", "... and e = t.",
     hyps={"et": e - t - 1, "ht": (t - e - F) + F}, goal=("contra",))
Identity("B23.wF_d1_pf", "App. B.2.3", "x = d = 1, e = t, f = t - F: p = -F - t.",
         _p23.substitute({"x": 1, "d": 1, "e": t, "f": t - F}), -F - t)
Ineq("B23.wF_d1_p", "App. B.2.3", "|p| = F + t > F, contradiction.", hyps=merge({"t1": t - 1}, pbounds(-F - t)),
     goal=("contra",))
Pattern("B23.wF_d0_acyc", "App. B.2.3", "d = 0, e = 0: C = (1,1,-t,0,0,-u) is acyclic.",
        hyps={"t1": t - 1, "u1": F - t - 1}, entries=(1, 1, -t, 0, 0, -(F - t)), spec=["+", "+", "-", "0", "0", "-"],
        prop=CC.prop_acyclic, prop_name="acyclic")
Pattern("B23.wF_d0_order", "App. B.2.3", "d = 0, e > 0: the unique proper wiggle class contains <1,2,3,4>.",
        hyps={"t1": t - 1, "u1": F - t - 1, "e1": e - 1}, entries=(1, 1, -t, 0, e, -(F - t)),
        spec=["+", "+", "-", "0", "+", "-"], prop=CC.prop_at_most_one_proper_class_containing((1, 2, 3, 4)),
        prop_name="unique class <1234>")
_mwd0 = S.smarkov(S.as_poly_tuple((1, 1, -t, 0, e, -u)), (1, 2, 3, 4))
Identity("B23.wF_d0_m", "App. B.2.3", "m = 2+t^2+u^2+e^2+tu-te.", _mwd0, 2 + t ** 2 + u ** 2 + e ** 2 + t * u - t * e)
Ineq("B23.wF_d0_big", "App. B.2.3", "m >= 2 + 3t^2/4 + u^2 + tu > t + u = F.",
     hyps={"t1": t - 1, "u1": u - 1, "e1": e - 1, "mT": (t + u) - 1 - _mwd0}, goal=("contra",),
     cert=(4 * H("mT") + Sq(2 * e - t) + 3 * H("t1") * H("t1") + 2 * H("t1") + 4 * H("u1") * H("u1") + 4 * H("u1")
           + 4 * (H("t1") + 1) * (H("u1") + 1)).cert())

# =============================================================================== B3: the two remaining cases
Ac = (1, -2, c, 1, 0, F - 2 * c)
_Ac = {"c1": c - 1, "c_hi": F - 1 - c, "F4": F - 4}
Tuple("B3.A_segment", "App. B.3", "The excursion [1,2,3,1,3] from A_c (table rows 1-5).", hyps=_Ac, start=Ac,
      steps=[(1, (-1, 2, -c, -1, 0, F)), (2, (1, 1, -c, 1, 0, F)), (3, (1, -1, F - c, -1, F, -F)),
             (1, (-1, 1, c - F, -2, F, -c)), (3, (1, -1, c - F, 2, F - 2 * c, c))])
Tuple("B3.A_replacement", "App. B.3", "The replacement [2,1,3] from A_c (table rows 6-8).", hyps=_Ac, start=Ac,
      steps=[(2, (-1, -1, c, -1, 0, F - 2 * c)), (1, (1, 1, -c, -1, c, F - c)), (3, (2, -1, F - 2 * c, 1, c, c - F))])
TupleEq("B3.A_relabel", "App. B.3", "mu_[2,1,3] A_c = (mu_[1,2,3,1,3] A_c)^{pi_123}.",
        S.srelabel(S.as_poly_tuple((1, -1, c - F, 2, F - 2 * c, c)), Q.PI123), (2, -1, F - 2 * c, 1, c, c - F))
Tuple("B3.A_forced1", "App. B.3", "After [1,2,3], mutation at 2 or 4 creates 2F - c or F^2 - 1.", hyps=_Ac,
      start=(1, -1, F - c, -1, F, -F), steps=[(2, {(1, 4): 2 * F - c})])
Tuple("B3.A_forced1b", "App. B.3", "(mutation at 4)", hyps=_Ac, start=(1, -1, F - c, -1, F, -F),
      steps=[(4, {(2, 3): F ** 2 - 1})])
Tuple("B3.A_forced2", "App. B.3", "After [1,2,3,1], mutation at 2 or 4 creates 2F - c or -1 - F(F-c).", hyps=_Ac,
      start=(-1, 1, c - F, -2, F, -c), steps=[(2, {(3, 4): 2 * F - c})])
Tuple("B3.A_forced2b", "App. B.3", "(mutation at 4)", hyps=_Ac, start=(-1, 1, c - F, -2, F, -c),
      steps=[(4, {(1, 2): -1 - F * (F - c)})])
for nm, ex in [("2Fc", 2 * F - c - F - 1), ("F2", F ** 2 - 1 - F - 1), ("FFc", 1 + F * (F - c) - F - 1)]:
    Ineq("B3.A_forced_" + nm, "App. B.3", "These entries exceed F in absolute value.", hyps=_Ac, goal=("ge0", ex))
for k_, ex in enumerate([F - 2 * c, c - F]):
    Ineq("B3.A_low_lo%d" % k_, "App. B.3", "Every entry along [2,1,3] (and A_c, and the endpoint) is low.",
         hyps=_Ac, goal=("ge0", ex + F - 1))
    Ineq("B3.A_low_hi%d" % k_, "App. B.3", "Every entry along [2,1,3] (and A_c, and the endpoint) is low.",
         hyps=_Ac, goal=("ge0", F - 1 - ex))
It = (1, -1, -t, 2, t - F, F - u)
_It = {"t1": t - 1, "t_hi": F - 1 - t, "u1": u - 1, "u_hi": F - 1 - u, "F4": F - 4}
Tuple("B3.I_segment", "App. B.3", "The excursion [1,2,3] from I_{t,u}.", hyps=_It, start=It,
      steps=[(1, (-1, 1, t, 1, -F, F - u)), (2, (1, 1, t - F, -1, F, -u)), (3, (2, -1, t - F, 1, F - u, u))])
TupleEq("B3.I_endpoint", "App. B.3", "J = (mu_[1,2,3] I_{t,u})^{pi_123} = (1,-2,F-u,1,u,t-F).",
        S.srelabel(S.as_poly_tuple((2, -1, t - F, 1, F - u, u)), Q.PI123), (1, -2, F - u, 1, u, t - F))
_EI = (1, -2, F - u, 1, u, t - F)
Tuple("B3.I_tgu", "App. B.3", "t > u: the replacement [2,1,3,2,3] ends at J.", hyps=merge(_It, {"tu": t - u - 1}),
      start=It, steps=[(2, (-1, 1, -t, -2, F - t, 2 * t - F - u)), (1, (1, -1, t, -1, F - t, t - F - u)),
                       (3, (1, 1, 2 * t - F - u, 1, -u, F + u - t)), (2, (-1, 2, 2 * t - F - u, -1, u, F - t)), (3, _EI)])
Tuple("B3.I_ugt", "App. B.3", "u > t: the replacement [3,1,3,2,1] ends at J.", hyps=merge(_It, {"ut": u - t - 1}),
      start=It, steps=[(3, (-1, 1, -t, -2, F + t - 2 * u, u - F)), (1, (1, -1, t, -1, F + t - 2 * u, u - F - t)),
                       (3, (1, 1, u - F, 1, -u, F + t - u)), (2, (-1, 2, u - F, -1, u, F + t - 2 * u)), (1, _EI)])
for tag, hy, ents in [("tgu", {"tu": t - u - 1}, [2 * t - F - u, t - F - u, F + u - t, F - t, t - F, F - u]),
                      ("ugt", {"ut": u - t - 1}, [F + t - 2 * u, u - F - t, u - F, F + t - u, F - u, t - F])]:
    for k_, ex in enumerate(ents):
        Ineq("B3.I_low_%s_lo%d" % (tag, k_), "App. B.3", "Every entry along the replacement is low.",
             hyps=merge(_It, hy), goal=("ge0", ex + F - 1))
        Ineq("B3.I_low_%s_hi%d" % (tag, k_), "App. B.3", "Every entry along the replacement is low.",
             hyps=merge(_It, hy), goal=("ge0", F - 1 - ex))
Identity("B3.I_tt_pf", "App. B.3", "p(I_{t,t}) = -2t.", S.spfaffian(S.as_poly_tuple(It)).substitute({"u": t}), -2 * t)
Ineq("B3.I_tt_k", "App. B.3", "t = u: 4t < m <= F-1, so k = F - t >= 2.",
     hyps=merge({"t1": t - 1}, pbounds(-2 * t)), goal=("ge0", F - t - 2))
Pattern("B3.I_tt_triangle", "App. B.3", "I_{t,t} contains the oriented triangle 2 -> 3 -> 4 -> 2 with weights (2,k,k).",
        hyps={"t1": t - 1, "k1": F - t - 1}, entries=(1, -1, -t, 2, t - F, F - t), spec=["+", "-", "-", "+", "-", "+"],
        prop=CC.prop_oriented_triangle(2, 3, 4), prop_name="oriented triangle 234")
Identity("B3.I_tt_markov", "App. B.3", "Its Markov constant is 2^2 + k^2 + k^2 - 2k^2 = 4.",
         Poly.coerce(4) + (F - t) ** 2 + (F - t) ** 2 - 2 * (F - t) ** 2, 4)

# =============================================================================== Sections 2, 3 and 5
k_ = V("k")
Ak = (k_, 0, 0, 1, 0, k_)
Identity("S2.Lk_markov", "Remark 2.5", "L_k = (k,0,0,1,0,k): M = 2k^2+1.", S.smarkov(S.as_poly_tuple(Ak), (1, 2, 3, 4)),
         2 * k_ ** 2 + 1)
Identity("S2.Lk_pf", "Remark 2.5", "L_k: p = k^2.", S.spfaffian(S.as_poly_tuple(Ak)), k_ ** 2)
Qt = (-2, t + 2, t, -t, 2 - t, 0)
Tuple("S3.recurrence", "Lemma 3.1", "For t >= 2: (mu_2 Q(t))^{pi_12} = Q(t-2).", hyps={"t2": t - 2},
      start=Qt, steps=[(2, (2, 2 - t, 4 - t, t, t - 2, 0))], relabel=(Q.PI12, (-2, t, t - 2, 2 - t, 4 - t, 0)))
Identity("S3.Qt_pf", "Remark 3.3", "p(Q(t)) = -4 for every t, so det B = 16.", S.spfaffian(S.as_poly_tuple(Qt)), -4)
Pattern("S3.Qt_class", "Remark 3.3",
        "For t >= 3, Q(t) has exactly one proper wiggle class, and it contains <1,3,4,2>.",
        hyps={"t3": t - 3}, entries=Qt, spec=["-", "+", "+", "-", "-", "0"],
        prop=CC.prop_exactly_one_proper_class_containing((1, 3, 4, 2)), prop_name="exactly one class <1342>")
Identity("S3.Qt_markov", "Remark 3.3", "M_<1,3,4,2>(Q(t)) = 12 for every t.",
         S.smarkov(S.as_poly_tuple(Qt), (1, 3, 4, 2)), 12)
Ax = (x, x, 0, 1, x, -1)
Identity("S5.Gx_markov", "Remark 5.6",
         "G_x = (x,x,0,1,x,-1) is acyclic (order 1<2<4<3) with M = x^3+4x^2+x+2.",
         S.smarkov(S.as_poly_tuple(Ax), (1, 2, 4, 3)), x ** 3 + 4 * x ** 2 + x + 2)
Tuple("S5.Gx_mu4", "Remark 5.6", "mu_4 G_x = (x, x, 0, x+1, -x, 1), of height x+1.",
      hyps={"x1": x - 1}, start=Ax, steps=[(4, (x, x, 0, x + 1, -x, 1))])
Pattern("S3.Qneg", "Theorem 3.2", "For t <= -3, Q(t) = (-2,t+2,t,-t,2-t,0) is acyclic (vertex 2 is a source).",
        hyps={"tn": -t - 3}, entries=Qt, spec=["-", "-", "-", "+", "+", "0"], prop=CC.prop_acyclic, prop_name="acyclic")
Pattern("S5.Gx_acyclic", "Remark 5.6", "G_x = (x,x,0,1,x,-1) is acyclic for x >= 1.",
        hyps={"x1": x - 1}, entries=Ax, spec=["+", "+", "0", "+", "+", "-"], prop=CC.prop_acyclic, prop_name="acyclic")
