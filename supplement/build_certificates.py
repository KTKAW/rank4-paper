"""Find the certificates that are not written by hand and store them in certificates.json.

Development tool (needs scipy). Verification of the paper does not need it: check_proofs.py
re-checks every stored certificate exactly with the standard library.

Usage:  python3 build_certificates.py            # build missing certificates
        python3 build_certificates.py --rebuild  # rebuild all
"""
import json
import sys
from pathlib import Path
from polynomial import Poly
from certificates import check_certificate, CertificateError, encode_cert, decode_cert
from find_certificates import find_certificate
import claims_core as CC
import symbolic as S
import quiver4 as Q
import proof_claims  # noqa: F401  (registers the claims)

HERE = Path(__file__).resolve().parent
STORE = HERE / "certificates.json"


def trivial_cert(hyps, x):
    """x >= 0 when x is a nonnegative constant, or x = h + c with h a hypothesis and c >= 0."""
    if x.is_constant() and x.constant() >= 0:
        return {"kind": "sum", "terms": [], "eqs": [], "const": x.constant()}
    for name in sorted(hyps):
        d = x - hyps[name]
        if d.is_constant() and d.constant() >= 0:
            return {"kind": "sum", "terms": [{"c": 1, "hyps": [name], "sq": None}], "eqs": [], "const": d.constant()}
    return None


def prove(hyps, eqs, goal, depth=2, hints=(), extra=()):
    if goal[0] == "ge0":
        c = trivial_cert(hyps, goal[1])
        if c is not None:
            return c
    for d in sorted(set([1, depth])):
        try:
            c = find_certificate(hyps, eqs, goal, depth=d, hints=hints, extra_terms=extra)
        except RuntimeError:
            c = None
        if c is not None:
            check_certificate(hyps, eqs, goal, c)
            return c
    return None


def build_tuple(claim):
    out = {}
    t = claim.start
    for s, (k, _) in enumerate(claim.steps):
        sg = {}
        for i, x in S.incident_entries(t, k):
            if x is None:
                sg[i] = '?'
                out["%d,%d" % (s, i)] = {"sign": '?', "cert": {"kind": "sum", "terms": [], "eqs": [], "const": 0}}
                continue
            cp = prove(claim.hyps, claim.eqs, ("ge0", x))
            if cp is not None:
                sg[i] = '+'
                out["%d,%d" % (s, i)] = {"sign": '+', "cert": cp}
                continue
            cn = prove(claim.hyps, claim.eqs, ("ge0", -x))
            if cn is not None:
                sg[i] = '-'
                out["%d,%d" % (s, i)] = {"sign": '-', "cert": cn}
                continue
            # unknown sign: entries depending on it become unknown; the check fails if they are needed
            sg[i] = '?'
            out["%d,%d" % (s, i)] = {"sign": '?', "cert": {"kind": "sum", "terms": [], "eqs": [], "const": 0}}
        t = S.smutate(t, k, sg)
    return out


def main(rebuild=False):
    store = {}
    if STORE.exists() and not rebuild:
        raw = json.loads(STORE.read_text())
        store = raw
    new = dict(store)
    failures = []
    for claim in CC.REGISTRY:
        if claim.id in new and not rebuild:
            continue
        try:
            if claim.kind == "ineq":
                if claim.cert is not None:
                    continue
                c = prove(claim.hyps, claim.eqs, claim.goal, claim.depth, claim.hints, claim.extra_terms)
                if c is None:
                    raise CertificateError("%s: no certificate found" % claim.id)
                new[claim.id] = encode_cert(c)
            elif claim.kind == "tuple":
                data = build_tuple(claim)
                new[claim.id] = {k: {"sign": v["sign"], "cert": encode_cert(v["cert"])} for k, v in data.items()}
            elif claim.kind == "pattern":
                data = {}
                for n, goal in claim.sign_goals():
                    c = prove(claim.hyps, claim.eqs, goal)
                    if c is None:
                        raise CertificateError("%s: cannot certify sign set of entry %d" % (claim.id, n))
                    data[str(n)] = encode_cert(c)
                new[claim.id] = data
        except CertificateError as exc:
            failures.append(str(exc))
            print("FAILED:", exc)
    STORE.write_text(json.dumps(new, indent=1, sort_keys=True) + "\n")
    print("stored", len(new), "entries;", len(failures), "failures")
    return failures


if __name__ == "__main__":
    sys.exit(1 if main("--rebuild" in sys.argv) else 0)
