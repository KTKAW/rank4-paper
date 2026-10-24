"""Verify every calculation that the appendices delegate to the supplement.

Standard library only. Loads the claims from proof_claims.py and the stored certificates
from certificates.json, and checks each claim exactly:
  * identities by exact polynomial expansion;
  * inequalities and contradictions by exact positivity certificates;
  * mutation tuples by symbolic mutation, after checking a certificate for the weak sign of
    every entry that the mutation formula needs;
  * sign-pattern statements (proper wiggle classes, acyclicity, vortices, oriented triangles)
    by enumerating every allowed sign pattern, after certifying each entry's allowed signs.
These checks are valid for all integer values of the parameters, not just a finite range.
Run:  python3 check_proofs.py
"""
import json
import sys
from pathlib import Path
from collections import Counter
from certificates import decode_cert, CertificateError
import claims_core as CC
import proof_claims  # noqa: F401  (registers the claims)

HERE = Path(__file__).resolve().parent


def load_store():
    raw = json.loads((HERE / "certificates.json").read_text())
    store = {}
    for claim in CC.REGISTRY:
        if claim.id not in raw:
            continue
        d = raw[claim.id]
        if claim.kind == "ineq":
            store[claim.id] = decode_cert(d)
        elif claim.kind == "tuple":
            store[claim.id] = {k: {"sign": v["sign"], "cert": decode_cert(v["cert"])} for k, v in d.items()}
        elif claim.kind == "pattern":
            store[claim.id] = {k: decode_cert(v) for k, v in d.items()}
    return store


def main(verbose=False):
    store = load_store()
    counts = Counter()
    patterns = 0
    failures = []
    for claim in CC.REGISTRY:
        try:
            n = claim.check(store)
            counts[claim.kind] += 1
            if claim.kind == "pattern":
                patterns += n
            if verbose:
                print("ok  %-14s %s" % (claim.id, claim.ref))
        except (CertificateError, KeyError) as exc:
            failures.append((claim.id, str(exc)))
            print("FAIL %s: %s" % (claim.id, exc))
    print("checked: %d identities, %d inequalities/contradictions, %d mutation paths, "
          "%d sign-pattern claims (%d patterns)" % (counts["identity"], counts["ineq"], counts["tuple"],
                                                   counts["pattern"], patterns))
    if failures:
        print("%d FAILURES" % len(failures))
        return 1
    print("All claims verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main("-v" in sys.argv))
