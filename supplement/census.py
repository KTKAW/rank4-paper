"""Height-two census (Theorem 6.2): generate certificates for all 695 quivers of height <= 2.

Writes census_certificates.json (deterministic: no timestamps or interpreter versions, sorted
keys), which check_census.py verifies with the independent implementation in reference_q4.py.
Run:  python3 census.py
"""
import json
from collections import Counter, deque
from itertools import product
from pathlib import Path
import quiver4 as Q

HERE = Path(__file__).resolve().parent
OUT = HERE / "census_certificates.json"
TORUS = (-2, 1, 1, -1, -1, -1)


def bfs_words(q, depth, bound=None):
    """All quivers reachable from q by at most `depth` mutations (each step within `bound` if given),
    with a shortest word for each, in breadth-first order (deterministic)."""
    out = [(q, ())]
    seen = {q}
    frontier = [(q, ())]
    for _ in range(depth):
        nxt = []
        for r, w in frontier:
            for k in Q.VERTICES:
                s = Q.mutate(r, k)
                if s in seen or (bound is not None and Q.height(s) > bound):
                    continue
                seen.add(s)
                nxt.append((s, w + (k,)))
        out.extend(nxt)
        frontier = nxt
    return out


def main():
    reps = sorted({Q.canonical(q) for q in product(range(-2, 3), repeat=6)})
    positive, remaining = {}, []
    for q in reps:
        hit = next(((r, w) for r, w in bfs_words(q, 3, 2) if Q.is_acyclic(r)), None)
        if hit is None:
            remaining.append(q)
        else:
            positive[q] = hit
    torus = Q.canonical(TORUS)
    candidates = {q: bfs_words(q, 2) for q in remaining if q != torus}
    # Markov values that the exclusion test will need (only after the two cheap obstructions fail)
    needed = 0
    for q, lst in candidates.items():
        for r, w in lst:
            if Q.has_cyclic_full_triangle(r) or Q.is_vortex(r):
                continue
            for m in Q.proper_values(r):
                if m >= 3 and 4 * Q.pfaffian(r) ** 2 < m * m:
                    needed = max(needed, m)
    signatures = Q.endpoint_signatures(needed)
    negative = {}
    for q in sorted(candidates):
        lst = candidates[q]
        found = None
        for depth in range(3):            # shortest certificate first, then (a), (b), (c)
            for name, test in (("triangle", Q.has_cyclic_full_triangle), ("vortex", Q.is_vortex),
                               ("markov", lambda r: Q.markov_excluded(r, signatures, needed))):
                found = next(((r, w, name) for r, w in lst if len(w) == depth and test(r)), None)
                if found:
                    break
            if found:
                break
        if found is None:
            raise SystemExit("no certificate for %r" % (q,))
        negative[q] = found
    data = {
        "representatives": [list(q) for q in reps],
        "torus": list(torus),
        "acyclic_certificates": [[list(q), list(w), list(r)] for q, (r, w) in sorted(positive.items())],
        "cyclic_certificates": [[list(q), list(w), name, list(r)] for q, (r, w, name) in sorted(negative.items())],
        "markov_table_bound": needed,
    }
    OUT.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    conn = lambda qs: sum(1 for q in qs if Q.is_connected(q))
    summary = {
        "representatives": len(reps), "connected": conn(reps),
        "mutation_acyclic": len(positive), "mutation_acyclic_connected": conn(positive),
        "shortest_lengths": dict(sorted(Counter(len(w) for r, w in positive.values()).items())),
        "mutation_cyclic": len(negative) + 1, "mutation_cyclic_connected": conn(negative) + 1,
        "certificate_types": dict(sorted(Counter(n for _, _, n in negative.values()).items())),
        "certificate_depths": dict(sorted(Counter(len(w) for _, w, _ in negative.values()).items())),
        "markov_table_bound": needed, "endpoint_signatures": len(signatures),
    }
    print(json.dumps(summary, indent=1))
    return summary


if __name__ == "__main__":
    main()
