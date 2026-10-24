"""Check census_certificates.json using only the independent implementation reference_q4.py.

Nothing from quiver4.py or census.py is imported: mutation, relabeling, acyclicity, connectivity,
mutation-cyclic triangles, vortices, proper wiggle classes and Markov values are recomputed by the
second implementation. Checks: coverage of all 15625 tuples by the 695 representatives, every
acyclic certificate (path within height 2 ending acyclic, and minimal length), every cyclic
certificate (path, obstruction), the dreaded torus, and the counts in Theorem 6.2.
Run:  python3 check_census.py
"""
import json
import math
from collections import Counter
from itertools import product, permutations
from pathlib import Path
import reference_q4 as R

HERE = Path(__file__).resolve().parent
PERMS = [{i + 1: p[i] + 1 for i in range(4)} for p in permutations(range(4))]


def canon(q):
    return min(R.relabel(q, pi) for pi in PERMS)


def word(q, w):
    for k in w:
        q = R.mu(q, k - 1)
    return q


def reach(q, depth, bound=None):
    seen = {q: 0}
    frontier = [q]
    for d in range(1, depth + 1):
        nxt = []
        for r in frontier:
            for k in range(4):
                s = R.mu(r, k)
                if s not in seen and (bound is None or R.ht(s) <= bound):
                    seen[s] = d
                    nxt.append(s)
        frontier = nxt
    return seen


def signatures(bound):
    out = set()
    top = math.isqrt(bound)
    for t in product(range(top + 1), repeat=6):
        if sum(x * x for x in t) > bound or not R.is_connected(t):
            continue
        mval = R.markov_linear(t, [0, 1, 2, 3])
        if mval <= bound:
            out.add((mval, R.pf(t) ** 2))
    return out


def markov_excluded(r, sig, bound):
    if not R.is_connected(r):
        return False
    cls = R.proper_classes(r)
    if not cls:
        return False
    p2 = R.pf(r) ** 2
    for cl in cls:
        mval = R.class_markov(r, cl)
        if mval < 3 or 4 * p2 >= mval * mval:
            continue
        assert mval <= bound, "signature table too small"
        if (mval, p2) in sig:
            return False
    return True


def main():
    data = json.loads((HERE / "census_certificates.json").read_text())
    reps = [tuple(q) for q in data["representatives"]]
    expected = sorted({canon(q) for q in product(range(-2, 3), repeat=6)})
    assert reps == expected and len(reps) == 695
    pos, neg = set(), set()
    depths = Counter()
    for q, w, end in data["acyclic_certificates"]:
        q, end = tuple(q), tuple(end)
        assert q in expected and q not in pos
        r = q
        for k in w:
            r = R.mu(r, k - 1)
            assert R.ht(r) <= 2
        assert r == end and R.is_acyclic(end)
        near = reach(q, len(w) - 1, 2) if w else {q: 0}
        assert w == [] and R.is_acyclic(q) or not any(R.is_acyclic(s) for s in near)
        pos.add(q)
        depths[len(w)] += 1
    assert dict(depths) == {0: 425, 1: 118, 2: 16, 3: 2}
    bound = data["markov_table_bound"]
    sig = signatures(bound)
    kinds, ndepth = Counter(), Counter()
    for q, w, kind, end in data["cyclic_certificates"]:
        q, end = tuple(q), tuple(end)
        assert q in expected and q not in pos and q not in neg and len(w) <= 2
        assert word(q, w) == end
        if kind == "triangle":
            assert R.tri_cyclic_obstruction(end)
        elif kind == "vortex":
            assert R.is_vortex(end) and not R.proper_classes(end)
        else:
            assert kind == "markov" and markov_excluded(end, sig, bound)
        neg.add(q)
        kinds[kind] += 1
        ndepth[len(w)] += 1
    torus = tuple(data["torus"])
    assert torus == canon((-2, 1, 1, -1, -1, -1)) and torus not in pos | neg
    assert all(canon(R.mu(torus, k)) == torus for k in range(4)) and not R.is_acyclic(torus)
    assert pos | neg | {torus} == set(expected)
    conn = lambda s: sum(1 for q in s if R.is_connected(q))
    counts = {"acyclic_connected": conn(pos), "acyclic_disconnected": len(pos) - conn(pos),
              "cyclic_connected": conn(neg) + 1, "cyclic_disconnected": len(neg) - conn(neg)}
    assert counts == {"acyclic_connected": 534, "acyclic_disconnected": 27,
                      "cyclic_connected": 133, "cyclic_disconnected": 1}, counts
    # connected cyclic representatives other than the torus, by certificate type and depth
    conn_neg = [c for c in data["cyclic_certificates"] if R.is_connected(tuple(c[0]))]
    assert Counter(c[2] for c in conn_neg) == Counter({"triangle": 45, "vortex": 40, "markov": 47})
    assert Counter(len(c[1]) for c in conn_neg) == Counter({0: 127, 1: 4, 2: 1})
    # Remark 6.3
    for q, w in [((-2, -1, 2, -1, -1, -1), (4, 1, 3)), ((-2, 1, 1, -2, 1, -1), (3, 2, 4))]:
        assert R.is_acyclic(word(q, w)) and not any(R.is_acyclic(s) for s in reach(q, 2))
    q = (-2, -1, 2, -1, -1, -2)
    assert R.tri_cyclic_obstruction(word(q, (1, 3)))
    for s in reach(q, 1):
        assert not R.tri_cyclic_obstruction(s) and not R.is_vortex(s)
        cls = R.proper_classes(s)
        assert len(cls) == 1 and (R.class_markov(s, cls[0]), R.pf(s) ** 2) == (3, 1)
    assert (R.markov_linear((1, 0, 0, 1, 0, 1), [0, 1, 2, 3]), R.pf((1, 0, 0, 1, 0, 1)) ** 2) == (3, 1)
    print("Census verified independently:", counts, "signature table through M =", bound)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
