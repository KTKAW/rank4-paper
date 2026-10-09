"""Independent checks of the manuscript's finite calculations.

Run: python3 Paper_draft/verify_examples.py
Uses only the standard library. Finite failed searches are not NMA proofs;
their completeness is a separately cited Lean theorem.
"""
from itertools import permutations, product
from pathlib import Path
import json

PAIRS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


def matrix(q):
    b = [[0] * 4 for _ in range(4)]
    for (i, j), x in zip(PAIRS, q):
        b[i][j], b[j][i] = x, -x
    return b


def mutate(q, k):
    b = matrix(q)
    return tuple(
        -b[i][j] if k in (i, j) else
        b[i][j] + max(b[i][k], 0) * max(b[k][j], 0)
        - max(-b[i][k], 0) * max(-b[k][j], 0)
        for i, j in PAIRS
    )


def word(q, w):
    for k in w:
        q = mutate(q, k)
    return q


def rank_ok(q, r):
    b = matrix(q)
    return all(b[i][j] <= 0 or r[i] < r[j]
               for i in range(4) for j in range(4))


def acyclic(q):
    return any(rank_ok(q, r) for r in permutations(range(4)))


def line(t):
    return (-2, t + 2, t, -t, 2 - t, 0)


def pf(q):
    a, b, c, d, e, f = q
    return a*f - b*e + c*d


def markov(q):
    a, b, c, d, e, f = q
    return sum(x*x for x in q) + a*b*d + a*c*e + b*c*f + d*e*f + a*c*d*f


def main():
    assert rank_ok(line(0), (1, 0, 2, 2))
    assert mutate(line(2), 1) == (2, 0, 2, 2, 0, 0)
    assert rank_ok(mutate(line(2), 1), (0, 1, 2, 1))
    assert rank_ok(line(-1), (2, 0, 3, 1))
    for t in range(-100, -1):
        assert rank_ok(line(t), (2, 0, 1, 1))
    for t in range(101):
        assert word(line(t), (0, 1)) == line(t + 4)
    s1 = (-2, -1, -1, 1, -1, 1)
    s3 = (-2, 1, -1, 1, 1, 1)
    assert word(s1, (0, 1)) == line(1)
    assert word(line(3), (1, 0)) == s3
    short_words = [w for d in range(4) for w in product(range(4), repeat=d)]
    assert len(short_words) == 85
    assert not any(acyclic(word(s, w)) for s in (s1, s3) for w in short_words)
    assert markov((0, -1, 0, 1, 0, 0)) == 2
    assert mutate((0, -1, 0, 1, 0, 0), 2) == (-1, 1, 0, -1, 0, 0)
    assert markov((-1, 1, 0, -1, 0, 0)) == 4
    assert pf((1, 1, 1, 2, 1, 1)) == pf((-2, 1, 1, -1, -1, -1)) == 2
    assert acyclic(mutate((-2, -1, 1, -1, 2, -1), 2))
    for x, y, z, u in product(range(1, 4), repeat=4):
        for v in (x*y, x*y + 1):
            q = (0, -x, y, -z, -u, -v)
            assert mutate(q, 0) == (0, x, -y, -z, -u, x*y-v)
            assert rank_ok(mutate(q, 0), (1, 3, 2, 0))
    for c, d in product(range(1, 6), repeat=2):
        for b in (d*(c-1), d*(c-1)+1):
            q = (-1, -b, c, d, -1, 0)
            endpoint = (1, d*(c-1)-b, 1-c, 0, -1, d)
            assert not acyclic(q)
            assert word(q, (1, 3)) == endpoint
            assert rank_ok(endpoint, (2, 3, 0, 1))
    for a, c, e, f in product((-3, -1), (1, 3), (1, 2), (-3, -1)):
        for delta_b, delta_d in product((0, 1), repeat=2):
            b, d = c*f-delta_b, e*f-delta_d
            q = (a, b, c, d, e, f)
            endpoint = (a, b-c*f, -c, d-e*f, -e, -f)
            assert mutate(q, 3) == endpoint
            assert rank_ok(endpoint, (3, 2, 0, 1))
    # Recheck the independent finite-orbit negative witness.
    start = (-2, 1, 1, -1, -1, -1)
    seen, pending = {start}, [start]
    while pending:
        q = pending.pop()
        assert not acyclic(q)
        for k in range(4):
            nxt = mutate(q, k)
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
        assert len(seen) <= 24
    assert len(seen) == 24
    report = {
        "status": "PASS",
        "short_words_per_seed": 85,
        "negative_seeds_checked": 2,
        "closed_cyclic_orbit_size": 24,
        "scope": "Exact finite examples and sampled parameter identities; universal statements rely on the cited mathematical and Lean proofs.",
    }
    Path(__file__).with_name("example_checks.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
