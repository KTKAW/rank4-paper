"""Computational evidence for Conjecture 5.5: every mutation-acyclic four-vertex quiver Q reaches an
acyclic quiver along a route on which every multiplicity is at most ht(Q).

Part 1 (exhaustive for small height). For every connected quiver of height h <= H1 (up to
relabeling), either a search within height h finds an acyclic quiver, or the quiver is shown to be
mutation-cyclic: by a mutation-cyclic full triangle, a vortex or a Markov exclusion within three
mutations, or else by the decision procedure of Corollary 5.2 (which relies on Theorem 5.1).
A quiver that is mutation-acyclic but needs more than its own height would be reported.
For H1 >= 3 the script also checks the statements about the quivers certified by Corollary 5.2
that the paper makes: the dreaded torus at height two, and at height three four quivers that are
mutation-equivalent, up to relabeling and reversal of all arrows, to the quiver of Example 5.4.

Part 2 (regions of mutation classes). For each connected acyclic quiver A with entries in [0, W],
every quiver reachable from A through quivers of height <= HR reaches an acyclic quiver without
exceeding its own height (computed as a minimax path problem inside the region).

Part 3 (random). Random mutation-acyclic quivers, obtained by random walks from acyclic quivers.

Run:  python3 conjecture_evidence.py            (default: H1 = 3, W = 2, HR = 10; a few minutes)
"""
import random
import sys
from collections import deque, Counter
from itertools import product
import quiver4 as Q

TORUS = (-2, 1, 1, -1, -1, -1)
EXAMPLE = (-3, -2, 2, 0, 3, -3)


def bounded_component(q, bound):
    comp, stack = {q}, [q]
    while stack:
        r = stack.pop()
        for k in Q.VERTICES:
            s = Q.mutate(r, k)
            if s not in comp and Q.height(s) <= bound:
                comp.add(s)
                stack.append(s)
    return comp


def part1(H1=3, table=600):
    sig = Q.endpoint_signatures(table)
    summary = {}
    for h in range(1, H1 + 1):
        reps = sorted({Q.canonical(q) for q in product(range(-h, h + 1), repeat=6)
                       if Q.height(q) == h and Q.is_connected(q)})
        tally = Counter()
        bad, by_search = [], []
        for q in reps:
            if Q.bounded_search(q, h)[0] == "acyclic":
                tally["reaches acyclic within its own height"] += 1
                continue
            frontier, seen, found = [q], {q}, False
            for depth in range(4):
                if any(Q.has_cyclic_full_triangle(r) or Q.is_vortex(r) or Q.markov_excluded(r, sig, table)
                       for r in frontier):
                    found = True
                    break
                nxt = []
                for r in frontier:
                    for k in Q.VERTICES:
                        s = Q.mutate(r, k)
                        if s not in seen:
                            seen.add(s)
                            nxt.append(s)
                frontier = nxt
            if found:
                tally["mutation-cyclic (obstruction within 3 mutations)"] += 1
                continue
            res = Q.decide(q, max_states=5_000_000)
            if res[0] == "cyclic":
                tally["mutation-cyclic (Corollary 5.2 search)"] += 1
                by_search.append(q)
            else:
                bad.append((q, res))
        summary[h] = (len(reps), dict(tally), bad, by_search)
        print("height %d: %d connected quivers up to relabeling: %s; certified by Corollary 5.2: %s; "
              "counterexamples/unresolved: %s" % (h, len(reps), dict(tally), by_search, bad))
    if H1 >= 2:
        assert summary[2][3] == [Q.canonical(TORUS)], summary[2][3]
    if H1 >= 3:
        hard = summary[3][3]
        assert len(hard) == 4, hard
        classes = [{Q.canonical(r) for r in bounded_component(x, 41)} for x in (EXAMPLE, Q.reverse(EXAMPLE))]
        assert all(any(q in cl for cl in classes) for q in hard)
        print("height 3: the four quivers certified by Corollary 5.2 are mutation-equivalent, up to relabeling "
              "and reversal, to the quiver of Example 5.4")
    return summary


def part2(W=2, HR=10):
    done = set()
    regions = states = viol = 0
    for A in product(range(W + 1), repeat=6):
        if not Q.is_connected(A) or A in done:
            continue
        region = {A}
        dq = deque([A])
        while dq:
            r = dq.popleft()
            for k in Q.VERTICES:
                s = Q.mutate(r, k)
                if s not in region and Q.height(s) <= HR:
                    region.add(s)
                    dq.append(s)
        done |= {q for q in region if Q.is_acyclic(q)}
        # minimax cost to an acyclic quiver, restricted to the region
        cost = {}
        for level in range(HR + 1):
            src = [q for q in region if Q.is_acyclic(q) and Q.height(q) <= level]
            dq = deque(src)
            vis = set(src)
            while dq:
                r = dq.popleft()
                cost.setdefault(r, level)
                for k in Q.VERTICES:
                    s = Q.mutate(r, k)
                    if s in region and s not in vis and Q.height(s) <= level:
                        vis.add(s)
                        dq.append(s)
        regions += 1
        states += len(region)
        viol += sum(1 for q in region if cost[q] > Q.height(q))
    print("regions from connected acyclic quivers with entries <= %d, height <= %d: %d regions, %d quivers, "
          "%d needing more than their own height" % (W, HR, regions, states, viol))
    return regions, states, viol


def part3(n=2000, seed=7):
    rng = random.Random(seed)
    count = viol = 0
    heights = []
    while count < n:
        A = tuple(rng.randint(0, rng.choice([1, 2, 3, 4, 5])) for _ in range(6))
        if not Q.is_connected(A):
            continue
        A = Q.relabel(A, tuple(rng.sample(Q.VERTICES, 4)))
        q, last = A, None
        for _ in range(rng.randint(3, 25)):
            k = rng.choice([v for v in Q.VERTICES if v != last])
            q, last = Q.mutate(q, k), k
            if Q.height(q) > 60:
                break
        if Q.height(q) > 60 or Q.height(q) < 6:
            continue
        count += 1
        heights.append(Q.height(q))
        if Q.bounded_search(q, Q.height(q), max_states=300000)[0] != "acyclic":
            viol += 1
            print("needs more than its own height (or search aborted):", q)
    print("random mutation-acyclic quivers: %d (heights %d..%d), %d exceptions" % (count, min(heights), max(heights), viol))
    return count, viol


def main(H1=3):
    s1 = part1(H1)
    _, _, v2 = part2()
    _, v3 = part3()
    ok = all(not s[2] for s in s1.values()) and v2 == 0 and v3 == 0
    print("No counterexample found." if ok else "COUNTEREXAMPLE OR UNRESOLVED CASE FOUND")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 3))
