"""Exhaustive finite check of the local analysis (Lemmas 4.2-4.4 and Proposition 4.5) for small T.

This is an independent sanity check of the CASE ANALYSIS, not part of the proof: check_proofs.py
verifies the calculations for all T, and the case analysis itself is written out in the paper.
Here, for each T <= T_max, we enumerate every low quiver C and every high excursion from it, using
only facts that hold for every quiver in a connected mutation-acyclic class with Markov invariant
3 <= m <= T and 2|p| < m:
  * every quiver on the excursion has a proper wiggle class with Markov value m
    (the transported totally proper class, Theorem 2.2);
  * no quiver on it contains a mutation-cyclic full triangle (Proposition 2.1);
  * C is not acyclic (a minimizing route meets its first acyclic quiver only at its end).
For every excursion found we check the conclusion the proof of Theorem 5.1 needs.

Run:  python3 bruteforce_local.py [T_max]      (default T_max = 6; T_max = 7 takes a few minutes)
"""
import sys
from itertools import product
from functools import lru_cache
import quiver4 as Q

DEPTH = 10


@lru_cache(maxsize=None)
def proper_vals(q):
    if Q.has_cyclic_full_triangle(q):
        return frozenset()
    return frozenset(Q.proper_values(q))


def excursions(C, m, F):
    """Reduced excursions from C starting with the mutation at 1: every intermediate quiver has
    height exactly F and admits m; stop at the first low quiver. Yields (kind, word, path)."""
    P = Q.mutate(C, 1)
    if Q.height(P) != F or m not in proper_vals(P):
        return
    stack = [((1,), (C, P))]
    while stack:
        w, qs = stack.pop()
        if len(w) > DEPTH:
            yield ("depth", w, qs)
            continue
        X = qs[-1]
        for k in Q.VERTICES:
            if k == w[-1]:
                continue
            Y = Q.mutate(X, k)
            h = Q.height(Y)
            if h > F or m not in proper_vals(Y):
                continue
            if h < F:
                yield ("return", w + (k,), qs + (Y,))
            else:
                stack.append((w + (k,), qs + (Y,)))


def low_route_exists(C, target, letters, maxlen, bound, allow_swap):
    """Is target (or its 1<->2 swap) reachable from C by at most maxlen mutations at `letters`,
    with every quiver after C of height <= bound?"""
    targets = {target} | ({Q.relabel(target, Q.PI12)} if allow_swap else set())
    frontier = [(C, ())]
    for _ in range(maxlen + 1):
        nxt = []
        for q, w in frontier:
            if q in targets:
                return True
            for k in letters:
                if w and w[-1] == k:
                    continue
                r = Q.mutate(q, k)
                if Q.height(r) <= bound:
                    nxt.append((r, w + (k,)))
        frontier = nxt
    return False


def check_T(T):
    F = T + 1
    A = {(1, -2, c, 1, 0, F - 2 * c): c for c in range(1, T + 1)}
    I = {(1, -1, -t, 2, t - F, F - u): (t, u) for t in range(1, T + 1) for u in range(1, T + 1)}
    stats, problems = {}, []

    def bump(key):
        stats[key] = stats.get(key, 0) + 1

    R = range(-T, T + 1)
    for C in product(R, repeat=6):
        if not Q.is_connected(C) or Q.is_acyclic(C):
            continue
        if Q.height(Q.mutate(C, 1)) != F:
            continue
        p2 = Q.pfaffian(C) ** 2
        ms = [m for m in proper_vals(C) if 3 <= m <= T and 4 * p2 < m * m]
        for m in ms:
            for j in (2, 3, 4):
                pi = {2: (1, 2, 3, 4), 3: (1, 3, 2, 4), 4: (1, 4, 3, 2)}[j]
                Cn = Q.relabel(C, pi)          # the second excursion vertex becomes 2
                mult = abs(Cn[0])
                for kind, w, qs in excursions(Cn, m, F):
                    if len(w) < 2 or w[1] != 2:
                        continue
                    if kind == "depth":
                        problems.append(("depth limit reached", Cn, m, w))
                        continue
                    end = qs[-1]
                    if mult == 0:
                        bump("no edge")
                        if w not in ((1, 2), (1, 2, 1)):
                            problems.append(("Lemma 4.2 shape", Cn, m, w))
                        if not low_route_exists(Cn, end, (1, 2), 2, T, False):
                            problems.append(("Lemma 4.2 replacement", Cn, m, w))
                    elif mult >= 2:
                        problems.append(("Lemma 4.4: excursion returned", Cn, m, w))
                    else:
                        third = [k for k in w if k > 2]
                        if not third:
                            bump("single arrow, only 1 and 2")
                            if not low_route_exists(Cn, end, (1, 2), 3, T, True):
                                problems.append(("Lemma 4.3 / Prop 4.5(a)", Cn, m, w))
                            continue
                        first = w.index(third[0])
                        prefix = w[:first]
                        Cs = Cn if Cn[0] == 1 else Q.reverse(Cn)
                        if prefix == (1, 2):
                            wn, Cc = w, Cs
                            if third[0] == 4:
                                Cc = Q.relabel(Cs, Q.PI34)
                                wn = tuple({3: 4, 4: 3}.get(k, k) for k in w)
                            if Cc in A:
                                bump("A_c")
                                if wn != (1, 2, 3, 1, 3):
                                    problems.append(("A_c word", Cc, m, wn))
                            elif Cc in I and I[Cc][0] != I[Cc][1]:
                                bump("I_{t,u}")
                                if wn != (1, 2, 3):
                                    problems.append(("I word", Cc, m, wn))
                            else:
                                problems.append(("unclassified", Cc, m, wn))
                        elif len(prefix) == 3:
                            bump("prefix [1,2,1] (replaced by minimality)")
                            if Q.height(Q.mutate(Cn, 2)) > F:
                                problems.append(("Appendix B.1: mu_2 C too high", Cn, m, w))
                        else:
                            bump("prefix of length >= 4 (replaced by minimality)")
                            X = qs[len(prefix)]
                            if not low_route_exists(Cn, X, (1, 2), 3, F, True):
                                problems.append(("Appendix B.1: long prefix", Cn, m, w))
    return stats, problems


def main(tmax=6):
    ok = True
    for T in range(3, tmax + 1):
        stats, problems = check_T(T)
        print("T = %d: excursions by type %s; problems: %d" % (T, dict(sorted(stats.items())), len(problems)))
        for p in problems[:10]:
            print("   ", p)
        ok = ok and not problems
    print("Local analysis confirmed for T <= %d." % tmax if ok else "PROBLEMS FOUND")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 6))
