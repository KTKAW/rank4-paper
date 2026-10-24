"""Property tests and cross-implementation tests for quiver4.py.

These look for the usual sources of silent error: index conventions (0- vs 1-based vertices,
the direction of a relabeling, the order of a mutation word), sign conventions, and arithmetic.
Python ints cannot overflow, and nothing here uses floating point; tests below also run on
entries far beyond 64-bit range to make sure no code path silently assumes machine integers.
"""
import random
from itertools import permutations
import quiver4 as Q
import reference_q4 as R


def rand_quiver(rng, w):
    return tuple(rng.randint(-w, w) for _ in range(6))


def to_ref_perm(pi):
    # quiver4 uses a tuple (pi(1),...,pi(4)); reference uses a dict on 1-based labels
    return {i + 1: pi[i] for i in range(4)}


def proper_mutation_order(q, order, k):
    """Fomin-Neville proper mutation of a cyclic ordering: k must be proper in `order`;
    after mutating, k moves clockwise past its out-neighbours (in q) without passing an
    in-neighbour. Returns the new cyclic ordering (defined up to wiggles)."""
    assert Q.vertex_is_proper(q, order, k)
    pos = order.index(k)
    rest = [order[(pos + s) % 4] for s in range(1, 4)]  # clockwise after k
    outs = [i for i, v in enumerate(rest) if Q.entry(q, k, v) > 0]
    ins = [i for i, v in enumerate(rest) if Q.entry(q, v, k) > 0]
    if outs and ins:
        assert max(outs) < min(ins), (q, order, k)
    last = max(outs) if outs else -1
    new = rest[:last + 1] + [k] + rest[last + 1:]
    return Q.normalize_cyclic(new)


def class_of(q, order):
    for cl in Q.wiggle_classes(q):
        if Q.normalize_cyclic(order) in cl:
            return cl
    raise AssertionError


def test_cross_implementation(rng, n=20000):
    for _ in range(n):
        q = rand_quiver(rng, rng.choice([1, 2, 3, 6, 50]))
        for k in Q.VERTICES:
            assert Q.mutate(q, k) == R.mu(q, k - 1)
        pi = tuple(rng.sample(Q.VERTICES, 4))
        assert Q.relabel(q, pi) == R.relabel(q, to_ref_perm(pi))
        assert Q.is_acyclic(q) == R.is_acyclic(q)
        assert Q.is_connected(q) == R.is_connected(q)
        assert Q.is_vortex(q) == R.is_vortex(q)
        assert Q.has_cyclic_full_triangle(q) == R.tri_cyclic_obstruction(q)
        assert Q.pfaffian(q) == R.pf(q)
        order = tuple(rng.sample(Q.VERTICES, 4))
        assert Q.markov(q, order) == R.markov_linear(q, [v - 1 for v in order])
        mine = sorted(tuple(sorted(cl)) for cl in Q.proper_classes(q))
        ref = sorted(tuple(sorted(tuple(v + 1 for v in o) for o in cl)) for cl in R.proper_classes(q))
        assert mine == ref, (q, mine, ref)
        assert Q.H_paper(q) == R.H(q)
    return n


def test_algebraic_properties(rng, n=20000):
    for _ in range(n):
        q = rand_quiver(rng, rng.choice([2, 5, 10 ** 30]))  # also far beyond 64-bit range
        for k in Q.VERTICES:
            r = Q.mutate(q, k)
            assert Q.mutate(r, k) == q                       # involution
            assert Q.pfaffian(r) == -Q.pfaffian(q)           # Pfaffian changes sign
            assert Q.components(r) == Q.components(q)        # components preserved
            assert Q.mutate(Q.reverse(q), k) == Q.reverse(r)  # commutes with reversal
        pi = tuple(rng.sample(Q.VERTICES, 4))
        inv = Q.inverse_perm(pi)
        for k in Q.VERTICES:                                  # tail transport (eq. tailtransport)
            assert Q.mutate(Q.relabel(q, pi), inv[k - 1]) == Q.relabel(Q.mutate(q, k), pi)
        sign = 1
        p = list(pi)
        for i in range(4):
            for j in range(i + 1, 4):
                if p[i] > p[j]:
                    sign = -sign
        assert Q.pfaffian(Q.relabel(q, pi)) == sign * Q.pfaffian(q)
        order = tuple(rng.sample(Q.VERTICES, 4))
        rot = order[1:] + order[:1]
        assert Q.markov(q, order) == Q.markov(q, rot)                     # rotation
        assert Q.markov(Q.reverse(q), tuple(reversed(order))) == Q.markov(q, order)  # opposite
    return n


def test_pentagon(rng, n=20000):
    for _ in range(n):
        q = (rng.choice([1, -1]),) + tuple(rng.randint(-12, 12) for _ in range(5))
        assert Q.mutate_word(q, (1, 2, 1, 2, 1)) == Q.relabel(q, Q.PI12)
    return n


def test_word_and_relabel_conventions():
    q = (1, 2, -1, 3, 0, -2)
    assert Q.mutate_word(q, (1, 2, 3)) == Q.mutate(Q.mutate(Q.mutate(q, 1), 2), 3)
    assert Q.mutate_word(q, "123") == Q.mutate_word(q, "1,2,3") == Q.mutate_word(q, [1, 2, 3])
    # relabeling: old vertex pi(i) gets new label i
    pi = Q.PI123
    r = Q.relabel(q, pi)
    for i in Q.VERTICES:
        for j in Q.VERTICES:
            if i != j:
                assert Q.entry(r, i, j) == Q.entry(q, pi[i - 1], pi[j - 1])
    assert pi[0] == 2 and pi[1] == 3 and pi[2] == 1
    for bad in [(1, 2, 3), (1.0, 0, 0, 0, 0, 0), [0] * 6]:
        try:
            Q.height(bad)
        except TypeError:
            pass
        else:
            raise AssertionError("bad input accepted: %r" % (bad,))
    for badk in (0, 5, "1", 1.0):
        try:
            Q.mutate(q, badk)
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError("bad vertex accepted: %r" % (badk,))
    return 1


def test_proper_mutation_invariance(rng, n=6000):
    """Markov value is invariant under proper mutations (Fomin-Neville), with our formula."""
    count = 0
    for _ in range(n):
        q = rand_quiver(rng, rng.choice([1, 2, 4, 9]))
        order = Q.normalize_cyclic(tuple(rng.sample(Q.VERTICES, 4)))
        for k in Q.VERTICES:
            if Q.vertex_is_proper(q, order, k):
                new = proper_mutation_order(q, order, k)
                assert Q.markov(Q.mutate(q, k), new) == Q.markov(q, order), (q, order, k)
                count += 1
    return count


def test_totally_proper_transport(rng, n=3000):
    """Transport the topological class of an acyclic A along a random word by proper mutations;
    the result is a proper class of the endpoint with the same Markov value."""
    done = 0
    while done < n:
        A = tuple(rng.randint(0, rng.choice([1, 2, 3])) for _ in range(6))
        pi = tuple(rng.sample(Q.VERTICES, 4))
        A = Q.relabel(A, pi)
        topo = Q.topological_order(A)
        m = Q.markov(A, topo)
        q, cl = A, class_of(A, topo)
        for _ in range(rng.randint(1, 8)):
            k = rng.choice(Q.VERTICES)
            members = [o for o in cl if Q.vertex_is_proper(q, o, k)]
            assert members, "class stopped being proper (would contradict Neville's theorem)"
            new = proper_mutation_order(q, members[0], k)
            q = Q.mutate(q, k)
            cl = class_of(q, new)
        assert cl in Q.proper_classes(q)
        assert Q.class_markov(q, cl) == m
        done += 1
    return done


def main(seed=20261023):
    rng = random.Random(seed)
    out = {}
    out["cross_implementation"] = test_cross_implementation(rng)
    out["algebraic_properties"] = test_algebraic_properties(rng)
    out["pentagon"] = test_pentagon(rng)
    out["conventions"] = test_word_and_relabel_conventions()
    out["proper_mutation_invariance"] = test_proper_mutation_invariance(rng)
    out["totally_proper_transport"] = test_totally_proper_transport(rng)
    out["checker_rejects_bad_certificates"] = test_checker_rejects_bad_certificates()
    out["symbolic_vs_numeric_mutation"] = test_symbolic_against_numeric(rng)
    return out



def test_checker_rejects_bad_certificates():
    """The certificate checker must reject wrong identities, negative coefficients, unknown
    hypotheses, and 'proofs' of false statements."""
    from polynomial import V
    from certificates import check_certificate, CertificateError, PS, H
    x, y = V("x"), V("y")
    hyps = {"x1": x - 1, "y1": y - 1}
    good = (H("x1") * H("y1") + H("x1") + H("y1")).cert()          # xy - 1 = (x-1)(y-1) + (x-1) + (y-1)
    assert check_certificate(hyps, {}, ("ge0", x * y - 1), good)
    bad_cases = [
        (("ge0", x * y - 2), good),                                      # false goal: residual -1 < 0
        (("ge0", x * y - 1), {"kind": "sum", "terms": [{"c": -1, "hyps": ["x1"], "sq": None}], "eqs": [], "const": "auto"}),
        (("ge0", x * y - 1), {"kind": "sum", "terms": [{"c": 1, "hyps": ["zz"], "sq": None}], "eqs": [], "const": "auto"}),
        (("contra",), good),                                             # x,y >= 1 is consistent
        (("ge0", x - 2), (H("x1")).cert()),                              # x >= 1 does not give x >= 2
    ]
    for goal, cert in bad_cases:
        try:
            check_certificate(hyps, {}, goal, cert)
        except CertificateError:
            continue
        raise AssertionError("checker accepted a bad certificate: %r" % (goal,))
    return len(bad_cases)


def test_symbolic_against_numeric(rng, n=3000):
    """Symbolic mutation with certified signs agrees with numeric mutation at sample points."""
    import symbolic as S
    from polynomial import V
    a, b, c = V("a"), V("b"), V("c")
    for _ in range(n):
        av, bv, cv = rng.randint(1, 9), rng.randint(1, 9), rng.randint(1, 9)
        t = S.as_poly_tuple((a, -b, c, b - a + 0 * c, -c, a * b))
        q = tuple(int(p.evaluate({"a": av, "b": bv, "c": cv})) for p in t)
        k = rng.choice(Q.VERTICES)
        signs = {}
        for i, xpoly in S.incident_entries(t, k):
            val = xpoly.evaluate({"a": av, "b": bv, "c": cv})
            signs[i] = "+" if val >= 0 else "-"
        r = S.smutate(t, k, signs)
        assert tuple(int(p.evaluate({"a": av, "b": bv, "c": cv})) for p in r) == Q.mutate(q, k)
    return n


if __name__ == "__main__":
    print(main())
