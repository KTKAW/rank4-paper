"""Concrete checks of the examples and remarks in the paper.

  * Theorem 3.2: the small cases t = -2, -1, 0, 1 of the family Q(t) (the general cases are the
    symbolic claims S3.* in proof_claims.py);
  * Remark 3.3: every Q(t), 0 <= t < 200, has a single proper wiggle class, with (M, p^2) = (12, 16),
    the pair of the acyclic quiver Q(0) (t >= 3 is also the symbolic claim S3.Qt-class);
  * Remark 3.4: the higher-rank family Q_n(t) for n = 5..8 and -5 <= t <= 12;
  * Remark 4.6: the route showing that minimality cannot be dropped;
  * Example 5.4: the height-three quiver (-3,-2,2,0,3,-3) is mutation-cyclic by Corollary 5.2,
    and no quiver in its bounded component has a mutation-cyclic triangle, is a vortex, or is
    Markov-excluded; the component contains the oriented four-cycle (3,-2,0,0,9,-1);
  * Remark 5.6: the family mu_4 G_x;
  * the decision procedure of Corollary 5.2 on a few inputs.
Run:  python3 examples.py
"""
import quiver4 as Q


def Qt(t):
    return (-2, t + 2, t, -t, 2 - t, 0)


def mutate_n(B, k):
    n = len(B)
    N = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k or j == k:
                N[i][j] = -B[i][j]
            else:
                N[i][j] = B[i][j] + max(B[i][k], 0) * max(B[k][j], 0) - max(-B[i][k], 0) * max(-B[k][j], 0)
    return N


def family():
    for t in (-2, -1, 0):
        assert Q.is_acyclic(Qt(t))
    q1 = Q.mutate(Qt(1), 2)
    assert q1 == (2, 1, 1, 1, -1, 1) and Q.is_vortex(q1) and not Q.proper_classes(q1)
    for t in range(-60, 61):
        assert Q.is_connected(Qt(t)) and Q.pfaffian(Qt(t)) == -4
    for t in range(2, 200):
        assert Q.relabel(Q.mutate(Qt(t), 2), Q.PI12) == Qt(t - 2)
    # Remark 3.3: unique proper class, signature (12, 16), equal to that of the acyclic Q(0)
    for t in range(0, 200):
        assert Q.proper_values(Qt(t)) == [12] and Q.pfaffian(Qt(t)) ** 2 == 16
    assert Q.markov(Qt(0), Q.topological_order(Qt(0))) == 12
    return "family Q(t): checked"


def higher_rank():
    count = 0
    for n in range(5, 9):
        for t in range(-5, 13):
            B = [[0] * n for _ in range(n)]
            M4 = Q.matrix(Qt(t))
            for i in range(4):
                for j in range(4):
                    B[i][j] = M4[i][j]
            B[4][2], B[2][4] = 1, -1                       # 5 -> 3
            for i in range(5, n):
                B[i][i - 1], B[i - 1][i] = 1, -1           # i+1 -> i
            if t >= 2:
                N = mutate_n(B, 1)
                perm = [1, 0] + list(range(2, n))
                Np = [[N[perm[i]][perm[j]] for j in range(n)] for i in range(n)]
                target = Q.matrix(Qt(t - 2))
                assert all(Np[i][j] == target[i][j] for i in range(4) for j in range(4))
                assert all(Np[i][j] == B[i][j] for i in range(n) for j in range(n) if i >= 4 or j >= 4)
            count += 1
    return "higher-rank family: %d cases" % count


def remark_minimality():
    root = (1, 1, -1, 1, 0, 0)
    assert Q.is_acyclic(root) and Q.proper_values(root) == [5] and Q.height(root) == 1
    w1, seg, tail = (2, 3, 1, 3, 1, 3, 1, 3), (1, 2, 1, 3, 2), (1, 2, 1, 2, 3)
    p1 = Q.path(root, w1)
    assert [Q.height(q) for q in p1[1:]] == [2, 2, 2, 2, 2, 3, 4, 5]
    C = p1[-1]
    assert C == (1, -2, 5, 1, -1, -4) and not Q.is_acyclic(C)
    p2 = Q.path(C, seg)
    assert [Q.height(q) for q in p2] == [5, 6, 6, 6, 6, 5]
    p3 = Q.path(p2[-1], tail)
    assert [Q.height(q) for q in p3[1:]] == [4, 3, 2, 2, 1] and p3[-1] == (1, 1, 0, -1, 1, 0) and Q.is_acyclic(p3[-1])
    full = w1 + seg + tail
    assert all(a != b for a, b in zip(full, full[1:]))
    return "Remark 4.6: checked"


def height_three_example():
    q = (-3, -2, 2, 0, 3, -3)
    assert Q.height(q) == 3 and Q.proper_values(q) == [41] and Q.pfaffian(q) ** 2 == 225
    assert (41, 225) in Q.endpoint_signatures(41)          # realized by a connected acyclic quiver
    assert Q.markov((0, 0, 3, 5, 1, 1), (1, 2, 3, 4)) == 41 and Q.pfaffian((0, 0, 3, 5, 1, 1)) ** 2 == 225
    B = Q.search_bound(q)
    assert B == 41
    status, n = Q.bounded_search(q, B)
    assert status == "exhausted"
    # the component itself
    comp = {q}
    stack = [q]
    while stack:
        r = stack.pop()
        for k in Q.VERTICES:
            s = Q.mutate(r, k)
            if s not in comp and Q.height(s) <= B:
                comp.add(s)
                stack.append(s)
    assert len(comp) == n == 238
    four_cycle = (3, -2, 0, 0, 9, -1)                       # 1 -> 2 -> 4 -> 3 -> 1, multiplicities 3, 9, 1, 2
    assert four_cycle in comp and [Q.entry(four_cycle, i, j) for i, j in ((1, 2), (2, 4), (4, 3), (3, 1))] == [3, 9, 1, 2]
    maxm = max(m for r in comp for m in Q.proper_values(r))
    sig = Q.endpoint_signatures(maxm)
    for r in comp:
        assert not Q.is_acyclic(r) and not Q.has_cyclic_full_triangle(r) and not Q.is_vortex(r)
        assert not Q.markov_excluded(r, sig, maxm)
    return "Example 5.4: component of %d quivers within height %d, no obstruction (Markov table to %d)" % (n, B, maxm)


def family_Ax():
    for xv in range(1, 30):
        A = (xv, xv, 0, 1, xv, -1)
        assert Q.is_acyclic(A)
        m = Q.markov(A, Q.topological_order(A))
        assert m == xv ** 3 + 4 * xv ** 2 + xv + 2
        r = Q.mutate(A, 4)
        assert Q.height(r) == xv + 1 and not Q.is_acyclic(r) and Q.proper_values(r) == [m]
    return "Remark 5.6: checked for 1 <= x <= 29"


def decision_examples():
    out = []
    for q in [Qt(4), Qt(5), (1, 1, -1, 1, 0, 0), (-2, 0, 2, -2, 0, -2), (-2, 1, 1, -1, -1, -1)]:
        res = Q.decide(q)
        out.append((q, res[0]))
    assert [r for _, r in out] == ["acyclic", "cyclic", "acyclic", "cyclic", "cyclic"]
    return "decision procedure: %s" % out


def main():
    for f in (family, higher_rank, remark_minimality, height_three_example, family_Ax, decision_examples):
        print(f())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
