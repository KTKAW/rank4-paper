"""Second, independent implementation of the basic operations (0-based vertex indices).

Written separately from quiver4.py, from the definitions in the paper, and used only by
tests.py to cross-check quiver4.py. It uses depth-first search for acyclicity, explicit
matrix mutation, and its own enumeration of wiggle classes."""
from itertools import combinations, permutations
from collections import deque

PAIRS = list(combinations(range(4), 2))


def mat(q):
    B = [[0] * 4 for _ in range(4)]
    for (i, j), v in zip(PAIRS, q):
        B[i][j] = v
        B[j][i] = -v
    return B


def tup(B):
    return tuple(B[i][j] for i, j in PAIRS)


def mu(q, k):
    """Mutation at vertex k (0-based) via the Fomin-Zelevinsky matrix rule."""
    B = mat(q)
    N = [[0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            if i == k or j == k:
                N[i][j] = -B[i][j]
            else:
                bik, bkj = B[i][k], B[k][j]
                N[i][j] = B[i][j] + max(bik, 0) * max(bkj, 0) - max(-bik, 0) * max(-bkj, 0)
    return tup(N)


def muw(q, w):
    """w is a sequence of 1-based vertices, applied left to right."""
    for k in w:
        q = mu(q, k - 1)
    return q


def relabel(q, pi):
    """Paper convention: b_ij(Q^pi) = b_{pi(i) pi(j)}(Q); pi given as dict/list on 1-based labels."""
    B = mat(q)
    p = [pi[i + 1] - 1 for i in range(4)]
    return tuple(B[p[i]][p[j]] for i, j in PAIRS)


PI12 = {1: 2, 2: 1, 3: 3, 4: 4}
PI123 = {1: 2, 2: 3, 3: 1, 4: 4}
PI34 = {1: 1, 2: 2, 3: 4, 4: 3}


def ht(q):
    return max(abs(x) for x in q)


def pf(q):
    a, b, c, d, e, f = q
    return a * f - b * e + c * d


def is_acyclic(q):
    B = mat(q)
    # DFS cycle detection
    color = [0] * 4

    def dfs(u):
        color[u] = 1
        for v in range(4):
            if B[u][v] > 0:
                if color[v] == 1:
                    return True
                if color[v] == 0 and dfs(v):
                    return True
        color[u] = 2
        return False

    return not any(color[u] == 0 and dfs(u) for u in range(4))


def is_connected(q):
    B = mat(q)
    seen = {0}
    st = [0]
    while st:
        u = st.pop()
        for v in range(4):
            if B[u][v] != 0 and v not in seen:
                seen.add(v)
                st.append(v)
    return len(seen) == 4


def markov_linear(q, order):
    """M for the linear order order[0]<...<order[3] (0-based vertex ids), formula (eq:markov-invariant)."""
    B = mat(q)
    v = order
    a, b, c = B[v[0]][v[1]], B[v[0]][v[2]], B[v[0]][v[3]]
    d, e = B[v[1]][v[2]], B[v[1]][v[3]]
    f = B[v[2]][v[3]]
    return a*a+b*b+c*c+d*d+e*e+f*f + a*b*d + a*c*e + b*c*f + d*e*f + a*c*d*f


def canon_cyc(order):
    i = order.index(0)
    return tuple(order[i:] + order[:i])


ALL_CYC = sorted({canon_cyc(list(p)) for p in permutations(range(4))})  # six cyclic orders


def vertex_proper(B, order, k):
    pos = {x: i for i, x in enumerate(order)}
    n = 4
    for i in range(n):
        if B[i][k] > 0:
            for j in range(n):
                if B[k][j] > 0:
                    # i, k, j must appear clockwise: going from i forward, k before j
                    if not ((pos[k] - pos[i]) % n < (pos[j] - pos[i]) % n):
                        return False
    return True


def wiggle_classes(q):
    B = mat(q)
    remaining = set(ALL_CYC)
    classes = []
    while remaining:
        s = remaining.pop()
        comp = {s}
        st = [s]
        while st:
            o = list(st.pop())
            for i in range(4):
                j = (i + 1) % 4
                if B[o[i]][o[j]] == 0:
                    o2 = o[:]
                    o2[i], o2[j] = o2[j], o2[i]
                    c = canon_cyc(o2)
                    if c not in comp:
                        comp.add(c)
                        remaining.discard(c)
                        st.append(c)
        classes.append(frozenset(comp))
    return classes


def proper_classes(q):
    B = mat(q)
    out = []
    for cl in wiggle_classes(q):
        if all(any(vertex_proper(B, list(o), k) for o in cl) for k in range(4)):
            out.append(cl)
    return out


def class_markov(q, cl):
    vals = {markov_linear(q, list(o)) for o in cl}
    assert len(vals) == 1, (q, cl, vals)
    return vals.pop()


def H(q):
    return max([ht(q)] + [abs(markov_linear(q, list(o))) for o in ALL_CYC])


def topo_order(q):
    B = mat(q)
    left = set(range(4))
    order = []
    while left:
        src = [i for i in sorted(left) if all(B[j][i] <= 0 for j in left)]
        if not src:
            return None
        order.append(src[0])
        left.remove(src[0])
    return order


def bounded_search(q, bound, max_states=None):
    """BFS within height <= bound. Returns (found_acyclic, states_visited, path)."""
    if ht(q) > bound:
        return None
    seen = {q: None}
    dq = deque([q])
    while dq:
        r = dq.popleft()
        if is_acyclic(r):
            path = []
            x = r
            while seen[x] is not None:
                x, k = seen[x]
                path.append(k)
            return True, len(seen), path[::-1]
        for k in range(4):
            s = mu(r, k)
            if s not in seen and ht(s) <= bound:
                seen[s] = (r, k + 1)
                dq.append(s)
                if max_states and len(seen) > max_states:
                    return 'aborted', len(seen), None
    return False, len(seen), None


def tri_cyclic_obstruction(q):
    B = mat(q)
    for i, j, k in combinations(range(4), 3):
        x, y, z = B[i][j], B[j][k], B[k][i]
        if (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0):
            x, y, z = abs(x), abs(y), abs(z)
            if min(x, y, z) >= 2 and x*x+y*y+z*z-x*y*z <= 4:
                return True
    return False


def is_vortex(q):
    if any(v == 0 for v in q):
        return False
    B = mat(q)
    for k in range(4):
        out_all = all(B[k][i] > 0 for i in range(4) if i != k)
        in_all = all(B[k][i] < 0 for i in range(4) if i != k)
        if out_all or in_all:
            i, j, l = [x for x in range(4) if x != k]
            if (B[i][j] > 0 and B[j][l] > 0 and B[l][i] > 0) or (B[i][j] < 0 and B[j][l] < 0 and B[l][i] < 0):
                return True
    return False
