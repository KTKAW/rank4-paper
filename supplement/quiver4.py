"""Rank-four quiver operations used throughout the supplement.

Conventions (identical to the paper):
  * A quiver is a 6-tuple q = (b12, b13, b14, b23, b24, b34) of Python ints; b_ij > 0 means
    b_ij arrows i -> j. Vertices are 1, 2, 3, 4 in every public function.
  * mutate(q, k) is Fomin-Zelevinsky matrix mutation at vertex k.
  * A mutation word is a sequence of vertices performed left to right: word (1, 2, 3)
    means mutate at 1, then 2, then 3.
  * relabel(q, pi) is Q^pi with b_ij(Q^pi) = b_{pi(i) pi(j)}(Q); pi is a tuple
    (pi(1), pi(2), pi(3), pi(4)). Old vertex pi(i) receives the new label i.
  * A cyclic ordering is a tuple of the four vertices read clockwise, normalized so that it
    starts with vertex 1. markov(q, order) reads the exchange matrix in the linear order
    order[0] < order[1] < order[2] < order[3].

All arithmetic is on Python ints, which have arbitrary precision, so nothing can overflow.
Nothing here uses floating point. Every function validates its inputs.
"""
from itertools import combinations, permutations
from collections import deque

PAIRS = tuple(combinations((1, 2, 3, 4), 2))  # ((1,2),(1,3),(1,4),(2,3),(2,4),(3,4))
VERTICES = (1, 2, 3, 4)
PI12 = (2, 1, 3, 4)
PI34 = (1, 2, 4, 3)
PI123 = (2, 3, 1, 4)   # pi(1)=2, pi(2)=3, pi(3)=1
ALL_PERMUTATIONS = tuple(permutations(VERTICES))


def check_quiver(q):
    if not (isinstance(q, tuple) and len(q) == 6 and all(type(x) is int for x in q)):
        raise TypeError("a quiver is a tuple of six Python ints, got %r" % (q,))
    return q


def _check_vertex(k):
    if type(k) is not int or k not in VERTICES:
        raise ValueError("vertices are the ints 1, 2, 3, 4; got %r" % (k,))
    return k


def entry(q, i, j):
    """b_ij(q) for vertices i != j (antisymmetric)."""
    _check_vertex(i)
    _check_vertex(j)
    if i == j:
        return 0
    if i < j:
        return q[PAIRS.index((i, j))]
    return -q[PAIRS.index((j, i))]


def matrix(q):
    """The 4x4 exchange matrix as a list of lists, indexed B[i-1][j-1] = b_ij."""
    check_quiver(q)
    return [[entry(q, i, j) for j in VERTICES] for i in VERTICES]


def from_matrix(B):
    if len(B) != 4 or any(len(r) != 4 for r in B):
        raise ValueError("need a 4x4 matrix")
    if any(type(x) is not int for r in B for x in r):
        raise TypeError("matrix entries must be Python ints")
    for i in range(4):
        if B[i][i] != 0:
            raise ValueError("diagonal must vanish")
        for j in range(4):
            if B[i][j] != -B[j][i]:
                raise ValueError("matrix must be skew-symmetric")
    return tuple(B[i - 1][j - 1] for i, j in PAIRS)


def mutate(q, k):
    check_quiver(q)
    _check_vertex(k)
    B = matrix(q)
    kk = k - 1
    N = [[0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            if i == kk or j == kk:
                N[i][j] = -B[i][j]
            else:
                bik, bkj = B[i][kk], B[kk][j]
                N[i][j] = B[i][j] + max(bik, 0) * max(bkj, 0) - max(-bik, 0) * max(-bkj, 0)
    return from_matrix(N)


def parse_word(w):
    """Accept (1,2,3), [1,2,3], '1,2,3' or '123' and return a tuple of ints."""
    if isinstance(w, str):
        w = w.replace(" ", "")
        parts = w.split(",") if "," in w else list(w)
        w = tuple(int(x) for x in parts if x)
    w = tuple(w)
    for k in w:
        _check_vertex(k)
    return w


def mutate_word(q, w):
    for k in parse_word(w):
        q = mutate(q, k)
    return q


def path(q, w):
    """[q, mu_{k1} q, mu_{k1 k2} q, ...]."""
    out = [check_quiver(q)]
    for k in parse_word(w):
        out.append(mutate(out[-1], k))
    return out


def _check_perm(pi):
    if tuple(sorted(pi)) != VERTICES:
        raise ValueError("a relabeling is a permutation of (1,2,3,4), got %r" % (pi,))
    return tuple(pi)


def relabel(q, pi):
    check_quiver(q)
    pi = _check_perm(pi)
    return tuple(entry(q, pi[i - 1], pi[j - 1]) for i, j in PAIRS)


def inverse_perm(pi):
    pi = _check_perm(pi)
    inv = [0] * 4
    for i, p in enumerate(pi, start=1):
        inv[p - 1] = i
    return tuple(inv)


def reverse(q):
    """Reverse every arrow."""
    return tuple(-x for x in check_quiver(q))


def height(q):
    return max(abs(x) for x in check_quiver(q))


def pfaffian(q):
    a, b, c, d, e, f = check_quiver(q)
    return a * f - b * e + c * d


def canonical(q):
    """Lexicographically least relabeling (reversal of all arrows is NOT quotiented out)."""
    return min(relabel(q, pi) for pi in ALL_PERMUTATIONS)


# ------------------------------------------------------------------------- graph properties
def is_acyclic(q):
    B = matrix(q)
    left = set(range(4))
    while left:
        sources = [i for i in left if all(B[j][i] <= 0 for j in left)]
        if not sources:
            return False
        left.difference_update(sources)
    return True


def topological_order(q):
    """A topological ordering (tuple of vertices) of an acyclic quiver, else None."""
    B = matrix(q)
    left = set(range(4))
    order = []
    while left:
        src = sorted(i for i in left if all(B[j][i] <= 0 for j in left))
        if not src:
            return None
        order.append(src[0] + 1)
        left.remove(src[0])
    return tuple(order)


def components(q):
    B = matrix(q)
    seen, comps = set(), []
    for s in range(4):
        if s in seen:
            continue
        comp, stack = {s}, [s]
        while stack:
            u = stack.pop()
            for v in range(4):
                if B[u][v] != 0 and v not in comp:
                    comp.add(v)
                    stack.append(v)
        seen |= comp
        comps.append(tuple(sorted(v + 1 for v in comp)))
    return comps


def is_connected(q):
    return len(components(q)) == 1


def has_cyclic_full_triangle(q):
    """Proposition 2.1: an oriented triangle with multiplicities x,y,z >= 2 and
    x^2+y^2+z^2-xyz <= 4 is mutation-cyclic (Beineke-Bruestle-Hille)."""
    for i, j, k in combinations(VERTICES, 3):
        x, y, z = entry(q, i, j), entry(q, j, k), entry(q, k, i)
        if (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0):
            x, y, z = abs(x), abs(y), abs(z)
            if min(x, y, z) >= 2 and x * x + y * y + z * z - x * y * z <= 4:
                return True
    return False


def is_vortex(q):
    """Complete quiver = oriented triangle plus a source or sink (Fomin-Neville)."""
    check_quiver(q)
    if any(x == 0 for x in q):
        return False
    for k in VERTICES:
        others = [v for v in VERTICES if v != k]
        out_all = all(entry(q, k, v) > 0 for v in others)
        in_all = all(entry(q, k, v) < 0 for v in others)
        if out_all or in_all:
            i, j, l = others
            x, y, z = entry(q, i, j), entry(q, j, l), entry(q, l, i)
            if (x > 0 and y > 0 and z > 0) or (x < 0 and y < 0 and z < 0):
                return True
    return False


# ------------------------------------------------------------------------- cyclic orderings
def normalize_cyclic(order):
    order = tuple(order)
    if tuple(sorted(order)) != VERTICES:
        raise ValueError("a cyclic ordering lists each vertex once")
    i = order.index(1)
    return order[i:] + order[:i]


ALL_CYCLIC_ORDERS = tuple(sorted({normalize_cyclic(p) for p in ALL_PERMUTATIONS}))  # six


def markov(q, order):
    """Fomin-Neville Markov invariant for the linear order order[0]<...<order[3]
    (formula (4) of the paper); invariant under rotation of the order."""
    v = tuple(order)
    if tuple(sorted(v)) != VERTICES:
        raise ValueError("order must list each vertex once")
    a, b, c = entry(q, v[0], v[1]), entry(q, v[0], v[2]), entry(q, v[0], v[3])
    d, e = entry(q, v[1], v[2]), entry(q, v[1], v[3])
    f = entry(q, v[2], v[3])
    return (a * a + b * b + c * c + d * d + e * e + f * f
            + a * b * d + a * c * e + b * c * f + d * e * f + a * c * d * f)


def vertex_is_proper(q, order, k):
    """Every two-path i -> k -> j meets i, k, j in clockwise order."""
    pos = {x: n for n, x in enumerate(order)}
    for i in VERTICES:
        if i != k and entry(q, i, k) > 0:
            for j in VERTICES:
                if j != k and j != i and entry(q, k, j) > 0:
                    if not ((pos[k] - pos[i]) % 4 < (pos[j] - pos[i]) % 4):
                        return False
    return True


def wiggle_classes(q):
    """Partition of the six cyclic orderings into wiggle classes (swap neighbours not joined)."""
    remaining = set(ALL_CYCLIC_ORDERS)
    classes = []
    while remaining:
        start = min(remaining)
        remaining.discard(start)
        comp, stack = {start}, [start]
        while stack:
            o = list(stack.pop())
            for i in range(4):
                j = (i + 1) % 4
                if entry(q, o[i], o[j]) == 0:
                    o2 = o[:]
                    o2[i], o2[j] = o2[j], o2[i]
                    c = normalize_cyclic(o2)
                    if c not in comp:
                        comp.add(c)
                        remaining.discard(c)
                        stack.append(c)
        classes.append(tuple(sorted(comp)))
    return sorted(classes)


def proper_classes(q):
    """Wiggle classes in which every vertex is proper in some member."""
    out = []
    for cl in wiggle_classes(q):
        if all(any(vertex_is_proper(q, o, k) for o in cl) for k in VERTICES):
            out.append(cl)
    return out


def class_markov(q, cl):
    vals = {markov(q, o) for o in cl}
    if len(vals) != 1:
        raise AssertionError("Markov value not constant on a wiggle class: %r %r" % (q, cl))
    return vals.pop()


def proper_values(q):
    return [class_markov(q, cl) for cl in proper_classes(q)]


# ------------------------------------------------------------------------- bounds and search
def H_paper(q):
    """The bound of an earlier version of the paper: max(ht, max |M| over all six orders).
    Not used by the decision procedure, which uses search_bound."""
    return max([height(q)] + [abs(markov(q, o)) for o in ALL_CYCLIC_ORDERS])


def search_bound(q):
    """The bound H(Q) of equation (13): max(ht(Q), max of M over the proper wiggle classes).
    Returns None when Q has no proper wiggle class (then Q is a vortex, hence mutation-cyclic)."""
    vals = proper_values(q)
    if not vals:
        return None
    return max([height(q)] + vals)


def bounded_search(q, bound, max_states=None):
    """Breadth-first search of the component of q among quivers of height <= bound.
    Returns ("acyclic", word) when an acyclic quiver is found, ("exhausted", n_states)
    when the whole component was searched, or ("aborted", n_states)."""
    check_quiver(q)
    if type(bound) is not int:
        raise TypeError("bound must be an int")
    if height(q) > bound:
        raise ValueError("start quiver exceeds the bound")
    pred = {q: None}
    dq = deque([q])
    while dq:
        r = dq.popleft()
        if is_acyclic(r):
            word = []
            x = r
            while pred[x] is not None:
                x, k = pred[x]
                word.append(k)
            return ("acyclic", tuple(reversed(word)))
        for k in VERTICES:
            s = mutate(r, k)
            if s not in pred and height(s) <= bound:
                pred[s] = (r, k)
                dq.append(s)
                if max_states is not None and len(pred) > max_states:
                    return ("aborted", len(pred))
    return ("exhausted", len(pred))


def endpoint_signatures(max_m):
    """All pairs (M, p^2) of connected acyclic quivers read in a topological ordering with
    M <= max_m (all six entries nonnegative). Uses that M is nondecreasing in each entry."""
    if type(max_m) is not int or max_m < 0:
        raise ValueError("max_m must be a nonnegative int")
    out = set()
    import math
    top = math.isqrt(max_m)

    def rec(prefix):
        if len(prefix) == 6:
            t = tuple(prefix)
            if is_connected(t):
                out.add((markov(t, (1, 2, 3, 4)), pfaffian(t) ** 2))
            return
        for x in range(top + 1):
            t = tuple(prefix + [x] + [0] * (5 - len(prefix)))
            if markov(t, (1, 2, 3, 4)) > max_m:
                break
            rec(prefix + [x])

    rec([])
    return out


def markov_excluded(q, signatures, max_m):
    """Lemma 2.6 test: connected, has a proper class, and no proper class has a signature
    (M, p^2) realized by a connected acyclic quiver. `signatures` must contain every
    signature with M <= max_m; a class whose M exceeds max_m makes the test inconclusive."""
    if not is_connected(q):
        return False
    classes = proper_classes(q)
    if not classes:
        return False
    p2 = pfaffian(q) ** 2
    for cl in classes:
        m = class_markov(q, cl)
        if m < 3 or 4 * p2 >= m * m:      # Lemma 2.4: connected acyclic endpoints have m>=3, 2|p|<m
            continue
        if m > max_m:
            return False                  # inconclusive, so do not claim exclusion
        if (m, p2) in signatures:
            return False
    return True


def decide(q, max_states=None):
    """Decision procedure of Corollary 5.2 with the sharper bound of Theorem 5.1.
    Returns ("acyclic", word), ("cyclic", reason) or ("aborted", n)."""
    check_quiver(q)
    if is_acyclic(q):
        return ("acyclic", ())
    comps = components(q)
    if len(comps) > 1:
        # disconnected: some component has at most three vertices; rank-three criterion
        if has_cyclic_full_triangle(q):
            return ("cyclic", "mutation-cyclic full triangle")
    B = search_bound(q)
    if B is None:
        return ("cyclic", "no proper wiggle class (vortex)")
    res = bounded_search(q, B, max_states)
    if res[0] == "acyclic":
        return res
    if res[0] == "exhausted":
        return ("cyclic", "component within height %d exhausted (%d quivers)" % (B, res[1]))
    return res
