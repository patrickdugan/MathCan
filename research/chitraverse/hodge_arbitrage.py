"""CHTR-02: exact weighted Hodge certificates for *reversible* edge quotes.

All calculations use fractions.Fraction.  An edge (u,v) carries an additive,
possibly signed log-quote q_e; traversing it backwards has quote -q_e.
This mathematical model is separate from one-way, fee-bearing market orders.
"""
from collections import deque
from dataclasses import dataclass
from fractions import Fraction


def _r(x):
    return x if isinstance(x, Fraction) else Fraction(x)


def _validate(n, edges, quotes, weights):
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be positive")
    if len(edges) != len(quotes) or len(edges) != len(weights):
        raise ValueError("each edge needs a quote and positive weight")
    for e in edges:
        if (len(e) != 2 or not all(isinstance(x, int) for x in e)
                or not all(0 <= x < n for x in e) or e[0] == e[1]):
            raise ValueError("edges must connect distinct valid vertices")
    if any(w <= 0 for w in weights):
        raise ValueError("positive weights are required")


def _tree_cycles(n, edges):
    """Produce tree edges and full-rank fundamental circulation rows.

    A chord u->v contributes +1 on itself and follows the tree from v to u.
    Parallel edges are supported. An unconnected graph is rejected.
    """
    parent = list(range(n))
    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x
    tree = []
    chords = []
    for i, (u, v) in enumerate(edges):
        a, b = root(u), root(v)
        if a == b:
            chords.append(i)
        else:
            parent[a] = b
            tree.append(i)
    if len(tree) != n - 1:
        raise ValueError("the undirected edge support must be connected")
    adjacent = [[] for _ in range(n)]
    for i in tree:
        u, v = edges[i]
        adjacent[u].append((v, i, 1))
        adjacent[v].append((u, i, -1))
    cycles = []
    for chord in chords:
        start, goal = edges[chord][1], edges[chord][0]
        queue = deque([start])
        seen = {start}
        routes = {}
        while queue and goal not in seen:
            u = queue.popleft()
            for v, i, direction in adjacent[u]:
                if v not in seen:
                    seen.add(v)
                    routes[v] = (u, i, direction)
                    queue.append(v)
        row = [0] * len(edges)
        row[chord] = 1
        p = goal
        while p != start:
            prev, i, direction = routes[p]
            row[i] = direction
            p = prev
        cycles.append(tuple(row))
    return tree, tuple(cycles)


def _solve_exact(matrix, rhs):
    """Gauss-Jordan over Q, rejecting inconsistent or singular systems."""
    n = len(rhs)
    if not n:
        return ()
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("square matrix required")
    rows = [[_r(x) for x in row] + [_r(rhs[i])] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if rows[r][col]), None)
        if pivot is None:
            raise ValueError("singular cycle Gram matrix")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [v / scale for v in rows[col]]
        for r in range(n):
            if r == col:
                continue
            factor = rows[r][col]
            if factor:
                rows[r] = [a - factor * b for a, b in zip(rows[r], rows[col])]
    return tuple(row[-1] for row in rows)


@dataclass(frozen=True)
class HodgeCertificate:
    node_potentials: tuple
    gradient: tuple
    residual: tuple
    energy: Fraction
    cycle_basis: tuple
    holonomies: tuple
    cycle_gram: tuple
    dual_multipliers: tuple


def hodge_certificate(n, edges, quotes, weights):
    """Construct the unique weighted residual and root-gauge potential.

    E* = (C q)^T (C W^-1 C^T)^-1 (C q).
    Result obeys q = gradient + residual, B^T W residual = 0,
    and C gradient = 0. No floating-point linear algebra is used.
    """
    edges = tuple(tuple(e) for e in edges)
    q = tuple(_r(x) for x in quotes)
    w = tuple(_r(x) for x in weights)
    _validate(n, edges, q, w)
    tree, cycles = _tree_cycles(n, edges)
    hol = tuple(sum((c[i] * q[i] for i in range(len(edges))), Fraction(0))
                for c in cycles)
    gram = tuple(tuple(sum((Fraction(c[i] * d[i], 1) / w[i]
                            for i in range(len(edges))), Fraction(0))
                       for d in cycles) for c in cycles)
    dual = _solve_exact(gram, hol)
    residual = tuple(sum((cycles[k][i] * dual[k]
                          for k in range(len(cycles))), Fraction(0)) / w[i]
                     for i in range(len(edges)))
    gradient = tuple(q[i] - residual[i] for i in range(len(edges)))
    adj = [[] for _ in range(n)]
    for i in tree:
        u, v = edges[i]
        adj[u].append((v, gradient[i]))
        adj[v].append((u, -gradient[i]))
    pot = [None] * n
    pot[0] = Fraction(0)
    todo = [0]
    while todo:
        u = todo.pop()
        for v, diff in adj[u]:
            if pot[v] is None:
                pot[v] = pot[u] + diff
                todo.append(v)
    if any(x is None for x in pot):
        raise AssertionError("broken spanning tree")
    if any(pot[v] - pot[u] != gradient[i]
           for i, (u, v) in enumerate(edges)):
        raise AssertionError("cycle dual failed to reconstruct gradient")
    energy = sum((w[i] * residual[i] ** 2
                  for i in range(len(edges))), Fraction(0))
    from_dual = sum((dual[k] * hol[k] for k in range(len(cycles))), Fraction(0))
    if energy != from_dual:
        raise AssertionError("energy fails exact duality")
    # The weighted residual is orthogonal to every vertex gradient.
    weighted_div = [Fraction(0) for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        weighted_div[u] -= w[i] * residual[i]
        weighted_div[v] += w[i] * residual[i]
    if any(weighted_div):
        raise AssertionError("weighted residual is not divergence-free")
    return HodgeCertificate(tuple(pot), gradient, residual, energy,
                            cycles, hol, gram, dual)


def signed_cycle_bound(n, edges, quotes, weights, cycle):
    """Exact lower bound on minimum weighted energy from any circulation.

    The vector must be a nonzero oriented circulation: B^T cycle = 0.
    Returns (cycle dot q)^2 / (cycle^T W^-1 cycle).
    """
    edges = tuple(tuple(x) for x in edges)
    q = tuple(_r(x) for x in quotes)
    w = tuple(_r(x) for x in weights)
    c = tuple(_r(x) for x in cycle)
    _validate(n, edges, q, w)
    if len(c) != len(edges) or all(x == 0 for x in c):
        raise ValueError("nonzero circulation with one value per edge required")
    divergence = [Fraction(0) for _ in range(n)]
    for (u, v), value in zip(edges, c):
        divergence[u] -= value
        divergence[v] += value
    if any(divergence):
        raise ValueError("cycle vector is not a circulation")
    hol = sum((a * b for a, b in zip(c, q)), Fraction(0))
    denom = sum((a * a / z for a, z in zip(c, w)), Fraction(0))
    return hol * hol / denom


def robust_nonzero_obstruction(energy, weights, errors):
    """Safe exact claim: any true q within |observed_e-true_e|<=error_e
    has nonzero cycle obstruction when E(observed) > sum(w_e*error_e^2).
    A False result is intentionally inconclusive.
    """
    e = _r(energy)
    w = tuple(_r(x) for x in weights)
    delta = tuple(_r(x) for x in errors)
    if e < 0 or len(w) != len(delta) or any(x <= 0 for x in w) or any(x < 0 for x in delta):
        raise ValueError("nonnegative energy, positive weights and error bars required")
    return e > sum((wi * di * di for wi, di in zip(w, delta)), Fraction(0))


def robust_cycle_energy_lower_bound(n, edges, quotes, weights, errors, cycle):
    """Certified E(true) lower bound for rectangular additive quote uncertainty.

    For a fixed nonzero circulation c and |true_e-observed_e|<=errors_e:
      E(true) >= max(0, |c.q|-sum_e |c_e|*errors_e)^2
                 / sum_e c_e^2/weights_e.
    On a connected unicyclic graph whose c spans its cycle space this is the
    exact minimum over all allowed true quote assignments.
    """
    q = tuple(_r(x) for x in quotes)
    w = tuple(_r(x) for x in weights)
    delta = tuple(_r(x) for x in errors)
    c = tuple(_r(x) for x in cycle)
    if len(delta) != len(q) or any(x < 0 for x in delta):
        raise ValueError("nonnegative error bars with one per quote required")
    # Reuse exact circulation checking and nonzero denominator.
    signed_cycle_bound(n, edges, q, w, c)
    hol = abs(sum((a * b for a, b in zip(c, q)), Fraction(0)))
    margin = max(Fraction(0), hol - sum((abs(a) * d
                                       for a, d in zip(c, delta)), Fraction(0)))
    denominator = sum((a*a/z for a, z in zip(c, w)), Fraction(0))
    return margin * margin / denominator