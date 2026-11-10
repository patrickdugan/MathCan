"""CHTR-03: exact finite-state exchange automata and path-ordered hook gains.

The rate multipliers are a deliberately simplified, quantity-independent model.
No chain interaction, AMM reserve curve, or executable arbitrage is implied.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence

from .cycle_potentials import multiplicative_potential, profitable_cycle


@dataclass(frozen=True)
class Hook:
    name: str
    source: int
    target: int
    next_state: tuple[int, ...]
    rate: tuple[Q, ...]

    def __post_init__(self):
        object.__setattr__(self, 'next_state', tuple(self.next_state))
        object.__setattr__(self, 'rate', tuple(Q(r) for r in self.rate))


@dataclass(frozen=True)
class CycleWitness:
    start: tuple[int, int]
    hooks: tuple[int, ...]
    trace: tuple[tuple[int, int], ...]
    gain: Q


def validate(assets: int, states: int, hooks: Sequence[Hook]) -> tuple[Hook, ...]:
    if type(assets) is not int or type(states) is not int or assets < 1 or states < 1:
        raise ValueError('assets and states must be positive integers')
    hooks = tuple(hooks)
    if len({h.name for h in hooks}) != len(hooks):
        raise ValueError('hook names must be unique')
    for h in hooks:
        if not (0 <= h.source < assets and 0 <= h.target < assets):
            raise ValueError('invalid asset index')
        if len(h.rate) != states or len(h.next_state) != states:
            raise ValueError('rate and transition tables must cover all states')
        if any(r <= 0 for r in h.rate):
            raise ValueError('all conversion rates must be positive')
        if any(type(s) is not int or s < 0 or s >= states for s in h.next_state):
            raise ValueError('invalid hook successor state')
    return hooks


def index(asset: int, state: int, states: int) -> int:
    return asset * states + state


def state_node(node: int, states: int) -> tuple[int, int]:
    return divmod(node, states)


def lifted_edges(assets: int, states: int, hooks: Sequence[Hook], *, upper=None):
    """Ordered by hook index, then source state; edge ids carry both indices."""
    hooks = validate(assets, states, hooks)
    if upper is not None and len(upper) != len(hooks):
        raise ValueError('upper bounds must cover each hook')
    edges = []
    for i, h in enumerate(hooks):
        values = h.rate if upper is None else upper[i]
        if len(values) != states or any(Q(x) <= 0 for x in values):
            raise ValueError('invalid bound table')
        for s in range(states):
            edges.append((index(h.source, s, states),
                          index(h.target, h.next_state[s], states), Q(values[s])))
    return tuple(edges)


def potential(assets: int, states: int, hooks: Sequence[Hook]):
    """Return a positive potential satisfying p[target] >= rate * p[source].

    Its existence excludes profitable market-state-closed cycles.
    A feasible positive vector proves every closed market-state cycle gain <=1.
    """
    return multiplicative_potential(assets * states, lifted_edges(assets, states, hooks))


def verify_potential(assets: int, states: int, hooks: Sequence[Hook], witness) -> bool:
    if witness is None or len(witness) != assets * states or any(Q(v) <= 0 for v in witness):
        return False
    return all(Q(witness[v]) >= r * Q(witness[u])
               for u, v, r in lifted_edges(assets, states, hooks))


def execute(assets: int, states: int, hooks: Sequence[Hook],
            start: tuple[int, int], route: Sequence[int]):
    hooks = validate(assets, states, hooks)
    a, s = start
    if not (0 <= a < assets and 0 <= s < states):
        raise ValueError('invalid initial asset/state')
    gain = Q(1)
    trace = [(a, s)]
    for i in route:
        if type(i) is not int or i < 0 or i >= len(hooks):
            raise ValueError('invalid hook index')
        h = hooks[i]
        if h.source != a:
            raise ValueError('hook asset mismatch')
        gain *= h.rate[s]
        a, s = h.target, h.next_state[s]
        trace.append((a, s))
    return (a, s), gain, tuple(trace)


def profitable_closed_cycle(assets: int, states: int, hooks: Sequence[Hook]):
    edges = lifted_edges(assets, states, hooks)
    edge_indices = profitable_cycle(assets * states, edges)
    if edge_indices is None:
        return None
    u0 = edges[edge_indices[0]][0]
    start = state_node(u0, states)
    route = tuple(i // states for i in edge_indices)
    end, gain, trace = execute(assets, states, hooks, start, route)
    assert end == start and gain > 1  # Independent witness reconstruction
    return CycleWitness(start, route, trace, gain)


def snapshot_potentials(assets: int, states: int, hooks: Sequence[Hook]):
    hooks = validate(assets, states, hooks)
    return tuple(multiplicative_potential(
        assets, tuple((h.source, h.target, h.rate[s]) for h in hooks))
        for s in range(states))


def best_gain_by_horizon(assets: int, states: int, hooks: Sequence[Hook],
                         start: tuple[int, int], horizon: int):
    """Exact best multiplicative value for each reachable (asset,state), <=horizon trades.

    Keeps an attaining hook word. This is finite-horizon dynamic programming,
    and does not require a no-profitable-cycle assumption.
    """
    hooks = validate(assets, states, hooks)
    if type(horizon) is not int or horizon < 0:
        raise ValueError('nonnegative integer horizon required')
    if not (0 <= start[0] < assets and 0 <= start[1] < states):
        raise ValueError('invalid start')
    best = {start: (Q(1), ())}
    for _ in range(horizon):
        next_best = best.copy()
        for (a, s), (gain, route) in best.items():
            for i, h in enumerate(hooks):
                if h.source != a:
                    continue
                dest = (h.target, h.next_state[s])
                new = gain * h.rate[s]
                if dest not in next_best or new > next_best[dest][0]:
                    next_best[dest] = (new, route + (i,))
        best = next_best
    return best


def gauge_rates(assets: int, states: int, hooks: Sequence[Hook],
                gauge: Sequence[Q]) -> tuple[Hook, ...]:
    """Gauge r' = r * g(source) / g(target); closed-route gains are preserved."""
    hooks = validate(assets, states, hooks)
    if len(gauge) != assets * states or any(Q(x) <= 0 for x in gauge):
        raise ValueError('positive gauge required at every (asset,state)')
    return tuple(Hook(h.name, h.source, h.target, h.next_state,
                      tuple(h.rate[s] * Q(gauge[index(h.source, s, states)]) /
                            Q(gauge[index(h.target, h.next_state[s], states)])
                            for s in range(states))) for h in hooks)


def commuting_order_ratio(assets: int, states: int, hooks: Sequence[Hook],
                          a: int, b: int, initial: tuple[int, int]):
    """Gain(a;b) / Gain(b;a) for two words with the SAME terminal node.

    The endpoint condition is essential: otherwise the ratio changes gauge.
    """
    end_ab, gain_ab, _ = execute(assets, states, hooks, initial, (a, b))
    end_ba, gain_ba, _ = execute(assets, states, hooks, initial, (b, a))
    if end_ab != end_ba:
        raise ValueError('orders end at different asset/state nodes')
    return gain_ab / gain_ba


def interval_certificate(assets: int, states: int, hooks: Sequence[Hook],
                         lower: Sequence[Sequence[Q]],
                         upper: Sequence[Sequence[Q]]):
    """Sound no-positive-cycle / fixed-profitable-cycle / unresolved certificates.

    Exact transition tables are shared by every admissible rate assignment.
    The upper-rate witness is sufficient even for correlated rate uncertainties.
    """
    hooks = validate(assets, states, hooks)
    if len(lower) != len(hooks) or len(upper) != len(hooks):
        raise ValueError('need one rate interval per hook-state pair')
    low_hooks, high_hooks = [], []
    for i, h in enumerate(hooks):
        if len(lower[i]) != states or len(upper[i]) != states:
            raise ValueError('wrong rate table size')
        lo, hi = tuple(Q(x) for x in lower[i]), tuple(Q(x) for x in upper[i])
        if any(not (0 < lo[s] <= hi[s]) for s in range(states)):
            raise ValueError('invalid rate interval')
        low_hooks.append(Hook(h.name, h.source, h.target, h.next_state, lo))
        high_hooks.append(Hook(h.name, h.source, h.target, h.next_state, hi))
    p = potential(assets, states, high_hooks)
    if p is not None:
        return ('robust_no_cycle', p)
    cyc = profitable_closed_cycle(assets, states, low_hooks)
    if cyc is not None:
        return ('guaranteed_closed_cycle', cyc)
    return ('unresolved', None)


def quotient_upper_certificate(assets: int, states: int, hooks: Sequence[Hook],
                               state_class: Sequence[int]):
    """Sound conservative quotient only when transitions respect state classes.

    Uses maximum rates in each source class. Failure can be spurious.
    Returns (potential on abstract states, concrete lifted potential) or None.
    """
    hooks = validate(assets, states, hooks)
    if len(state_class) != states or any(type(c) is not int or c < 0 for c in state_class):
        raise ValueError('nonnegative class ids required')
    labels = sorted(set(state_class))
    canonical = {c: i for i, c in enumerate(labels)}
    alpha = tuple(canonical[c] for c in state_class)
    q = len(labels)
    abstractions = []
    for h in hooks:
        next_class, rate_class = [], []
        for c in range(q):
            fibre = [s for s in range(states) if alpha[s] == c]
            successors = {alpha[h.next_state[s]] for s in fibre}
            if len(successors) != 1:
                raise ValueError('state partition is not stable under all hook transitions')
            next_class.append(next(iter(successors)))
            rate_class.append(max(h.rate[s] for s in fibre))
        abstractions.append(Hook(h.name, h.source, h.target,
                                 tuple(next_class), tuple(rate_class)))
    p = potential(assets, q, abstractions)
    if p is None:
        return None
    concrete_p = tuple(p[index(a, alpha[s], q)]
                       for a in range(assets) for s in range(states))
    assert verify_potential(assets, states, hooks, concrete_p)
    return p, concrete_p
