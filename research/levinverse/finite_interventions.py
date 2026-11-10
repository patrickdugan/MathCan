"""Finite action-relative observational quotients and exact stochastic checks.

Small, auditable synthetic systems only; no inference about biological systems.
Uses the Python standard library and exact Fraction arithmetic.
"""
from collections import deque
from fractions import Fraction


def _labels(signatures):
    distinct = {}
    out = []
    for signature in signatures:
        if signature not in distinct:
            distinct[signature] = len(distinct)
        out.append(distinct[signature])
    return tuple(out)


def refine_partition(states, actions, step, observe):
    """Return stable class labels and number of strict partition refinements.

    `step[(state, action)]` and `observe[state]` must be total; states must be
    distinct and all signatures must be hashable. Iteration order only changes
    numerical class labels, never the equivalence relation.
    """
    states, actions = tuple(states), tuple(actions)
    if len(set(states)) != len(states):
        raise ValueError("states must be distinct")
    state_set = set(states)
    if any(step[(s, a)] not in state_set for s in states for a in actions):
        raise ValueError("every action must map into the declared state set")
    ix = {s: i for i, s in enumerate(states)}
    labels = _labels(tuple(observe[s] for s in states))
    initial_blocks = len(set(labels))
    refinements = 0
    while True:
        newer = _labels((labels[i], tuple(labels[ix[step[(s, a)]]] for a in actions))
                        for i, s in enumerate(states))
        if newer == labels:
            return labels, refinements
        refinements += 1
        if refinements > len(states) - initial_blocks:
            raise AssertionError("strict-refinement bound violated")
        labels = newer


def shortest_distinguishing_word(s, t, actions, step, observe):
    """Return a shortest action word distinguishing two states, or None."""
    queue = deque([(s, t, ())])
    seen = {(s, t)}
    while queue:
        x, y, word = queue.popleft()
        if observe[x] != observe[y]:
            return word
        for action in actions:
            x1, y1 = step[(x, action)], step[(y, action)]
            if (x1, y1) not in seen:
                seen.add((x1, y1))
                queue.append((x1, y1, word + (action,)))
    return None


def total_variation(p, q):
    """Total variation of two finite probability measures (exact Fractions)."""
    return sum((abs(p.get(x, 0) - q.get(x, 0)) for x in p.keys() | q.keys()),
               Fraction(0)) / 2


def pushforward(row, quotient):
    out = {}
    for state, probability in row.items():
        y = quotient[state]
        out[y] = out.get(y, Fraction(0)) + probability
    return out


def uniform_one_step_defect(micro, macro, quotient, actions):
    """Supremum TV distance of micro pushforwards vs declared macro rows."""
    return max((total_variation(pushforward(micro[(s, a)], quotient),
                                macro[(quotient[s], a)])
                for s in quotient for a in actions), default=Fraction(0))


def observation_history_law(initial, transitions, quotient, policy, horizon):
    """Exact law of observed histories for a deterministic history policy.

    `transitions[(state, action)]` maps next states to probability masses.
    The initial observation is included in each history tuple.
    """
    distribution = {(initial, (quotient[initial],)): Fraction(1)}
    for _ in range(horizon):
        following = {}
        for (state, history), mass in distribution.items():
            action = policy(history)
            for next_state, probability in transitions[(state, action)].items():
                key = (next_state, history + (quotient[next_state],))
                following[key] = following.get(key, Fraction(0)) + mass * probability
        distribution = following
    result = {}
    for (_, history), mass in distribution.items():
        result[history] = result.get(history, Fraction(0)) + mass
    return result


def micro_macro_history_error(initial_micro, micro, macro, quotient, policy, horizon):
    observed = observation_history_law(initial_micro, micro, quotient, policy, horizon)
    ys = set(quotient.values())
    identity = {y: y for y in ys}
    approximate = observation_history_law(quotient[initial_micro], macro,
                                          identity, policy, horizon)
    return total_variation(observed, approximate)


def coupling_bound(epsilon, horizon):
    epsilon = Fraction(epsilon)
    if not 0 <= epsilon <= 1 or horizon < 0:
        raise ValueError("epsilon must lie in [0,1], horizon must be nonnegative")
    return 1 - (1 - epsilon) ** horizon
