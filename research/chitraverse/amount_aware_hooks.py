"""CHTR-04: exact-rational shared-state multi-pool trades and funded hooks.

An immutable, two-asset accounting model. Tokens are moved among trader, fee-only
constant-product pools, and a prefunded hook account. A deterministic hook rule
selects the fee for a pool/direction/phase, a balance transfer after the swap,
and the next shared phase. Neither callbacks nor swaps mint tokens.

Every positive amount is represented exactly by fractions.Fraction. No notion
of gas, precision/rounding, atomic onchain EVM execution, oracle reads, or MEV
is represented; these are deliberately finite mathematical examples.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Optional
from functools import lru_cache


def rational(value):
    if isinstance(value, float):
        raise TypeError("use an exact rational, not float")
    return Fraction(value)


def _positive(value, label):
    out = rational(value)
    if out <= 0:
        raise ValueError(f"{label} must be positive")
    return out


def _nonnegative(value, label):
    out = rational(value)
    if out < 0:
        raise ValueError(f"{label} must be nonnegative")
    return out


@dataclass(frozen=True)
class Wallet:
    a: Fraction
    b: Fraction

    def __post_init__(self):
        object.__setattr__(self, "a", _nonnegative(self.a, "A balance"))
        object.__setattr__(self, "b", _nonnegative(self.b, "B balance"))

    def at(self, asset):
        if asset == "A":
            return self.a
        if asset == "B":
            return self.b
        raise ValueError("asset must be A or B")

    def changed(self, asset, amount):
        amount = rational(amount)
        return Wallet(self.a + (amount if asset == "A" else 0),
                      self.b + (amount if asset == "B" else 0)) if asset in ("A", "B") else self._invalid_asset()

    @staticmethod
    def _invalid_asset():
        raise ValueError("asset must be A or B")


def wallet_value(wallet, prices):
    pa, pb = map(rational, prices)
    if pa <= 0 or pb <= 0:
        raise ValueError("numeraire prices must be positive")
    return pa * wallet.a + pb * wallet.b


@dataclass(frozen=True)
class Pool:
    a: Fraction
    b: Fraction

    def __post_init__(self):
        object.__setattr__(self, "a", _positive(self.a, "A reserve"))
        object.__setattr__(self, "b", _positive(self.b, "B reserve"))

    @property
    def k(self):
        return self.a * self.b


@dataclass(frozen=True)
class HookRule:
    """Pay `payment` units of `asset` from hook to trader after the swap.

    A negative payment charges trader to fund the hook. The rule is supplied
    by the protocol, not selected by the simulated trader at execution time.
    """
    gamma: Fraction
    next_phase: int
    asset: Optional[str] = None
    payment: Fraction = Fraction(0)

    def __post_init__(self):
        gamma = rational(self.gamma)
        payment = rational(self.payment)
        if not (0 < gamma <= 1):
            raise ValueError("fee multiplier must lie in (0,1]")
        if not isinstance(self.next_phase, int) or self.next_phase < 0:
            raise ValueError("invalid next phase")
        if self.asset is None and payment != 0:
            raise ValueError("nonzero payment needs an asset")
        if self.asset is not None and self.asset not in ("A", "B"):
            raise ValueError("invalid hook asset")
        object.__setattr__(self, "gamma", gamma)
        object.__setattr__(self, "payment", payment)


@dataclass(frozen=True)
class HookProgram:
    """rules[phase][pool_index][direction] with direction 0=A->B, 1=B->A."""
    rules: tuple

    def __post_init__(self):
        if not self.rules:
            raise ValueError("hook program must have a phase")
        pool_count = len(self.rules[0])
        if pool_count == 0:
            raise ValueError("hook program must have a pool")
        for phase in self.rules:
            if len(phase) != pool_count:
                raise ValueError("every phase must have the same pools")
            for directions in phase:
                if len(directions) != 2 or not all(isinstance(x, HookRule) for x in directions):
                    raise ValueError("each pool must have two HookRules")
                if any(x.next_phase >= len(self.rules) for x in directions):
                    raise ValueError("next phase outside program")

    @property
    def pool_count(self):
        return len(self.rules[0])

    def rule(self, phase, pool, direction):
        return self.rules[phase][pool][0 if direction == "A2B" else 1]


@dataclass(frozen=True)
class Market:
    pools: tuple
    trader: Wallet
    hook: Wallet
    phase: int = 0

    def __post_init__(self):
        if len(self.pools) < 1 or not all(isinstance(p, Pool) for p in self.pools):
            raise ValueError("at least one valid pool required")
        if not isinstance(self.trader, Wallet) or not isinstance(self.hook, Wallet):
            raise ValueError("wallets required")
        if not isinstance(self.phase, int) or self.phase < 0:
            raise ValueError("invalid phase")


@dataclass(frozen=True)
class Trade:
    pool: int
    direction: str
    amount: Fraction | str

    def __post_init__(self):
        if not isinstance(self.pool, int) or self.pool < 0:
            raise ValueError("pool must be a nonnegative index")
        if self.direction not in ("A2B", "B2A"):
            raise ValueError("unknown direction")
        if self.amount != "all":
            object.__setattr__(self, "amount", _positive(self.amount, "input"))


@dataclass(frozen=True)
class Receipt:
    trade: Trade
    phase_before: int
    phase_after: int
    gamma: Fraction
    input_amount: Fraction
    output: Fraction
    reserve_k_before: Fraction
    reserve_k_after: Fraction
    hook_transfer: Fraction
    hook_asset: Optional[str]


def _totals(market):
    return Wallet(market.trader.a + market.hook.a + sum((p.a for p in market.pools), Fraction(0)),
                  market.trader.b + market.hook.b + sum((p.b for p in market.pools), Fraction(0)))


def execute(market, trade, program):
    """Atomic exact execution with reserve accounting and a funded hook callback."""
    if not isinstance(market, Market) or not isinstance(trade, Trade) or not isinstance(program, HookProgram):
        raise TypeError("Market, Trade, HookProgram required")
    if program.pool_count != len(market.pools) or market.phase >= len(program.rules):
        raise ValueError("market/program mismatch")
    if trade.pool >= len(market.pools):
        raise ValueError("missing pool")
    direction = trade.direction
    supplied = "A" if direction == "A2B" else "B"
    received = "B" if direction == "A2B" else "A"
    amount = market.trader.at(supplied) if trade.amount == "all" else trade.amount
    if amount <= 0 or market.trader.at(supplied) < amount:
        raise ValueError("insufficient trader input")
    rule = program.rule(market.phase, trade.pool, direction)
    old = market.pools[trade.pool]
    effective = rule.gamma * amount
    if direction == "A2B":
        output = old.b * effective / (old.a + effective)
        new_pool = Pool(old.a + amount, old.b - output)
    else:
        output = old.a * effective / (old.b + effective)
        new_pool = Pool(old.a - output, old.b + amount)
    trader = market.trader.changed(supplied, -amount).changed(received, output)
    hook = market.hook
    if rule.payment:
        # Sign convention: positive means paid out of the prefunded hook account.
        trader = trader.changed(rule.asset, rule.payment)
        hook = hook.changed(rule.asset, -rule.payment)
    pools = list(market.pools)
    pools[trade.pool] = new_pool
    final = Market(tuple(pools), trader, hook, rule.next_phase)
    assert _totals(final) == _totals(market), "token conservation violated"
    assert new_pool.k >= old.k, "fee-only constant-product invariant decreased"
    receipt = Receipt(trade, market.phase, final.phase, rule.gamma, amount, output,
                      old.k, new_pool.k, rule.payment, rule.asset)
    return final, receipt


def execute_route(market, trades, program):
    state = market
    receipts = []
    for trade in trades:
        state, receipt = execute(state, trade, program)
        receipts.append(receipt)
    return state, tuple(receipts)


def baseline_gap(initial, final, prices):
    """Return exact wealth decomposition under common initial marginal prices.

    A pool with baseline X0,Y0 is at equilibrium under prices (pa,pb) exactly
    when pa*X0=pb*Y0. All pool products must be nondecreasing. The returned
    identity follows from token conservation; it is path- and order-independent.
    """
    if len(initial.pools) != len(final.pools):
        raise ValueError("pool count differs")
    if _totals(initial) != _totals(final):
        raise ValueError("token accounting differs")
    pa, pb = map(rational, prices)
    if pa <= 0 or pb <= 0:
        raise ValueError("prices must be positive")
    displacement = Fraction(0)
    invariant_growth = Fraction(0)
    for original, last in zip(initial.pools, final.pools):
        v = pa * original.a
        if v != pb * original.b:
            raise ValueError("pool not initially balanced at shared numeraire")
        if last.k < original.k:
            raise ValueError("the pool invariant decreased")
        displacement += v * (last.a-original.a)**2 / (original.a*last.a)
        invariant_growth += v * (last.k-original.k) / (last.a*original.b)
    trader_gain = wallet_value(final.trader, (pa,pb))-wallet_value(initial.trader, (pa,pb))
    hook_drawdown = wallet_value(initial.hook, (pa,pb))-wallet_value(final.hook, (pa,pb))
    assert trader_gain == hook_drawdown - displacement - invariant_growth
    assert displacement >= 0 and invariant_growth >= 0
    return {
        "trader_gain": trader_gain,
        "hook_drawdown": hook_drawdown,
        "displacement_gap": displacement,
        "invariant_growth_gap": invariant_growth,
        "profit_upper_bound": hook_drawdown,
    }


def protocol(rules_by_phase):
    """Build a HookProgram from nested iterables, preserving a fixed rule table."""
    return HookProgram(tuple(tuple(tuple(direction_rules) for direction_rules in phase)
                             for phase in rules_by_phase))


def constant_program(pool_count, gamma=Fraction(1), phases=1, toggle=False):
    gamma = rational(gamma)
    rules = []
    for i in range(phases):
        next_phase = (i + 1) % phases if toggle else i
        rules.append(tuple((HookRule(gamma, next_phase), HookRule(gamma, next_phase))
                           for _ in range(pool_count)))
    return HookProgram(tuple(rules))


@dataclass(frozen=True)
class OptimalPlan:
    final_value: Fraction
    route: tuple
    final_state: Market
    explored_states: int


def optimal_route(initial, program, choices, max_steps, prices=(1,1),
                  terminal=None, max_states=20000):
    """Exact optimum on a finite specified action menu and a bounded horizon.

    Terminal is a predicate on market states. ``all`` inputs are resolved at
    execution time. Returned path is replayed before returning. Search considers
    stopping early, with a deterministic tie break in menu order.
    """
    if max_steps < 0 or max_states <= 0:
        raise ValueError("invalid search bound")
    choices = tuple(choices)
    if not all(isinstance(x, Trade) for x in choices):
        raise TypeError("choices must be Trade actions")
    if terminal is None:
        terminal = lambda _: True
    visits = [0]

    @lru_cache(maxsize=None)
    def solve(state, remaining):
        visits[0] += 1
        if visits[0] > max_states:
            raise RuntimeError("search reached the registered state cap")
        best = (wallet_value(state.trader, prices), ()) if terminal(state) else None
        if remaining:
            for action in choices:
                try:
                    successor, _ = execute(state, action, program)
                except ValueError:
                    continue
                candidate = solve(successor, remaining - 1)
                if candidate is not None and (best is None or candidate[0] > best[0]):
                    best = (candidate[0], (action,) + candidate[1])
        return best

    best = solve(initial, max_steps)
    if best is None:
        raise ValueError("no terminal state reachable within horizon")
    final, _ = execute_route(initial, best[1], program)
    assert wallet_value(final.trader, prices) == best[0] and terminal(final)
    return OptimalPlan(best[0], best[1], final, visits[0])


def lower_sqrt_rational(x, denominator=10**6):
    """Certified rational lower approximation to sqrt(x), using integer isqrt."""
    from math import isqrt
    x = _nonnegative(x, "radicand")
    if not isinstance(denominator, int) or denominator <= 0:
        raise ValueError("denominator must be positive integer")
    scaled_floor = (x.numerator * denominator * denominator) // x.denominator
    n = isqrt(scaled_floor)
    ans = Fraction(n, denominator)
    assert ans * ans <= x
    assert (ans + Fraction(1, denominator))**2 > x
    return ans


def general_budget(initial, final, prices, denominator=10**6):
    """Non-equilibrium universal bound from AM-GM, with rational sqrt floors.

    The bound holds for any amount-aware trade ordering and funded callbacks,
    provided the modeled token totals are conserved and each pool's product
    does not decrease. It may be loose when pool equilibria disagree.
    """
    if len(initial.pools) != len(final.pools):
        raise ValueError("pool count mismatch")
    if _totals(initial) != _totals(final):
        raise ValueError("token conservation fails")
    pa, pb = map(rational, prices)
    if pa <= 0 or pb <= 0:
        raise ValueError("prices must be positive")
    surplus = Fraction(0)
    for before, after in zip(initial.pools, final.pools):
        if after.k < before.k:
            raise ValueError("pool invariant decreased")
        lower = lower_sqrt_rational(pa * pb * before.k, denominator)
        surplus += pa * before.a + pb * before.b - 2 * lower
    hook_drawdown = wallet_value(initial.hook, (pa,pb)) - wallet_value(final.hook, (pa,pb))
    trader_gain = wallet_value(final.trader, (pa,pb)) - wallet_value(initial.trader, (pa,pb))
    assert trader_gain <= hook_drawdown + surplus
    return {
        "trader_gain": trader_gain,
        "hook_drawdown": hook_drawdown,
        "initial_mispricing_surplus_upper": surplus,
        "trader_gain_upper": hook_drawdown + surplus,
    }
