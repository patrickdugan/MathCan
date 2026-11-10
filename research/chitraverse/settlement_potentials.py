"""CHTR-05: exact atomic multi-account settlement and rational pool-value bounds.

Invented digital two-asset ledger with explicitly registered transfers, fee-only
constant-product trades, adversarial pool-mutating callbacks, and settlement-time
funding/credit rules. No EVM execution semantics, oracle authentication, or
permissionless security is claimed. Standard-library Fraction arithmetic only.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Optional

from .amount_aware_hooks import Wallet, rational, lower_sqrt_rational, wallet_value

ASSETS = ("A", "B")


def _amount(value, *, strictly_positive=False):
    v = rational(value)
    if v < 0 or (strictly_positive and v == 0):
        raise ValueError("amount must be positive" if strictly_positive else "amount must be nonnegative")
    return v


@dataclass(frozen=True)
class LedgerState:
    """Complete in-scope ledger, with account roles fixed by the certificate.

    Account naming has no magic meaning. It is the caller's responsibility to
    declare disjoint exhaustive roles for a bound. Pool ids have nonnegative
    holdings at rest; a swap requires both reserves to be strictly positive.
    """
    accounts: tuple[tuple[str, Wallet], ...]
    pools: tuple[str, ...]
    phase: int = 0

    def __post_init__(self):
        names = [name for name, _ in self.accounts]
        if not names or len(names) != len(set(names)) or any(not isinstance(n, str) or not n for n in names):
            raise ValueError("accounts require unique nonempty names")
        if not all(isinstance(w, Wallet) for _, w in self.accounts):
            raise ValueError("account balances must be Wallet instances")
        if not self.pools or len(self.pools) != len(set(self.pools)) or any(n not in names for n in self.pools):
            raise ValueError("pool roles require distinct present accounts")
        if not isinstance(self.phase, int) or self.phase < 0:
            raise ValueError("phase must be nonnegative integer")

    def wallet(self, name):
        for key, wallet in self.accounts:
            if key == name:
                return wallet
        raise ValueError(f"unregistered account: {name}")

    @property
    def names(self):
        return frozenset(name for name, _ in self.accounts)

    def totals(self):
        return Wallet(sum((w.a for _, w in self.accounts), Fraction(0)),
                      sum((w.b for _, w in self.accounts), Fraction(0)))


@dataclass(frozen=True)
class Transfer:
    source: str
    destination: str
    asset: str
    amount: Fraction

    def __post_init__(self):
        if not self.source or not self.destination or self.source == self.destination:
            raise ValueError("transfers need distinct nonempty accounts")
        if self.asset not in ASSETS:
            raise ValueError("unknown asset")
        object.__setattr__(self, "amount", _amount(self.amount, strictly_positive=True))


@dataclass(frozen=True)
class BalanceGuard:
    account: str
    asset: str
    minimum: Fraction

    def __post_init__(self):
        if self.asset not in ASSETS:
            raise ValueError("unknown guard asset")
        object.__setattr__(self, "minimum", _amount(self.minimum))


@dataclass(frozen=True)
class Swap:
    pool: str
    direction: str
    amount: Fraction | str
    gamma: Fraction = Fraction(1)

    def __post_init__(self):
        if self.direction not in ("A2B", "B2A"):
            raise ValueError("swap direction must be A2B or B2A")
        if self.amount != "all":
            object.__setattr__(self, "amount", _amount(self.amount, strictly_positive=True))
        gamma = rational(self.gamma)
        if not 0 < gamma <= 1:
            raise ValueError("fee multiplier must lie in (0,1]")
        object.__setattr__(self, "gamma", gamma)


@dataclass(frozen=True)
class SettlementRule:
    """Atomic callback whose pre/swap/post order is explicitly fixed."""
    key: str
    phase: int
    next_phase: int
    before: tuple[Transfer, ...] = ()
    swap: Optional[Swap] = None
    after: tuple[Transfer, ...] = ()
    guards: tuple[BalanceGuard, ...] = ()
    pool_floors: tuple[tuple[str, Fraction], ...] = ()

    def __post_init__(self):
        if not self.key or not isinstance(self.phase, int) or self.phase < 0 or not isinstance(self.next_phase, int) or self.next_phase < 0:
            raise ValueError("invalid action key or phase")
        if any(not isinstance(t, Transfer) for t in self.before + self.after):
            raise ValueError("bad transfer")
        if any(not isinstance(g, BalanceGuard) for g in self.guards):
            raise ValueError("bad guard")
        if self.swap is not None and not isinstance(self.swap, Swap):
            raise ValueError("bad swap")
        floors = []
        for name, value in self.pool_floors:
            floors.append((name, _amount(value)))
        if len({name for name, _ in floors}) != len(floors):
            raise ValueError("duplicate pool floor")
        object.__setattr__(self, "pool_floors", tuple(floors))


@dataclass(frozen=True)
class SettlementProgram:
    rules: tuple[SettlementRule, ...]
    # Caps on the magnitude of *intermediate* negative balances. All final
    # balances must be nonnegative, and the overdraft disappears at settlement.
    credit_limits: tuple[tuple[str, str, Fraction], ...] = ()

    def __post_init__(self):
        if not self.rules or any(not isinstance(r, SettlementRule) for r in self.rules):
            raise ValueError("nonempty registered action program required")
        if len({(r.phase, r.key) for r in self.rules}) != len(self.rules):
            raise ValueError("duplicate action and phase")
        cleaned = []
        for name, asset, limit in self.credit_limits:
            if asset not in ASSETS:
                raise ValueError("invalid credit asset")
            cleaned.append((name, asset, _amount(limit)))
        if len({(name, asset) for name, asset, _ in cleaned}) != len(cleaned):
            raise ValueError("duplicate credit authorization")
        object.__setattr__(self, "credit_limits", tuple(cleaned))

    def rule(self, phase, key):
        for rule in self.rules:
            if rule.phase == phase and rule.key == key:
                return rule
        raise ValueError("unregistered action for current phase")


@dataclass(frozen=True)
class SettlementReceipt:
    key: str
    phase_before: int
    phase_after: int
    transfers: tuple[Transfer, ...]
    swap_output: Optional[Fraction]
    # Maximum transient debt reached by each account and asset.
    exposures: tuple[tuple[str, str, Fraction], ...]
    totals_before: Wallet
    totals_after: Wallet
    products_before: tuple[tuple[str, Fraction], ...]
    products_after: tuple[tuple[str, Fraction], ...]


def settle(state: LedgerState, program: SettlementProgram, key: str):
    """Apply registered callback atomically, checking solvency and all claims.

    Intrastep debt is a *typed* abstract overdraft, with account-and-asset caps.
    Intermediate negatives in other accounts are rejected; pool balances must
    remain positive at the instant of an invariant-based swap. On any exception,
    the original immutable state is unchanged. Receipt records actual flows.
    """
    if not isinstance(state, LedgerState) or not isinstance(program, SettlementProgram):
        raise TypeError("state and program required")
    rule = program.rule(state.phase, key)
    accounts = {name: [w.a, w.b] for name, w in state.accounts}
    credit = {(name, asset): limit for name, asset, limit in program.credit_limits}
    for name, asset in credit:
        if name not in accounts or name in state.pools:
            raise ValueError("credit must target an existing nonpool account")
    for g in rule.guards:
        if g.account not in accounts:
            raise ValueError("guard references unknown account")
        if accounts[g.account][ASSETS.index(g.asset)] < g.minimum:
            raise ValueError("guard condition failed")
    minima = {(name, asset): Fraction(0) for name in accounts for asset in ASSETS}
    observed = []

    def move(t):
        if t.source not in accounts or t.destination not in accounts:
            raise ValueError("unregistered transfer endpoint")
        j = ASSETS.index(t.asset)
        accounts[t.source][j] -= t.amount
        accounts[t.destination][j] += t.amount
        for name in (t.source, t.destination):
            value = accounts[name][j]
            minima[name, t.asset] = min(minima[name, t.asset], value)
            if value < -credit.get((name, t.asset), Fraction(0)):
                raise ValueError("temporary balance exceeds authorized credit")
        observed.append(t)

    pre_products = tuple((pool, state.wallet(pool).a * state.wallet(pool).b) for pool in state.pools)
    for t in rule.before:
        move(t)
    out = None
    if rule.swap is not None:
        swap = rule.swap
        if swap.pool not in state.pools or "trader" not in accounts:
            raise ValueError("swap needs a pool and registered trader")
        src = "A" if swap.direction == "A2B" else "B"
        dst = "B" if src == "A" else "A"
        i, j = ASSETS.index(src), ASSETS.index(dst)
        x = accounts["trader"][i] if swap.amount == "all" else swap.amount
        if x <= 0:
            raise ValueError("swap input must be positive")
        reserve_in, reserve_out = accounts[swap.pool][i], accounts[swap.pool][j]
        if reserve_in <= 0 or reserve_out <= 0:
            raise ValueError("swap needs strictly positive reserves")
        out = reserve_out * swap.gamma * x / (reserve_in + swap.gamma * x)
        move(Transfer("trader", swap.pool, src, x))
        move(Transfer(swap.pool, "trader", dst, out))
    for t in rule.after:
        move(t)

    # All debts must be settled before atomic commit, even if intrastep cap
    # permitted temporarily negative trader or hook balances.
    for balances in accounts.values():
        if balances[0] < 0 or balances[1] < 0:
            raise ValueError("unsettled account deficit")
    for name, limit in rule.pool_floors:
        if name not in state.pools:
            raise ValueError("unregistered pool floor")
        if accounts[name][0] * accounts[name][1] < limit:
            raise ValueError("pool reserve product breached registered floor")
    result = LedgerState(tuple((name, Wallet(*accounts[name])) for name, _ in state.accounts),
                         state.pools, rule.next_phase)
    if state.totals() != result.totals():
        raise AssertionError("token conservation failure")
    receipt = SettlementReceipt(rule.key, state.phase, result.phase, tuple(observed), out,
                                tuple((name, asset, -minimum) for (name, asset), minimum in sorted(minima.items())
                                      if minimum < 0),
                                state.totals(), result.totals(), pre_products,
                                tuple((name, result.wallet(name).a * result.wallet(name).b) for name in state.pools))
    return result, receipt


def settle_route(state, program, actions):
    receipts = []
    for key in actions:
        state, receipt = settle(state, program, key)
        receipts.append(receipt)
    return state, tuple(receipts)


@dataclass(frozen=True)
class AccountRoles:
    trader: str
    custodians: tuple[str, ...]
    sponsors: tuple[str, ...]

    def validate(self, state: LedgerState):
        parts = (self.trader,) + self.custodians + self.sponsors + state.pools
        if len(set(parts)) != len(parts) or frozenset(parts) != state.names:
            raise ValueError("roles must be disjoint and exhaustive")


def _total_value(state, names, prices):
    return sum((wallet_value(state.wallet(name), prices) for name in names), Fraction(0))


def extraction_certificate(initial: LedgerState, final: LedgerState,
                           roles: AccountRoles, prices=(1, 1), denominator=10**6,
                           ex_ante_pool_floors=None):
    """Exact rational *upper* budget despite arbitrary reserve-mutating hooks.

    For each pool: pa*x+pb*y >= 2 sqrt(pa*pb*x*y) >= 2 L_i, where
    L_i=floor_Q(sqrt(pa*pb*x*y)). All quantities here are exact rationals.
    The certificate's slack is the exact nonnegative difference U - gain.
    Every nonpool account must belong to exactly one declared budget category.
    """
    if not isinstance(roles, AccountRoles):
        raise TypeError("roles required")
    roles.validate(initial)
    roles.validate(final)
    if initial.names != final.names:
        raise ValueError("account registry changed")
    if initial.pools != final.pools:
        raise ValueError("pool registry changed")
    if initial.totals() != final.totals():
        raise ValueError("token accounting differs")
    prices = tuple(rational(p) for p in prices)
    if len(prices) != 2 or min(prices) <= 0:
        raise ValueError("positive two-asset marking prices required")
    if not isinstance(denominator, int) or denominator <= 0:
        raise ValueError("positive approximation denominator required")
    gain = wallet_value(final.wallet(roles.trader), prices) - wallet_value(initial.wallet(roles.trader), prices)
    custodian_draw = _total_value(initial, roles.custodians, prices)-_total_value(final, roles.custodians, prices)
    sponsor_draw = _total_value(initial, roles.sponsors, prices)-_total_value(final, roles.sponsors, prices)
    pool_value_loss = _total_value(initial, initial.pools, prices)-_total_value(final, initial.pools, prices)
    if gain != custodian_draw+sponsor_draw+pool_value_loss:
        raise AssertionError("complete ledger accounting mismatch")
    detail = []
    upper_pool_release = Fraction(0)
    final_pool_slack = Fraction(0)
    for name in initial.pools:
        before = initial.wallet(name)
        after = final.wallet(name)
        x = prices[0] * prices[1] * after.a * after.b
        root_floor = lower_sqrt_rational(x, denominator)
        init_value = wallet_value(before, prices)
        last_value = wallet_value(after, prices)
        slack = last_value - 2 * root_floor
        if slack < 0:
            raise AssertionError("rational AM-GM failed")
        release = init_value - 2 * root_floor
        upper_pool_release += release
        final_pool_slack += slack
        detail.append((name, before.a * before.b, after.a * after.b,
                       root_floor, release, slack))
    upper = custodian_draw + sponsor_draw + upper_pool_release
    if upper - gain != final_pool_slack or upper < gain:
        raise AssertionError("rational extraction certificate failed")
    result = {
        "trader_gain": gain,
        "custodian_drawdown": custodian_draw,
        "external_sponsor_drawdown": sponsor_draw,
        "pool_value_loss": pool_value_loss,
        "pool_release_upper": upper_pool_release,
        "gain_upper_bound": upper,
        "certificate_gap": final_pool_slack,
        "pool_details": tuple(detail),
    }
    if ex_ante_pool_floors is not None:
        if set(ex_ante_pool_floors) != set(initial.pools):
            raise ValueError("pool floors must cover every pool")
        floor_release = Fraction(0)
        for name in initial.pools:
            floor_k = _amount(ex_ante_pool_floors[name])
            final_pool = final.wallet(name)
            if final_pool.a * final_pool.b < floor_k:
                raise ValueError("final reserve product below claimed floor")
            floor_release += wallet_value(initial.wallet(name), prices) - 2 * lower_sqrt_rational(prices[0]*prices[1]*floor_k, denominator)
        ex_ante = custodian_draw + sponsor_draw + floor_release
        if gain > ex_ante:
            raise AssertionError("registered floor certificate failed")
        result["floor_based_gain_bound"] = ex_ante
    return result


def verify_witness(state, program, actions, roles, prices=(1,1), denominator=10**6,
                   ex_ante_pool_floors=None):
    """Replay a registered route, returning the exact certificate and receipts."""
    final, receipts = settle_route(state, program, actions)
    cert = extraction_certificate(state, final, roles, prices, denominator,
                                  ex_ante_pool_floors)
    return final, cert, receipts


@dataclass(frozen=True)
class FinitePotentialAudit:
    certified: bool
    state_count: int
    transition_count: int
    # One concrete violated local inequality when certified=False.
    violating_edge: Optional[tuple[LedgerState, str, LedgerState]] = None


def audit_finite_superpotential(domain, program, roles, prices, potential,
                                 charges=None):
    """Check every enabled rule edge of a *closed finite* settlement-state set.

    A success is a complete finite-graph certificate only for the supplied
    closed domain and the registered action program. New reachable states
    invalidate that certification. Missing successors fail closed.
    """
    states = tuple(domain)
    if len(set(states)) != len(states) or not states:
        raise ValueError("finite domain must be nonempty and duplicate free")
    present = set(states)
    if set(potential) != present:
        raise ValueError("potential table must cover the exact closed domain")
    if not isinstance(program, SettlementProgram) or not isinstance(roles, AccountRoles):
        raise TypeError("registered program and role partition required")
    charges = {} if charges is None else charges
    if set(charges) - {(rule.phase, rule.key) for rule in program.rules}:
        raise ValueError("charge references unknown program rule")
    prices = tuple(rational(x) for x in prices)
    if len(prices) != 2 or min(prices) <= 0:
        raise ValueError("positive prices required")
    for state in states:
        roles.validate(state)
    values = {state: rational(potential[state]) for state in states}
    transition_count = 0
    disabled_reasons = ("temporary balance exceeds authorized credit",
                        "unsettled account deficit", "guard condition failed",
                        "pool reserve product breached registered floor",
                        "swap input must be positive")
    for state in states:
        for rule in program.rules:
            if rule.phase != state.phase:
                continue
            try:
                successor, _ = settle(state, program, rule.key)
            except ValueError as e:
                if str(e) in disabled_reasons:
                    continue
                raise
            if successor not in present:
                raise ValueError("finite domain is not closed under enabled actions")
            transition_count += 1
            gain = wallet_value(successor.wallet(roles.trader), prices) - wallet_value(state.wallet(roles.trader), prices)
            charge = rational(charges.get((rule.phase, rule.key), 0))
            if gain > values[state] - values[successor] + charge:
                return FinitePotentialAudit(False, len(states), transition_count,
                                            (state, rule.key, successor))
    return FinitePotentialAudit(True, len(states), transition_count)
