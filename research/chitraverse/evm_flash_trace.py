"""CHTR-06: small, exact, Uniswap-v4-inspired flash-accounting trace verifier.

This is a trace-level *abstract machine*, NOT an EVM emulator or a proof about
PoolManager bytecode. Currency transfers must be fully enumerated, authenticated
caller frames must come from a trusted execution trace, and pool changes must
be matched to deployed hook/manager code separately.

Supported: integer ERC20-like balances, pool allocations, signed per-caller
currency deltas, ERC6909-like redeemable claims, sync/settle/take/clear,
custom pool deltas, fee-only floor-rounded CPMM swaps, nested frame reverts,
external account transfers and exact terminal budget receipts.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from json import dumps, loads
from typing import Any

from .amount_aware_hooks import lower_sqrt_rational

UINT256 = 2**256 - 1
INT128 = 2**127 - 1
INT256 = 2**255 - 1


class TraceRejected(ValueError):
    """Fail-closed model violation, which reverts the entire outer replay."""


def uint(x: Any, *, bound: int = UINT256) -> int:
    if type(x) is not int or not 0 <= x <= bound:
        raise TraceRejected(f"expected an unsigned integer <= {bound}")
    return x


def sint(x: Any, *, bound: int = INT128) -> int:
    if type(x) is not int or not -bound <= x <= bound:
        raise TraceRejected("signed amount out of declared int128 range")
    return x


def positive_price(x: Any) -> Fraction:
    try:
        v = Fraction(x)
    except (TypeError, ValueError, ZeroDivisionError) as e:
        raise TraceRejected("invalid marking price") from e
    if v <= 0:
        raise TraceRejected("marking price must be positive")
    return v


def _canonical(v):
    if isinstance(v, dict):
        return {str(k): _canonical(z) for k, z in sorted(v.items())}
    if isinstance(v, tuple):
        return [_canonical(z) for z in v]
    if isinstance(v, list):
        return [_canonical(z) for z in v]
    return v


def digest(v) -> str:
    return sha256(dumps(_canonical(v), sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class FlashLedger:
    """Two-asset, whole-token vault and virtual pool balance model."""

    def __init__(self, physical: dict, pools: dict, *, vault="manager", claims=None,
                 surplus=None, trader="trader", prices=(1, 1)):
        self.physical = deepcopy(physical)
        self.pools = deepcopy(pools)
        self.claims = deepcopy(claims or {})
        self.deltas: dict[str, dict[str, int]] = {}
        self.vault = vault
        self.trader = trader
        self.assets = ("A", "B")
        self.prices = tuple(positive_price(x) for x in prices)
        self.sync: tuple[str, int] | None = None
        self.surplus = deepcopy(surplus) if surplus is not None else {}
        if len(self.prices) != 2:
            raise TraceRejected("two asset prices required")
        if not self.physical or vault not in self.physical or trader not in self.physical:
            raise TraceRejected("vault and trader must have physical accounts")
        if not self.pools:
            raise TraceRejected("at least one pool required")
        for group in (self.physical, self.pools, self.claims):
            for key, holdings in group.items():
                if not isinstance(key, str) or not key or type(holdings) is not dict:
                    raise TraceRejected("invalid account or pool map")
                if set(holdings) != set(self.assets):
                    raise TraceRejected("all balances require A and B fields")
                for amount in holdings.values():
                    uint(amount)
        for name in self.claims:
            if name not in self.physical or name == self.vault:
                raise TraceRejected("unknown claim owner")
        if surplus is None:
            self.surplus = {a: self.physical[vault][a] -
                            sum(p[a] for p in self.pools.values()) -
                            sum(c[a] for c in self.claims.values())
                            for a in self.assets}
        if set(self.surplus) != set(self.assets):
            raise TraceRejected("surplus needs both asset keys")
        for a in self.assets:
            uint(self.surplus[a])
        self.initial_totals = self.physical_totals()
        self.initial = self.snapshot()
        self.check()

    def snapshot(self):
        return {k: deepcopy(getattr(self, k)) for k in
                ("physical", "pools", "claims", "deltas", "surplus", "sync")}

    def restore(self, snapshot):
        for k, v in snapshot.items():
            setattr(self, k, deepcopy(v))

    def physical_totals(self):
        return {a: sum(w[a] for w in self.physical.values()) for a in self.assets}

    def backing_gap(self):
        """Zero iff vault = allocated pools + ERC6909 claims + deltas + surplus."""
        return {a: self.physical[self.vault][a]
                - sum(w[a] for w in self.pools.values())
                - sum(w[a] for w in self.claims.values())
                - sum(d.get(a, 0) for d in self.deltas.values())
                - self.surplus[a] for a in self.assets}

    def check(self):
        if self.physical_totals() != self.initial_totals:
            raise TraceRejected("unaccounted ERC20 mint, burn or external account")
        for w in list(self.physical.values()) + list(self.pools.values()) + list(self.claims.values()):
            for a in self.assets:
                uint(w[a])
        for d in self.deltas.values():
            for v in d.values():
                if type(v) is not int or abs(v) > INT256:
                    raise TraceRejected("signed transient delta overflow")
        if any(self.backing_gap().values()):
            raise TraceRejected("vault backing identity failed")

    def _asset(self, asset):
        if asset not in self.assets:
            raise TraceRejected("unsupported asset")

    def _delta(self, owner, asset, amount):
        if owner == self.vault or owner not in self.physical:
            raise TraceRejected("unregistered or vault delta owner")
        self._asset(asset)
        sint(amount)
        d = self.deltas.setdefault(owner, {})
        next_value = d.get(asset, 0) + amount
        if abs(next_value) > INT256:
            raise TraceRejected("transient delta overflow")
        d[asset] = next_value

    def _balance(self, group, name, asset, change):
        self._asset(asset)
        if name not in group:
            raise TraceRejected("unregistered balance holder")
        value = group[name][asset] + change
        uint(value)
        group[name][asset] = value

    def _transfer(self, source, target, asset, amount, *, surplus_effect=True):
        uint(amount, bound=INT128)
        if source == target or not source or not target:
            raise TraceRejected("transfer needs distinct accounts")
        self._balance(self.physical, source, asset, -amount)
        self._balance(self.physical, target, asset, amount)
        if surplus_effect:
            self.surplus[asset] += (amount if target == self.vault else 0)
            self.surplus[asset] -= (amount if source == self.vault else 0)

    def raw_transfer(self, source, target, asset, amount):
        self._transfer(source, target, asset, amount)

    def tax_transfer(self, source, target, tax_receiver, asset, gross, tax):
        uint(gross, bound=INT128)
        uint(tax, bound=INT128)
        if tax > gross or len({source, target, tax_receiver}) != 3:
            raise TraceRejected("invalid tax transfer")
        # Explicitly two conserved physical transfers. Tax cannot vanish.
        self._transfer(source, target, asset, gross - tax)
        self._transfer(source, tax_receiver, asset, tax)

    def allocate(self, pool, owner, asset, quantity):
        sint(quantity)
        if pool not in self.pools:
            raise TraceRejected("unregistered pool")
        self._balance(self.pools, pool, asset, quantity)
        self._delta(owner, asset, -quantity)

    def move_pool(self, source, target, asset, amount):
        uint(amount, bound=INT128)
        if source == target or source not in self.pools or target not in self.pools:
            raise TraceRejected("unknown or identical pools")
        self._balance(self.pools, source, asset, -amount)
        self._balance(self.pools, target, asset, amount)

    def swap(self, pool, owner, input_asset, amount, fee_num, fee_den):
        uint(amount, bound=INT128)
        uint(fee_num)
        uint(fee_den)
        if amount == 0 or fee_num == 0 or fee_num > fee_den or pool not in self.pools:
            raise TraceRejected("invalid CPMM swap")
        self._asset(input_asset)
        output_asset = "B" if input_asset == "A" else "A"
        inp = self.pools[pool][input_asset]
        out_reserve = self.pools[pool][output_asset]
        if inp == 0 or out_reserve == 0:
            raise TraceRejected("empty pool")
        # Explicit integer floor, matching a declared fee-only CPMM formula.
        output = (out_reserve * fee_num * amount) // (inp * fee_den + fee_num * amount)
        if output == 0 or output >= out_reserve or output > INT128:
            raise TraceRejected("zero/overflow output")
        self.allocate(pool, owner, input_asset, amount)
        self.allocate(pool, owner, output_asset, -output)
        return output

    def sync_currency(self, asset):
        self._asset(asset)
        self.sync = (asset, self.physical[self.vault][asset])

    def settle(self, recipient):
        if self.sync is None:
            raise TraceRejected("settle requires a sync")
        asset, before = self.sync
        paid = self.physical[self.vault][asset] - before
        if paid < 0 or paid > INT128:
            raise TraceRejected("negative or overflowing synced balance change")
        self.surplus[asset] -= paid
        self._delta(recipient, asset, paid)
        self.sync = None
        return paid

    def take(self, caller, recipient, asset, amount):
        uint(amount, bound=INT128)
        if recipient == self.vault:
            raise TraceRejected("self-directed take excluded from abstraction")
        self._transfer(self.vault, recipient, asset, amount, surplus_effect=False)
        self._delta(caller, asset, -amount)

    def mint_claim(self, caller, recipient, asset, amount):
        uint(amount, bound=INT128)
        if recipient not in self.physical or recipient == self.vault:
            raise TraceRejected("bad claim recipient")
        self._asset(asset)
        if recipient not in self.claims:
            self.claims[recipient] = {"A": 0, "B": 0}
        self._balance(self.claims, recipient, asset, amount)
        self._delta(caller, asset, -amount)

    def transfer_claim(self, caller, recipient, asset, amount):
        uint(amount, bound=INT128)
        if caller == recipient or recipient not in self.physical or recipient == self.vault:
            raise TraceRejected("unregistered or identical claim transferee")
        self._asset(asset)
        self._balance(self.claims, caller, asset, -amount)
        if recipient not in self.claims:
            self.claims[recipient] = {"A": 0, "B": 0}
        self._balance(self.claims, recipient, asset, amount)

    def burn_claim(self, caller, asset, amount):
        uint(amount, bound=INT128)
        # Caller-as-owner only. Third-party ERC6909 allowance remains out of scope.
        self._balance(self.claims, caller, asset, -amount)
        self._delta(caller, asset, amount)

    def clear(self, caller, asset, amount):
        uint(amount, bound=INT128)
        self._asset(asset)
        if amount <= 0 or self.deltas.get(caller, {}).get(asset, 0) != amount:
            raise TraceRejected("clear must match entire positive delta")
        self._delta(caller, asset, -amount)
        self.surplus[asset] += amount

    def check_lock(self):
        self.check()
        if any(d.get(a, 0) for d in self.deltas.values() for a in self.assets):
            raise TraceRejected("unlock ends with nonzero currency deltas")
        if any(v < 0 for v in self.surplus.values()):
            raise TraceRejected("manager vault is underbacked at lock")

    def value(self, holdings) -> Fraction:
        return sum((self.prices[i] * holdings[a] for i, a in enumerate(self.assets)), Fraction(0))

    def _position(self, snapshot, account):
        physical = snapshot["physical"][account]
        claims = snapshot["claims"].get(account, {"A": 0, "B": 0})
        return self.value({a: physical[a] + claims[a] for a in self.assets})

    def receipt(self, *, denominator=10**6):
        """A *terminal* exact conservation and conservative reserve floor receipt."""
        self.check_lock()
        uint(denominator)
        if denominator == 0:
            raise TraceRejected("invalid root denominator")
        before = self.initial
        after = self.snapshot()
        others = [a for a in self.physical if a not in (self.vault, self.trader)]
        gain = self._position(after, self.trader) - self._position(before, self.trader)
        other_draw = sum((self._position(before, a) - self._position(after, a)
                          for a in others), Fraction(0))
        surplus_draw = self.value(before["surplus"]) - self.value(after["surplus"])
        initial_pool = sum((self.value(p) for p in before["pools"].values()), Fraction(0))
        final_pool = sum((self.value(p) for p in after["pools"].values()), Fraction(0))
        lower_values = {}
        for k, p in after["pools"].items():
            z = self.prices[0] * self.prices[1] * p["A"] * p["B"]
            root_floor = lower_sqrt_rational(z, denominator)
            lower_values[k] = 2 * root_floor
        floor_sum = sum(lower_values.values(), Fraction(0))
        upper = other_draw + surplus_draw + initial_pool - floor_sum
        if gain != other_draw + surplus_draw + initial_pool - final_pool:
            raise TraceRejected("terminal full-account wealth identity failed")
        if upper - gain != final_pool - floor_sum or upper < gain:
            raise TraceRejected("terminal budget check failed")
        return {
            "trader_gain": str(gain),
            "other_account_drawdown": str(other_draw),
            "vault_surplus_drawdown": str(surplus_draw),
            "initial_pool_value": str(initial_pool),
            "final_pool_value": str(final_pool),
            "pool_lower_values": {k: str(v) for k, v in sorted(lower_values.items())},
            "upper_extraction_bound": str(upper),
            "nonnegative_slack": str(upper - gain),
            "pool_root_denominator": denominator,
            "terminal_state_digest": digest(after),
            "conserved_physical_totals": self.physical_totals(),
            "remaining_transient_deltas": {k: dict(v) for k, v in self.deltas.items()},
            "terminal_vault_surplus": dict(self.surplus),
        }


@dataclass(frozen=True)
class ReplayResult:
    accepted: bool
    error: str | None
    failed_index: int | None
    event_hashes: tuple[str, ...]
    final: dict
    certificate: dict | None


class TraceReplay:
    """Replay declared frames and steps; all aborts return the initial state.

    An event's `actor` is checked against the current declared call frame.
    Authenticity of those frames requires an external, trusted EVM trace.
    """

    def __init__(self, ledger: FlashLedger, *, root="router"):
        if root not in ledger.physical or root == ledger.vault:
            raise TraceRejected("invalid unlock caller")
        self.ledger = ledger
        self.root = root
        self.frames = []
        self.active = False

    def _keys(self, event, required, allowed=()):
        if set(event) != set(required) and (set(event) - set(required) - set(allowed)
                                           or set(required) - set(event)):
            raise TraceRejected("missing or unknown trace event fields")

    def step(self, event):
        if type(event) is not dict or type(event.get("op")) is not str:
            raise TraceRejected("malformed trace step")
        op = event["op"]
        if op == "unlock":
            self._keys(event, ("op", "actor"))
            if self.active or event["actor"] != self.root:
                raise TraceRejected("unlock caller mismatch or already unlocked")
            self.frames = [(self.root, None)]
            self.active = True
            return
        if not self.active or not self.frames:
            raise TraceRejected("operation outside unlock callback")
        actor = self.frames[-1][0]
        if event.get("actor") != actor:
            raise TraceRejected("callback actor mismatches declared call frame")
        if op == "enter":
            self._keys(event, ("op", "actor", "callee"))
            if event["callee"] not in self.ledger.physical or event["callee"] == self.ledger.vault:
                raise TraceRejected("unregistered callback contract")
            self.frames.append((event["callee"], self.ledger.snapshot()))
            return
        if op in ("return", "revert"):
            self._keys(event, ("op", "actor"))
            if len(self.frames) <= 1:
                raise TraceRejected("unmatched nested call return")
            _, prior = self.frames.pop()
            if op == "revert":
                self.ledger.restore(prior)
            return
        if op == "assert_balance":
            self._keys(event, ("op", "actor", "account", "asset", "balance"))
            self.ledger._asset(event["asset"])
            uint(event["balance"])
            if (event["account"] not in self.ledger.physical or
                    self.ledger.physical[event["account"]][event["asset"]] != event["balance"]):
                raise TraceRejected("physical balance differs from supplied observation")
            return
        if op == "assert_delta":
            self._keys(event, ("op", "actor", "owner", "asset", "delta"))
            self.ledger._asset(event["asset"])
            if (type(event["delta"]) is not int or
                    self.ledger.deltas.get(event["owner"], {}).get(event["asset"], 0) != event["delta"]):
                raise TraceRejected("transient delta differs from supplied observation")
            return
        if op == "lock":
            self._keys(event, ("op", "actor"))
            if len(self.frames) != 1:
                raise TraceRejected("unlock left nested callback active")
            self.ledger.check_lock()
            self.active = False
            self.frames.clear()
            return
        methods = {
            "transfer": (("op", "actor", "source", "target", "asset", "amount"), self._transfer),
            "tax_transfer": (("op", "actor", "source", "target", "tax_receiver", "asset", "gross", "tax"), self._tax),
            "pool_delta": (("op", "actor", "pool", "asset", "quantity"), self._pool_delta),
            "pool_move": (("op", "actor", "source", "target", "asset", "amount"), self._pool_move),
            "swap": (("op", "actor", "pool", "input_asset", "amount", "fee_num", "fee_den"), self._swap),
            "sync": (("op", "actor", "asset"), self._sync),
            "settle": (("op", "actor"), self._settle),
            "settle_for": (("op", "actor", "recipient"), self._settle_for),
            "take": (("op", "actor", "recipient", "asset", "amount"), self._take),
            "mint": (("op", "actor", "recipient", "asset", "amount"), self._mint),
            "burn": (("op", "actor", "asset", "amount"), self._burn),
            "claim_transfer": (("op", "actor", "recipient", "asset", "amount"), self._claim_transfer),
            "clear": (("op", "actor", "asset", "amount"), self._clear),
        }
        if op not in methods:
            raise TraceRejected("unknown abstract opcode")
        required, handler = methods[op]
        self._keys(event, required)
        handler(event)
        self.ledger.check()

    def _transfer(self, x):
        self.ledger.raw_transfer(x["source"], x["target"], x["asset"], x["amount"])

    def _tax(self, x):
        self.ledger.tax_transfer(x["source"], x["target"], x["tax_receiver"], x["asset"], x["gross"], x["tax"])

    def _pool_delta(self, x):
        self.ledger.allocate(x["pool"], x["actor"], x["asset"], x["quantity"])

    def _pool_move(self, x):
        self.ledger.move_pool(x["source"], x["target"], x["asset"], x["amount"])

    def _swap(self, x):
        self.ledger.swap(x["pool"], x["actor"], x["input_asset"], x["amount"], x["fee_num"], x["fee_den"])

    def _sync(self, x):
        self.ledger.sync_currency(x["asset"])

    def _settle(self, x):
        self.ledger.settle(x["actor"])

    def _settle_for(self, x):
        self.ledger.settle(x["recipient"])

    def _take(self, x):
        self.ledger.take(x["actor"], x["recipient"], x["asset"], x["amount"])

    def _mint(self, x):
        self.ledger.mint_claim(x["actor"], x["recipient"], x["asset"], x["amount"])

    def _burn(self, x):
        self.ledger.burn_claim(x["actor"], x["asset"], x["amount"])

    def _claim_transfer(self, x):
        self.ledger.transfer_claim(x["actor"], x["recipient"], x["asset"], x["amount"])

    def _clear(self, x):
        self.ledger.clear(x["actor"], x["asset"], x["amount"])

    def replay(self, events, *, denominator=10**6):
        start = self.ledger.snapshot()
        traces = []
        try:
            if not isinstance(events, (list, tuple)) or not events:
                raise TraceRejected("empty event sequence")
            if self.active:
                raise TraceRejected("replay instance is already unlocked")
            for i, event in enumerate(events):
                self.step(event)
                self.ledger.check()
                traces.append(digest({"previous": traces[-1] if traces else "0" * 64,
                                      "event": event, "state": self.ledger.snapshot()}))
            if self.active:
                raise TraceRejected("missing final lock")
            return ReplayResult(True, None, None, tuple(traces), self.ledger.snapshot(),
                                self.ledger.receipt(denominator=denominator))
        except (TraceRejected, KeyError) as e:
            self.ledger.restore(start)
            self.active = False
            self.frames.clear()
            return ReplayResult(False, str(e), min(len(traces), len(events) - 1) if events else 0,
                                tuple(traces), self.ledger.snapshot(), None)


def from_json_spec(spec):
    """Construct exact machine from explicit balance snapshots (never an RPC lookup)."""
    if type(spec) is not dict or set(spec) != {"physical", "pools", "trader", "root", "prices", "events"}:
        raise TraceRejected("bad specification keys")
    ledger = FlashLedger(spec["physical"], spec["pools"], trader=spec["trader"],
                         prices=spec["prices"])
    return TraceReplay(ledger, root=spec["root"]).replay(spec["events"])


def main(argv=None):
    """Replay an explicitly declared, trusted-input JSON witness; no RPC calls."""
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description="CHTR-06 finite EVM-inspired trace accounting")
    parser.add_argument("spec", type=Path, help="JSON with complete declared ledger and events")
    parser.add_argument("--output", type=Path, help="optional JSON receipt destination")
    args = parser.parse_args(argv)
    try:
        outcome = from_json_spec(loads(args.spec.read_text(encoding="utf-8")))
        result = {"accepted": outcome.accepted, "error": outcome.error,
                  "failed_index": outcome.failed_index,
                  "event_hashes": list(outcome.event_hashes),
                  "certificate": outcome.certificate}
    except (ValueError, TypeError, KeyError) as exc:
        result = {"accepted": False, "error": str(exc), "failed_index": None,
                  "event_hashes": [], "certificate": None}
    output = dumps(result, sort_keys=True, indent=2) + "\n"
    if args.output:
        if args.output.exists():
            parser.error("refusing to overwrite an existing receipt")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
