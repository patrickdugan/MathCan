"""CHTR-07: pinned-source Uniswap v4 PoolManager transient-accounting witness checker.

This validates a DECLARED, ordered, instrumented-source witness. The observer
must separately authenticate contract address, call frames, full TSTORE writes,
all external balance changes and the pinned bytecode/source relationship.
Neither a transaction receipt nor the examples here establish that provenance.

Coverage: PoolManager's Lock, NonzeroDeltaCount, CurrencyDelta, CurrencyReserves,
ERC20/native settle paths, account deltas for swap/liquidity/donate, take,
clear, ERC6909 mint/burn (caller-owned burns), and call-frame rollback.
Uniswap's concentrated-liquidity arithmetic and permissioned hook return
values remain opaque inputs requiring an independent concrete-step witness.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from hashlib import sha256
import json

CORE_COMMIT = "bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6"
ZERO = "0x" + "0" * 40
UINT256 = 2**256 - 1
MAX_INT128 = 2**127 - 1
MIN_INT128 = -(2**127)
MAX_INT256 = 2**255 - 1
MIN_INT256 = -(2**255)
LOCK_SLOT = "0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23"
NONZERO_SLOT = "0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b"
SYNC_CURRENCY_SLOT = "0x27e098c505d44ec3574004bca052aabf76bd35004c182099d8c575fb238593b9"
SYNC_BALANCE_SLOT = "0x1e0745a7db1623981f0b2a5d4232364c00787266eb75ad546f190e6cebe9bd95"

_ROT = ((0, 36, 3, 41, 18), (1, 44, 10, 45, 2), (62, 6, 43, 15, 61),
        (28, 55, 25, 21, 56), (27, 20, 39, 8, 14))
_RC = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)
_MASK64 = 2**64 - 1


def keccak256(message: bytes) -> bytes:
    """Pure Python Ethereum Keccak-256, independently testable against vectors."""
    if not isinstance(message, bytes):
        raise TypeError("Keccak input must be bytes")
    padded = bytearray(message)
    padded.append(0x01)  # legacy Keccak domain separator, NOT FIPS SHA3
    padded.extend(b"\x00" * ((-len(padded)) % 136))
    padded[-1] ^= 0x80
    state = [0] * 25
    for offset in range(0, len(padded), 136):
        block = padded[offset:offset + 136]
        for lane in range(17):
            state[lane] ^= int.from_bytes(block[8 * lane:8 * lane + 8], "little")
        for rc in _RC:
            c = [0] * 5
            for x in range(5):
                c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
            for x in range(5):
                d = c[(x - 1) % 5] ^ ((c[(x + 1) % 5] << 1 |
                     c[(x + 1) % 5] >> 63) & _MASK64)
                for y in range(5):
                    state[x + 5 * y] ^= d
            b = [0] * 25
            for x in range(5):
                for y in range(5):
                    n = state[x + 5 * y]
                    rotation = _ROT[x][y]
                    t = ((n << rotation) | (n >> (64 - rotation))) & _MASK64 if rotation else n
                    b[y + 5 * ((2 * x + 3 * y) % 5)] = t
            for x in range(5):
                for y in range(5):
                    state[x + 5 * y] = (b[x + 5 * y] ^
                        ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])) & _MASK64
            state[0] ^= rc
    return b"".join(x.to_bytes(8, "little") for x in state[:4])


def address(value: str) -> str:
    if (not isinstance(value, str) or len(value) != 42 or not value.startswith("0x")
            or any(c not in "0123456789abcdef" for c in value[2:])):
        raise WitnessError("address must be lowercase 20-byte hex")
    return value


def word(value: int) -> str:
    if type(value) is not int or not MIN_INT256 <= value <= UINT256:
        raise WitnessError("word outside uint256/int256 range")
    return "0x" + format(value & UINT256, "064x")


def delta_slot(target: str, currency: str) -> str:
    """CurrencyDelta._computeSlot: keccak256 of two padded address words."""
    a, b = address(target), address(currency)
    return "0x" + keccak256(bytes.fromhex("00" * 12 + a[2:] + "00" * 12 + b[2:])).hex()


def _uint(value, bound=UINT256):
    if type(value) is not int or value < 0 or value > bound:
        raise WitnessError("uint quantity or balance outside declared bound")
    return value


def _int128(value):
    if type(value) is not int or not MIN_INT128 <= value <= MAX_INT128:
        raise WitnessError("signed delta must fit int128")
    return value


def _hex32(value):
    if not isinstance(value, str) or len(value) != 66 or not value.startswith("0x") \
            or any(c not in "0123456789abcdef" for c in value[2:]):
        raise WitnessError("TSTORE slot and value must be lowercase bytes32")
    return value


def _canonical_hash(obj):
    return sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class WitnessError(ValueError):
    pass


@dataclass(frozen=True)
class Audit:
    accepted: bool
    failed_at: int | None
    reason: str | None
    terminal: dict | None
    evidence_hash: str | None
    complete_source_evidence: bool = False  # never inferred from self-declared fixture


class V4DeltaWitness:
    """Check exact TSTORE microsteps against pinned PoolManager source rules.

    The event sequence and snapshots remain untrusted data. This class checks
    consistency, not EVM execution authenticity or whole-pool reserve balances.
    """

    def __init__(self, spec: dict):
        if not isinstance(spec, dict) or set(spec) != {
            "schema", "core_commit", "manager", "root", "balances", "events"}:
            raise WitnessError("unexpected witness schema fields")
        if spec["schema"] != "mathcan.chtr07.v1" or spec["core_commit"] != CORE_COMMIT:
            raise WitnessError("source pin/schema mismatch")
        self.manager = address(spec["manager"])
        self.root = address(spec["root"])
        if self.root == self.manager:
            raise WitnessError("root must be external")
        if not isinstance(spec["balances"], dict) or not spec["balances"]:
            raise WitnessError("nonempty currency balance table required")
        self.balances: dict[str, dict[str, int]] = {}
        for c, accounts in spec["balances"].items():
            address(c)
            if not isinstance(accounts, dict) or self.manager not in accounts or self.root not in accounts:
                raise WitnessError("each currency must include vault and caller balances")
            checked = {address(a): _uint(q) for a, q in accounts.items()}
            self.balances[c] = checked
        self.initial_supply = {c: sum(b.values()) for c, b in self.balances.items()}
        self.deltas: dict[tuple[str, str], int] = {}
        self.claims: dict[tuple[str, str], int] = {}
        self.counter = 0
        self.unlocked = False
        self.frames: list[tuple[str, dict | None]] = []
        self.sync_currency = ZERO
        self.synced_balance = 0
        self.tstore: dict[str, str] = {}
        self.opaque_pool_calls = 0
        self._events = spec["events"]
        if not isinstance(self._events, list) or not self._events:
            raise WitnessError("nonempty ordered events required")

    def _snapshot(self):
        return deepcopy((self.balances, self.deltas, self.claims, self.counter,
                         self.unlocked, self.sync_currency, self.synced_balance,
                         self.tstore, self.opaque_pool_calls))

    def _restore(self, checkpoint):
        (self.balances, self.deltas, self.claims, self.counter, self.unlocked,
         self.sync_currency, self.synced_balance, self.tstore,
         self.opaque_pool_calls) = deepcopy(checkpoint)

    def _fields(self, event, keys):
        if set(event) != set(keys):
            raise WitnessError("missing or unexpected event fields")

    def _write(self, slot, value, writes):
        _hex32(slot)
        value = _hex32(value)
        self.tstore[slot] = value
        writes.append({"slot": slot, "value": value})

    def _update_delta(self, beneficiary, currency, change, writes):
        beneficiary, currency = address(beneficiary), address(currency)
        _int128(change)
        if beneficiary not in self.balances[currency]:
            raise WitnessError("unregistered delta beneficiary")
        if change == 0:
            return
        key = (beneficiary, currency)
        prior = self.deltas.get(key, 0)
        nxt = prior + change
        if not MIN_INT256 <= nxt <= MAX_INT256:
            raise WitnessError("int256 currency delta overflow")
        self.deltas[key] = nxt
        self._write(delta_slot(beneficiary, currency), word(nxt), writes)
        if prior == 0 and nxt != 0:
            self.counter += 1
            self._write(NONZERO_SLOT, word(self.counter), writes)
        elif prior != 0 and nxt == 0:
            self.counter -= 1
            if self.counter < 0:
                raise WitnessError("NonzeroDeltaCount underflow")
            self._write(NONZERO_SLOT, word(self.counter), writes)

    def _move(self, currency, from_, to, amount):
        currency, from_, to = address(currency), address(from_), address(to)
        if currency not in self.balances or from_ == to:
            raise WitnessError("unknown currency or self transfer")
        _uint(amount)
        a = self.balances[currency]
        if from_ not in a or to not in a or a[from_] < amount:
            raise WitnessError("missing account or insufficient physical funds")
        a[from_] -= amount
        a[to] += amount

    def _step(self, e):
        if not isinstance(e, dict) or not isinstance(e.get("op"), str):
            raise WitnessError("invalid event")
        op = e["op"]
        if op == "unlock":
            self._fields(e, ("op", "actor", "writes"))
            if self.unlocked or self.frames or address(e["actor"]) != self.root or self.counter:
                raise WitnessError("invalid unlock frame or outstanding delta")
            writes = []
            self._write(LOCK_SLOT, word(1), writes)
            self.frames = [(self.root, None)]
            self.unlocked = True
        elif op == "sync":
            self._fields(e, ("op", "actor", "currency", "observed_balance", "writes"))
            self._actor(e["actor"], require_unlocked=False)
            c = address(e["currency"])
            if c not in self.balances:
                raise WitnessError("unknown synced currency")
            writes = []
            if c == ZERO:
                self.sync_currency = ZERO
                self._write(SYNC_CURRENCY_SLOT, word(0), writes)
            else:
                observed = _uint(e["observed_balance"])
                if observed != self.balances[c][self.manager]:
                    raise WitnessError("sync balance witness mismatch")
                self.sync_currency, self.synced_balance = c, observed
                self._write(SYNC_CURRENCY_SLOT, word(int(c, 16)), writes)
                self._write(SYNC_BALANCE_SLOT, word(observed), writes)
        elif op == "transfer":
            self._fields(e, ("op", "actor", "currency", "source", "destination", "amount", "writes"))
            self._actor(e["actor"], require_unlocked=False)
            if e["currency"] == ZERO:
                raise WitnessError("native external transfers require explicit settle(msg.value)")
            self._move(e["currency"], e["source"], e["destination"], e["amount"])
            writes = []
        elif op == "enter":
            self._fields(e, ("op", "actor", "callee", "writes"))
            self._actor(e["actor"])
            callee = address(e["callee"])
            if callee == self.manager or any(callee not in b for b in self.balances.values()):
                raise WitnessError("unregistered callback callee")
            self.frames.append((callee, self._snapshot()))
            writes = []
        elif op in ("return", "revert"):
            self._fields(e, ("op", "actor", "writes"))
            self._actor(e["actor"])
            if len(self.frames) <= 1:
                raise WitnessError("no nested frame to return or revert")
            _, snap = self.frames.pop()
            if op == "revert":
                self._restore(snap)
            writes = []
        else:
            self._actor(e.get("actor"))
            writes = []
            if op == "pool_account":
                self._fields(e, ("op", "actor", "kind", "currency0", "currency1",
                                 "hook", "hook_delta", "caller_delta", "writes"))
                if e["kind"] not in ("swap", "modifyLiquidity", "donate"):
                    raise WitnessError("unknown PoolManager accounting origin")
                c0, c1, hook = address(e["currency0"]), address(e["currency1"]), address(e["hook"])
                if c0 == c1 or c0 not in self.balances or c1 not in self.balances:
                    raise WitnessError("malformed pool currencies")
                if (not isinstance(e["hook_delta"], list) or len(e["hook_delta"]) != 2
                    or not isinstance(e["caller_delta"], list) or len(e["caller_delta"]) != 2):
                    raise WitnessError("two signed account deltas per pair required")
                if e["kind"] == "donate" and e["hook_delta"] != [0, 0]:
                    raise WitnessError("PoolManager.donate does not post a hook balance delta")
                for c, change in zip((c0, c1), e["hook_delta"]):
                    if change:
                        self._update_delta(hook, c, change, writes)
                    else:
                        _int128(change)
                for c, change in zip((c0, c1), e["caller_delta"]):
                    self._update_delta(e["actor"], c, change, writes)
                self.opaque_pool_calls += 1
            elif op == "take":
                self._fields(e, ("op", "actor", "currency", "recipient", "amount", "writes"))
                c = address(e["currency"])
                amount = _uint(e["amount"], MAX_INT128)
                self._update_delta(e["actor"], c, -amount, writes)
                self._move(c, self.manager, e["recipient"], amount)
            elif op == "mint":
                self._fields(e, ("op", "actor", "currency", "recipient", "amount", "writes"))
                c = address(e["currency"])
                amount = _uint(e["amount"], MAX_INT128)
                self._update_delta(e["actor"], c, -amount, writes)
                key = (address(e["recipient"]), c)
                if e["recipient"] not in self.balances[c]:
                    raise WitnessError("unregistered ERC6909 beneficiary")
                self.claims[key] = _uint(self.claims.get(key, 0) + amount)
            elif op == "burn":
                self._fields(e, ("op", "actor", "currency", "amount", "writes"))
                c = address(e["currency"])
                amount = _uint(e["amount"], MAX_INT128)
                key = (address(e["actor"]), c)  # approved caller-owned subset only
                if self.claims.get(key, 0) < amount:
                    raise WitnessError("ERC6909 claim insufficient")
                self._update_delta(e["actor"], c, amount, writes)
                self.claims[key] -= amount
            elif op == "clear":
                self._fields(e, ("op", "actor", "currency", "amount", "writes"))
                c = address(e["currency"])
                amount = _uint(e["amount"], MAX_INT128)
                if self.deltas.get((e["actor"], c), 0) != amount:
                    raise WitnessError("clear requires full positive transient delta")
                self._update_delta(e["actor"], c, -amount, writes)
            elif op == "settle":
                self._fields(e, ("op", "actor", "recipient", "msg_value", "paid",
                                 "observed_balance", "writes"))
                c = self.sync_currency
                if c not in self.balances:
                    raise WitnessError("native currency absent from registered balances")
                paid = _uint(e["paid"], MAX_INT128)
                msg_value = _uint(e["msg_value"])
                if c == ZERO:
                    if paid != msg_value:
                        raise WitnessError("native paid amount must equal msg.value")
                    self._move(ZERO, e["actor"], self.manager, msg_value)
                    if e["observed_balance"] != self.balances[c][self.manager]:
                        raise WitnessError("observed native balance mismatch")
                else:
                    if msg_value != 0:
                        raise WitnessError("ERC20 settle cannot carry msg.value")
                    observed = _uint(e["observed_balance"])
                    if observed != self.balances[c][self.manager]:
                        raise WitnessError("ERC20 balanceOfSelf observation mismatch")
                    if observed < self.synced_balance or paid != observed - self.synced_balance:
                        raise WitnessError("settle credit diverges from sync balance delta")
                    self.sync_currency = ZERO
                    self._write(SYNC_CURRENCY_SLOT, word(0), writes)
                self._update_delta(e["recipient"], c, paid, writes)
            elif op == "lock":
                self._fields(e, ("op", "actor", "writes"))
                if len(self.frames) != 1 or self.counter != 0 or any(self.deltas.values()):
                    raise WitnessError("PoolManager unlockCallback has unsettled currencies")
                self._write(LOCK_SLOT, word(0), writes)
                self.frames.clear()
                self.unlocked = False
            else:
                raise WitnessError("unsupported PoolManager opcode")
        if e.get("writes") != writes:
            raise WitnessError("TSTORE witness differs from pinned source transition")
        self._check()

    def _actor(self, candidate, *, require_unlocked=True):
        actor = address(candidate)
        if require_unlocked and (not self.unlocked or not self.frames):
            raise WitnessError("PoolManager method called while locked")
        if self.frames and actor != self.frames[-1][0]:
            raise WitnessError("actor differs from declared active call frame")
        if not self.frames and actor != self.root:
            raise WitnessError("unknown actor outside unlock frame")

    def _check(self):
        if self.counter != sum(1 for n in self.deltas.values() if n != 0):
            raise WitnessError("NonzeroDeltaCount is inconsistent with per-address deltas")
        if self.tstore.get(NONZERO_SLOT, word(0)) != word(self.counter):
            raise WitnessError("transient nonzero-count slot differs")
        if self.tstore.get(LOCK_SLOT, word(0)) != word(int(self.unlocked)):
            raise WitnessError("transient unlock slot differs")
        for (a, c), n in self.deltas.items():
            if self.tstore.get(delta_slot(a, c), word(0)) != word(n):
                raise WitnessError("transient delta slot differs")
        for currency, accounts in self.balances.items():
            if any(q < 0 or q > UINT256 for q in accounts.values()):
                raise WitnessError("physical balance overflow")
            if sum(accounts.values()) != self.initial_supply[currency]:
                raise WitnessError("currency balance supply changed or account omitted")

    def replay(self) -> Audit:
        try:
            for i, event in enumerate(self._events):
                self._step(event)
            if self.unlocked or self.frames:
                raise WitnessError("unfinished unlock or callback frame")
            return Audit(True, None, None, {
                "nonzero_delta_count": self.counter,
                "deltas": {a + ":" + c: n for (a, c), n in sorted(self.deltas.items())},
                "claims": {a + ":" + c: n for (a, c), n in sorted(self.claims.items())},
                "vault_balances": {c: self.balances[c][self.manager] for c in sorted(self.balances)},
                "opaque_pool_calls": self.opaque_pool_calls,
                "source_commit": CORE_COMMIT,
            }, _canonical_hash(self._events), False)
        except (WitnessError, KeyError, TypeError, IndexError) as exc:
            return Audit(False, i if "i" in locals() else None, str(exc), None, None, False)


def from_json_spec(spec: dict) -> Audit:
    return V4DeltaWitness(spec).replay()


def main(argv=None) -> int:
    from argparse import ArgumentParser
    from pathlib import Path
    parser = ArgumentParser(description="Pinned Uniswap v4 transient-accounting witness replay")
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    a = parser.parse_args(argv)
    try:
        data = json.loads(a.input.read_text(encoding="utf8"))
        result = from_json_spec(data)
    except (json.JSONDecodeError, WitnessError) as exc:
        result = Audit(False, None, str(exc), None, None, False)
    obj = result.__dict__
    rendered = json.dumps(obj, indent=2, sort_keys=True) + "\n"
    if a.output:
        if a.output.exists():
            parser.error("output already exists")
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(rendered, encoding="utf8")
    else:
        print(rendered, end="")
    return 0 if result.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
