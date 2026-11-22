"""RHD-10B: leakage-audited CPU baseline for finite recurrent corrections.

This trains a *tabular behavioral clone*, not a neural RLT. All evaluation
observations omit teacher actions and expected values. Metrics describe only
the restricted RHD-10 finite-ring verifier grammar.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

from research.rh_proof_distillation.rhd10_rank_one_repair import (
    Candidate, apply_action, episodes, suggested_action, verify,
)


def candidate_from_snapshot(raw: dict) -> Candidate:
    """Reconstruct an independent policy state from public candidate fields."""
    return Candidate(
        w0=raw["w0"],
        local_coeffs=tuple(raw["local_coeffs"]),
        global_sign=raw["global_sign"],
        conductor=raw["conductor"],
        unit_offset=raw["unit_offset"],
        exceptions=frozenset(raw["exceptions"]),
    )


def public_episode(row: dict) -> dict:
    """Whitelist test-time fields. The generator's teacher labels are private."""
    probe = row["local_probe"]
    return {
        "root_id": row["root_id"],
        "selected_factor": row["selected_factor"],
        "source_prime": row["source_prime"],
        "candidate": row["candidate"],
        "local_probe": {
            "a": probe["a"], "b": probe["b"],
            "factor_mod_841": probe["factor_mod_841"],
        },
    }


def redact_failure(failure: dict) -> dict:
    """Keep testable failure diagnostics, suppress expected/correct values."""
    allowed = ("gate", "factor", "place", "selected_place", "probe", "observed")
    return {key: failure[key] for key in allowed if key in failure}


def key_for_failure(problem: dict) -> str:
    gate = problem["gate"]
    suffix = ""
    if "factor" in problem:
        suffix = f":{problem['factor']}"
    elif "place" in problem:
        suffix = f":{problem['place']}"
    return gate + suffix


def action_string(action: dict) -> str:
    return json.dumps(action, sort_keys=True, separators=(",", ":"))


@dataclass(frozen=True)
class FrequencyPolicy:
    """Majority-action table fitted exclusively to training teacher traces."""
    table: dict[str, dict]
    training_examples: int

    @classmethod
    def fit(cls, source: list[dict]) -> "FrequencyPolicy":
        votes: dict[str, Counter] = defaultdict(Counter)
        n = 0
        for row in source:
            if row["split"] != "train":
                raise ValueError("fit accepts training episodes exclusively")
            state = candidate_from_snapshot(row["candidate"])
            for transition in row["oracle_actions"]:
                if "action" not in transition:
                    break  # the teacher's explicit STOP
                problems = verify(state)
                if not problems:
                    raise AssertionError("teacher acted after verification success")
                problem = redact_failure(problems[0])
                action = transition["action"]
                votes[key_for_failure(problem)][action_string(action)] += 1
                state = apply_action(state, action)
                n += 1
            if verify(state):
                raise AssertionError("training teacher trace failed replay")
        table = {}
        for key in sorted(votes):
            winning = sorted(votes[key].items(), key=lambda item: (-item[1], item[0]))[0][0]
            table[key] = json.loads(winning)
        return cls(table, n)

    def choose(self, failure: dict) -> dict:
        return dict(self.table.get(key_for_failure(failure), {"kind": "STOP"}))


@dataclass(frozen=True)
class ExactRuleCeiling:
    """Privileged finite-arithmetic control, deliberately labeled an oracle."""
    def choose(self, failure: dict) -> dict:
        return suggested_action(failure)


def _metric_result(solved: bool, edits: int, calls: int, invalid: int,
                   post_success: int, correct_stop: bool) -> dict:
    return {"solved": solved, "edits": edits, "verifier_calls": calls,
            "invalid_edits": invalid, "post_success_edits": post_success,
            "correct_stop": correct_stop}


def evaluate_episode(row: dict, policy, mode: str) -> dict:
    """Verifier calls count only what a policy can see, not audit scoring.

    sparse_recurrent: one redacted failing gate per round.
    sparse_one_step: exactly one repair, followed by a final verifier call.
    full_open_loop: all redacted failures initially, make edits without a
    new verifier until a final check. This is a necessary strong baseline.
    """
    public = public_episode(row)
    state = candidate_from_snapshot(public["candidate"])
    calls = edits = invalid = post_success = 0

    def query(full: bool) -> list[dict]:
        nonlocal calls
        calls += 1
        all_failures = verify(state)
        exposed = all_failures if full else all_failures[:1]
        return [redact_failure(failure) for failure in exposed]

    def repair(failure: dict) -> None:
        nonlocal state, edits, invalid, post_success
        # Hidden verifier calls below are evaluator instrumentation only.
        before = len(verify(state))
        action = policy.choose(failure)
        if action.get("kind") == "STOP":
            return
        state = apply_action(state, action)
        edits += 1
        after = len(verify(state))
        invalid += int(after >= before)
        post_success += int(before == 0)

    if mode == "full_open_loop":
        for failure in query(full=True):
            repair(failure)
        final = query(full=True)
    elif mode in ("sparse_one_step", "sparse_recurrent"):
        budget = 1 if mode == "sparse_one_step" else 3
        failures = query(full=False)
        for _ in range(budget):
            if not failures:
                break
            repair(failures[0])
            failures = query(full=False)
        final = failures
    else:
        raise ValueError(f"unrecognized mode: {mode}")
    solved = not final
    return _metric_result(solved, edits, calls, invalid, post_success, solved)


def aggregate(rows: list[dict], policy, mode: str) -> dict:
    totals = Counter()
    for row in rows:
        outcome = evaluate_episode(row, policy, mode)
        totals.update({
            "solved": int(outcome["solved"]),
            "edits": outcome["edits"],
            "calls": outcome["verifier_calls"],
            "invalid": outcome["invalid_edits"],
            "post_success": outcome["post_success_edits"],
            "stop_correct": int(outcome["correct_stop"]),
        })
    n = len(rows)
    return {
        "episodes": n, "solved": totals["solved"],
        "verified_repairs_per_100_verifier_calls":
            round(100 * totals["solved"] / totals["calls"], 6) if totals["calls"] else 0,
        "mean_verifier_calls": round(totals["calls"] / n, 6) if n else 0,
        "total_verifier_calls": totals["calls"],
        "edits": totals["edits"], "invalid_edits": totals["invalid"],
        "post_success_edits": totals["post_success"],
        "stop_accuracy": round(totals["stop_correct"] / n, 6) if n else 0,
    }


def build_report(root_rows: list[dict] | None = None) -> dict:
    rows = list(episodes()) if root_rows is None else root_rows
    split = {
        name: [row for row in rows if row["split"] == name]
        for name in ("train", "val", "test")
    }
    if not split["train"] or not split["val"] or not split["test"]:
        raise ValueError("train, validation, and test must all be populated")
    if len({r["root_id"] for r in rows}) != len(rows):
        raise ValueError("duplicate root")
    learned = FrequencyPolicy.fit(split["train"])
    policies = {"trained_frequency": learned, "privileged_rule_ceiling": ExactRuleCeiling()}
    modes = ("sparse_one_step", "sparse_recurrent", "full_open_loop")
    metrics = {
        phase: {
            policy_name: {
                mode: aggregate(split[phase], policy, mode)
                for mode in modes
            }
            for policy_name, policy in policies.items()
        }
        for phase in ("val", "test")
    }
    return {
        "experiment": "RHD-10B finite within-family verifier-efficiency audit",
        "model": "tabular behavioral clone, not a trained neural recurrent model",
        "training_teacher_transitions": learned.training_examples,
        "learned_action_keys": sorted(learned.table),
        "split_counts": {name: len(group) for name, group in split.items()},
        "test_policy_observation_fields":
            sorted(public_episode(split["test"][0]).keys()),
        "test_verifier_fields":
            sorted(redact_failure(verify(candidate_from_snapshot(
                split["test"][0]["candidate"]))[0]).keys()),
        "verifier_call_definition":
            "policy-visible queries only; independent evaluator audit checks excluded",
        "generalization": "within Q(zeta20), p=29 finite fault grammar only",
        "proof_term_data": False,
        "results": metrics,
    }


def write_report(output: Path) -> dict:
    report = build_report()
    output.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode("utf-8")
    output.write_bytes(data)
    output.with_suffix(".sha256").write_text(
        hashlib.sha256(data).hexdigest() + "  " + output.name + "\n",
        encoding="utf-8",
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = write_report(args.output)
    print(json.dumps({
        "split_counts": report["split_counts"],
        "test": report["results"]["test"]["trained_frequency"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
