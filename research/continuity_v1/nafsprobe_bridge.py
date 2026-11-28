"""Read-only compatibility adapter for NafsProbe's legacy SQLite SelfModel.

Input is a simulator-owned snapshot, not an authenticated event log. Explicit
commitment/belief fields become *namespaced simulation facts*. Free-text
reflections, episode reasons, values and anchor are annotations only.

This module never writes to the source database or to the frozen experiment.
"""
from __future__ import annotations

import argparse
from contextlib import closing
from dataclasses import asdict, dataclass
from hashlib import sha256
import json
from pathlib import Path
import sqlite3
from typing import Any

from research.continuity_v1.core import Event, Projection, replay

MAX_SNAPSHOT_BYTES = 4 * 1024 * 1024


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def _node_id(category: str, key: str) -> str:
    source = _canonical_json({"category": category, "key": key})
    return f"legacy:{category}:{sha256(source.encode('utf-8')).hexdigest()}"


def _string(value: Any, path: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{path} must be a string")
    return value


def _string_dict(value: Any, path: str) -> dict[str, str]:
    if not isinstance(value, dict):
        raise ValueError(f"{path} must be an object")
    return {_string(k, path + '.key'): _string(v, path + '.' + str(k))
            for k, v in value.items()}


def _items(value: Any, path: str) -> list[dict[str, Any]]:
    if not isinstance(value, list) or any(not isinstance(e, dict) for e in value):
        raise ValueError(f"{path} must be a list of objects")
    return value


def _validate_payload(payload: Any) -> dict[str, Any]:
    """The concrete shape written by nafsprobe/causal-v0.2/nafs_probe.py.

    Unknown fields are rejected so schema upgrades cannot silently change the
    meaning of canonical fields. A validated JSON shape is not source proof.
    """
    if not isinstance(payload, dict):
        raise ValueError("SelfModel payload must be a JSON object")
    expected = {"agent_id", "values", "autobiographical_anchor", "commitments",
                "beliefs", "episodes", "reflections"}
    if set(payload) != expected:
        raise ValueError("SelfModel fields differ from frozen NafsProbe schema")
    _string(payload["agent_id"], "agent_id")
    _string(payload["autobiographical_anchor"], "autobiographical_anchor")
    values = payload["values"]
    if not isinstance(values, list) or any(not isinstance(v, str) for v in values):
        raise ValueError("values must be a list of strings")
    _string_dict(payload["commitments"], "commitments")
    if not isinstance(payload["beliefs"], dict):
        raise ValueError("beliefs must be a dictionary")
    for key, belief in payload["beliefs"].items():
        _string(key, "beliefs.key")
        if not isinstance(belief, dict) or set(belief) != {"value", "source", "verified_during"}:
            raise ValueError(f"invalid legacy belief record at {key!r}")
        _string_dict(belief, "beliefs." + key)
    _items(payload["episodes"], "episodes")
    _items(payload["reflections"], "reflections")
    return payload


@dataclass(frozen=True)
class LegacyImport:
    run_id: str
    source_payload_sha256: str
    source_assurance: str
    events: tuple[Event, ...]
    projection: Projection
    episode_count: int
    reflection_count: int

    def public_receipt(self) -> dict[str, Any]:
        """Content-free attestation of what was read and derived."""
        return {"run_id": self.run_id,
                "source_payload_sha256": self.source_payload_sha256,
                "source_assurance": self.source_assurance,
                "canonical_digest": self.projection.canonical_digest,
                "history_digest": self.projection.history_digest,
                "canonical_claim_count": len(self.projection.claims),
                "episode_count": self.episode_count,
                "reflection_count": self.reflection_count}


def translate_snapshot(payload: dict[str, Any], *, run_id: str,
                       source_payload_sha256: str) -> LegacyImport:
    """Pure transform of one current-state snapshot into typed replay events.

    The original NafsProbe database does not retain separate source events for
    its mutable commitments/beliefs. Hence this bridge cannot reconstruct when
    an obligation was accepted or prove a claimed cryptographic signature.
    """
    source = _validate_payload(payload)
    events: list[Event] = []
    # Canonical claims are tagged as *legacy simulator snapshot* data. They are
    # intentionally not "authorized:" permissions for a live policy gate.
    events.append(Event(_node_id("agent", "identity"), "assert",
                        claim="nafs.agent:" + _canonical_json({"agent_id": source["agent_id"]})))
    for key, value in sorted(source["commitments"].items()):
        events.append(Event(_node_id("commitment", key), "assert",
                            claim="nafs.commitment:" + _canonical_json({"key": key, "value": value})))
    for key, belief in sorted(source["beliefs"].items()):
        events.append(Event(_node_id("belief", key), "assert",
                            claim="nafs.simulated_belief:" + _canonical_json({"key": key, **belief})))

    # Annotations retain their source content for later narrative inspection.
    # They never modify canonical claims and are marked as unverified notes.
    events.append(Event("legacy:profile", "interpret", model_version="nafsprobe-profile-snapshot",
                        note=_canonical_json({"values": source["values"],
                                              "autobiographical_anchor": source["autobiographical_anchor"]})))
    for idx, episode in enumerate(source["episodes"]):
        events.append(Event(f"legacy:episode:{idx}", "interpret",
                            model_version="nafsprobe-episode-annotation",
                            note=_canonical_json(episode)))
    for idx, reflection in enumerate(source["reflections"]):
        events.append(Event(f"legacy:reflection:{idx}", "interpret",
                            model_version="nafsprobe-model-reflection",
                            note=_canonical_json(reflection)))
    projection = replay(events)
    return LegacyImport(run_id, source_payload_sha256, "legacy_sqlite_snapshot_unverified",
                        tuple(events), projection, len(source["episodes"]), len(source["reflections"]))


def load_nafsprobe_snapshot(db_path: str | Path, run_id: str,
                            *, max_payload_bytes: int = MAX_SNAPSHOT_BYTES) -> LegacyImport:
    """Open the legacy state table read-only; reject missing or invalid rows."""
    if not run_id:
        raise ValueError("a nonempty run_id is required")
    if max_payload_bytes <= 0:
        raise ValueError("max_payload_bytes must be positive")
    source = Path(db_path).resolve(strict=True)
    uri = source.as_uri() + "?mode=ro"
    with closing(sqlite3.connect(uri, uri=True, timeout=5)) as db:
        db.execute("PRAGMA query_only=ON")
        row = db.execute("SELECT payload FROM agent_state WHERE run_id=?", (run_id,)).fetchone()
    if row is None:
        raise KeyError(f"run_id absent from legacy state: {run_id!r}")
    original = row[0]
    if not isinstance(original, str):
        raise ValueError("legacy payload must be a JSON text column")
    raw_bytes = original.encode("utf-8")
    if len(raw_bytes) > max_payload_bytes:
        raise ValueError("legacy snapshot exceeds the configured size cap")
    try:
        state = json.loads(original)
    except json.JSONDecodeError as exc:
        raise ValueError("malformed NafsProbe snapshot JSON") from exc
    return translate_snapshot(state, run_id=run_id,
                              source_payload_sha256=sha256(raw_bytes).hexdigest())


def main() -> None:
    parser = argparse.ArgumentParser(description="Read-only NafsProbe snapshot continuity audit")
    parser.add_argument("--db", required=True)
    parser.add_argument("--run-id", required=True)
    args = parser.parse_args()
    result = load_nafsprobe_snapshot(args.db, args.run_id)
    print(json.dumps(result.public_receipt(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
