"""Append-only *observation history* for legacy NafsProbe snapshots.

NafsProbe has one mutable JSON payload per run_id, not a source event stream.
This sidecar records changes first OBSERVED on sync. It never invents the
historical timestamps or causes of legacy state transitions.

The source SQLite database is only read. This separate SQLite sidecar is a
research artifact, with hash-chain checks for accidental corruption; hashes
alone do not authenticate an adversarially editable source or destination.
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
from research.continuity_v1.nafsprobe_bridge import LegacyImport, load_nafsprobe_snapshot

ZERO_HASH = "0" * 64


def _json(v: Any) -> str:
    return json.dumps(v, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def _digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def _claim_digest(claims: tuple[str, ...]) -> str:
    return _digest(_json(sorted(claims)))


def _chain_next(previous: str, event: Event) -> str:
    return _digest(previous + "\n" + _json(asdict(event)))


def _decode_event(event_json: str) -> Event:
    obj = json.loads(event_json)
    if not isinstance(obj, dict) or set(obj) != {"eid", "kind", "claim", "premises",
                                                     "target", "model_version", "note"}:
        raise ValueError("sidecar has malformed event shape")
    if not isinstance(obj["premises"], list):
        raise ValueError("sidecar has malformed premises")
    obj["premises"] = tuple(obj["premises"])
    return Event(**obj)


def _schema(conn: sqlite3.Connection) -> None:
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS continuity_observations (
        run_id TEXT NOT NULL, seq INTEGER NOT NULL, source_sha TEXT NOT NULL,
        bridge_history_sha TEXT NOT NULL, canonical_claims_sha TEXT NOT NULL,
        first_event_pos INTEGER NOT NULL, last_event_pos INTEGER NOT NULL,
        chain_tip TEXT NOT NULL, assurance TEXT NOT NULL,
        PRIMARY KEY (run_id, seq)
    );
    CREATE TABLE IF NOT EXISTS continuity_events (
        run_id TEXT NOT NULL, pos INTEGER NOT NULL, event_json TEXT NOT NULL,
        prev_hash TEXT NOT NULL, event_hash TEXT NOT NULL,
        PRIMARY KEY (run_id, pos)
    );
    """)


def _read_and_audit(conn: sqlite3.Connection, run_id: str) -> tuple[list[Event], str, list[tuple]]:
    observations = conn.execute("""SELECT seq, source_sha, bridge_history_sha,
      canonical_claims_sha, first_event_pos, last_event_pos, chain_tip, assurance
      FROM continuity_observations WHERE run_id=? ORDER BY seq""", (run_id,)).fetchall()
    rows = conn.execute("""SELECT pos, event_json, prev_hash, event_hash FROM continuity_events
      WHERE run_id=? ORDER BY pos""", (run_id,)).fetchall()
    events = []
    prev = ZERO_HASH
    for expected_pos, (pos, event_json, predecessor, current) in enumerate(rows):
        if pos != expected_pos or predecessor != prev:
            raise ValueError("sidecar chain position or predecessor mismatch")
        event = _decode_event(event_json)
        if _json(asdict(event)) != event_json or _chain_next(prev, event) != current:
            raise ValueError("sidecar event canonicalization or hash mismatch")
        prev = current
        events.append(event)
    projection = replay(events)
    if observations:
        for i, obs in enumerate(observations):
            seq, _, _, claim_sha, start, end, tip, assurance = obs
            if seq != i or start < 0 or end < start or end >= len(rows):
                raise ValueError("sidecar observation indices are inconsistent")
            if i and start != observations[i-1][5] + 1:
                raise ValueError("sidecar observation ranges are discontinuous")
            if i == 0 and start != 0:
                raise ValueError("sidecar must begin at event zero")
            if rows[end][3] != tip or assurance != "legacy_sqlite_snapshot_unverified":
                raise ValueError("sidecar observation binding mismatch")
            prefix = replay(events[:end+1])
            if _claim_digest(prefix.claims) != claim_sha:
                raise ValueError("sidecar observation claim digest mismatch")
        if observations[-1][5] != len(rows)-1:
            raise ValueError("sidecar contains unbound trailing events")
    elif rows:
        raise ValueError("sidecar has events without observations")
    return events, prev, observations


def _current_claim_map(events: list[Event], projection: Projection) -> dict[str, Event]:
    """Map original stable field identity to its current observed assertion."""
    active = set(projection.active_node_ids)
    out: dict[str, Event] = {}
    for e in events:
        if e.kind == "assert" and e.eid in active:
            if "::" not in e.eid:
                raise ValueError("unrecognized sidecar assertion ID")
            origin = e.eid.split("::", 1)[1]
            if origin in out:
                raise ValueError("multiple active sidecar versions of one field")
            out[origin] = e
    return out


@dataclass(frozen=True)
class SidecarReceipt:
    run_id: str
    status: str
    observation_seq: int
    event_count: int
    source_payload_sha256: str
    canonical_claims_sha256: str
    chain_tip: str

    def public_receipt(self) -> dict[str, Any]:
        return asdict(self)


def audit_sidecar(sidecar_path: str | Path, run_id: str) -> SidecarReceipt:
    source = Path(sidecar_path).resolve(strict=True)
    uri = source.as_uri() + "?mode=ro"
    with closing(sqlite3.connect(uri, uri=True)) as conn:
        conn.execute("PRAGMA query_only=ON")
        events, tip, observations = _read_and_audit(conn, run_id)
    if not observations:
        raise KeyError("no observations for run")
    last = observations[-1]
    return SidecarReceipt(run_id, "audited", last[0], len(events), last[1], last[3], tip)


def sync_nafsprobe(source_db: str | Path, run_id: str,
                   sidecar_db: str | Path) -> SidecarReceipt:
    source = Path(source_db).resolve(strict=True)
    destination = Path(sidecar_db).resolve()
    if source == destination:
        raise ValueError("sidecar path must be separate from the legacy NafsProbe database")
    legacy: LegacyImport = load_nafsprobe_snapshot(source, run_id)
    destination.parent.mkdir(parents=True, exist_ok=True)
    # A sidecar transaction serializes sync writers for the same run.
    with closing(sqlite3.connect(destination, timeout=10)) as conn:
        conn.execute("PRAGMA journal_mode=DELETE")
        _schema(conn)
        conn.execute("BEGIN IMMEDIATE")
        try:
            previous, tip, observations = _read_and_audit(conn, run_id)
            if observations and observations[-1][1] == legacy.source_payload_sha256:
                conn.commit()
                last = observations[-1]
                return SidecarReceipt(run_id, "unchanged", last[0], len(previous), last[1], last[3], tip)
            seq = len(observations)
            old_projection = replay(previous)
            old_by_source = _current_claim_map(previous, old_projection)
            new_by_source = {e.eid: e for e in legacy.events if e.kind == "assert"}
            changes: list[Event] = []
            for origin in sorted(old_by_source):
                old = old_by_source[origin]
                new = new_by_source.get(origin)
                if new is None or old.claim != new.claim:
                    changes.append(Event(f"obs{seq}:retract::{origin}", "retract", target=old.eid))
            for origin in sorted(new_by_source):
                new = new_by_source[origin]
                old = old_by_source.get(origin)
                if old is None or old.claim != new.claim:
                    changes.append(Event(f"obs{seq}:assert::{origin}", "assert", claim=new.claim))
            # We retain all observed model-attributed annotations at each changed
            # source snapshot. This records an observation, not event provenance.
            for a in legacy.events:
                if a.kind == "interpret":
                    changes.append(Event(f"obs{seq}:interpret::{a.eid}", "interpret",
                                         model_version=a.model_version, note=a.note))
            if not changes:
                # E.g. the original JSON bytes were reserialized in another order.
                # An anchor event binds the new source fingerprint without
                # granting canonical authority.
                changes.append(Event(f"obs{seq}:interpret::source-representation", "interpret",
                                     model_version="nafsprobe-snapshot-representation",
                                     note="The observed source bytes changed without changing projected facts"))
            all_events = previous + changes
            projection = replay(all_events)
            if projection.claims != legacy.projection.claims:
                raise ValueError("sidecar projection differs from current NafsProbe snapshot")
            start = len(previous)
            for off, event in enumerate(changes):
                predecessor = tip
                tip = _chain_next(tip, event)
                conn.execute("""INSERT INTO continuity_events
                    (run_id,pos,event_json,prev_hash,event_hash) VALUES (?,?,?,?,?)""",
                    (run_id, start+off, _json(asdict(event)), predecessor, tip))
            claimed = _claim_digest(projection.claims)
            conn.execute("""INSERT INTO continuity_observations
                (run_id,seq,source_sha,bridge_history_sha,canonical_claims_sha,
                 first_event_pos,last_event_pos,chain_tip,assurance)
                 VALUES (?,?,?,?,?,?,?,?,?)""",
                 (run_id,seq,legacy.source_payload_sha256,legacy.projection.history_digest,
                  claimed,start,len(all_events)-1,tip,legacy.source_assurance))
            conn.commit()
            return SidecarReceipt(run_id,"appended",seq,len(all_events),
                                  legacy.source_payload_sha256,claimed,tip)
        except Exception:
            conn.rollback()
            raise


def main() -> None:
    p = argparse.ArgumentParser(description="Maintain a sidecar of observed legacy NafsProbe state revisions")
    p.add_argument("--db", help="The original NafsProbe database, which is opened read-only")
    p.add_argument("--sidecar", required=True)
    p.add_argument("--run-id", required=True)
    p.add_argument("--audit-only", action="store_true")
    args = p.parse_args()
    if args.audit_only:
        result = audit_sidecar(args.sidecar, args.run_id)
    else:
        if not args.db:
            p.error("--db is required unless --audit-only")
        result = sync_nafsprobe(args.db, args.run_id, args.sidecar)
    print(json.dumps(result.public_receipt(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
