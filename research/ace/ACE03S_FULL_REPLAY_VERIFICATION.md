# ACE-03S | Complete streamed replay verification

Both complete modular proof graphs passed on 2026-11-25 using the
unchanged source at `0456b5981235db8ba1faf154b8bbd4744f256868`.

| Graph | Checked modules | Kernel visits | Elapsed seconds | Maximum RSS, KiB |
| --- | ---: | ---: | ---: | ---: |
| Unbounded Replacement | 21 | 81,601 | 50.76 | 4,466,548 |
| Unbounded Separation | 21 | 103,182 | 106.25 | 5,018,632 |

Each runner supplied its entire graph in topological order to
`compileModular`. The checker validated dependency contexts and closed
conclusions before admitting each later node. Both runs checked the
exact guarded source-schema target and translated a source proof that
uses the same axiom twice. The source rewrite used 5 nodes, target
translation 8, conditional wrapper 9 and final cut 3. The final external
context was empty.

The Replacement graph's IDs, dependency counts and per-node visits agree
with all seven earlier split receipts. The completed proof covers the
fixed relation

\[
 \varphi(y,x)=\forall z\,(x\in z\longrightarrow y\in z).
\]

This relation remains equivalent to equality in a singleton-closed
class. Its role is to exercise unbounded universal counterexample
transport and the two-parameter reflection interface. General schema
coverage has its own proof and resource obligations.

## Reproduction

The local runs used Node `v24.22.3`, a 6 GiB V8 heap cap and a 600-second
process timeout. Timings and memory are observations from this execution
environment. The deterministic receipts contain the proof counts and
exact-target results.

```sh
node --max-old-space-size=6144 research/ace/unbounded_replacement_replay.mjs full > /tmp/ace-s-full.json
diff -u research/ace/unbounded_replacement_full_receipt.json /tmp/ace-s-full.json
node --max-old-space-size=6144 research/ace/modular_unbounded_replay.mjs > /tmp/ace-q-unbounded.json
diff -u research/ace/modular_unbounded_receipt.json /tmp/ace-q-unbounded.json
```

[full_replay_provenance.json](full_replay_provenance.json) records SHA-256
hashes for all 32 original ACE JavaScript modules and the pinned L
formula. The source bytes matched the stated commit. The checker rules
and L definition retain those bytes in this change.

## Prior CI evidence

The earlier full Separation replay had already succeeded in
[ACE run 45596235187, job 139142926505](https://github.com/patrickdugan/MathCan/actions/runs/45596235187/job/139142926505).
Its PR head was `f7a6b42eaf9c7b4f64a60832eb033ea607626a85` and GitHub
tested merge commit `509a0d95cf751253cd401e17621256b3e44636a6`.
All 42 jobs passed. The full Separation step took 69 seconds with
Node `v22.23.5`; its JSON receipt equals the new local receipt.

The exact-head ACE run at `0456b598` was queued when inspected.
The local results above supply completed evidence for the full graph at
that source commit. The updated workflow compares both complete replays
against the measured deterministic receipts on future runs.

## Scope carried forward

The executed checker accepts the complete modular derivations for these
fixed instances. Its semantic soundness remains an external obligation.
The remaining path through constructible well-ordering, internal Choice,
uniform coding adequacy and native Lean/RH translation is recorded in
[ACE03T_CONSTRUCTIBLE_WELL_ORDER.md](ACE03T_CONSTRUCTIBLE_WELL_ORDER.md).

Paid authoring compute: $0.
