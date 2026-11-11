# TOE transcript intake

Six episodes have source-linked records in [EPISODE_INDEX.json](EPISODE_INDEX.json), with public transcript URLs, dates, provenance and timestamped topics. Full publisher-owned or third-party machine transcript text is intentionally kept out of this public repository.

Machine transcripts often misrecognize names and mathematical terminology; quoted scientific claims must be checked against original audio and primary papers. The interviews are used as *research prompts* rather than as mathematical evidence.

The included local caption importer accepts separately obtained authorized SRT/VTT files and writes SHA-256 provenance and timestamped segment JSONL in the git-ignored research/toe/private/ directory.

```sh
python -m research.toe.transcript_intake --list
python -m research.toe.transcript_intake --episode-id toe-ravera-2026-09-14 --input /path/to/authorized-caption.vtt --permission-basis 'authorized local research'
```

Research order: Bianconi on entropy and dynamical cosmology; Ravera on gauge relationality; Gorard on discrete geometry; Verlinde on emergent gravity; Mannheim on conformal cosmology; Turok on indefinite metric/Hilbert assumptions. Each has distinct field equations and experimental assumptions.
