# Source record

## Supplied manuscript

Title: *Prescribing cycles in a Collatz-like map by quadratic reciprocity*.
Subtitle: *Finite certificates, composite parameters, and an exact cycle census*.
The first supplied page says "Research manuscript" and is dated 25 November 2026.
No author is named on that page. This package attributes the finite-core
lemma, original relative-sign construction, all-moduli theorem and original
137-cycle census to that supplied manuscript. It makes no novelty claim for
the extensions. The seven image hashes appear in `data/source_manifest.json`.

| Image | Manuscript content |
| --- | --- |
| HX93xbDWQAA2G2i.jpg | Title, abstract and finite odd core |
| HX93ybiWEAAHRSM.jpg | Elementary examples and local characters |
| HX93zqqWIAAqGDP.jpg | Theorem2 and relative-sign cycle lower bound |
| HX931-DXQAAqa3C.jpg | Theorem4: all periodic forward-closed sets |
| HX933HEWgAAzfkJ.jpg | Complete reference census and quotient counts |
| HX9347gX0AAuAVs.jpg | First-step certificates and related maps |
| HX936GfWwAA0Ocr.jpg | Reproducibility, open questions and bibliography |

The manuscript's companion archive was not supplied. The two recovered chat
artifacts are preserved as `legacy/original_census.cpp` and
`data/reference_census.csv`; their hashes match the downloaded versions.
The new formatted C++ census supplies both path traversal and indegree
peeling. Its complete outputs match the reference CSV exactly, and Python
replays the listed cycles through the full map.

## Classical ingredients checked against primary teaching sources

- Ben Lynn, [Quadratic Reciprocity](https://crypto.stanford.edu/pbc/notes/numbertheory/quadrecip.html), Stanford PBC notes. Used for the symmetry of the Legendre symbols when an auxiliary prime is 1 modulo 4.
- Andrew V. Sutherland, [MIT 18.785, Fall 2021 lecture notes](https://math.mit.edu/classes/18.785/2021fa/lectures.html), lecture 18, Theorem 18.1; [full MIT notes](https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_full_lec.pdf). Used for infinitely many primes in each coprime arithmetic progression.
- Lean 4.35.0, repository toolchain pin. Local kernel binary reports commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; the file imports `Init` and prints transitive axioms for 19 declarations.

The branch-count lattice proof, sharper prefix-decoder argument and absolute
sign variation are derived in `MATHEMATICS.md`. Empirical cycle population
claims point to the scripts and complete receipts in this package.
