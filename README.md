# Erdős #74: bounded bipartite defect and coloring

How slowly can the distance from bipartite grow among finite subgraphs of a
graph with infinite chromatic number? This repository organizes Jared Wilder's
Lean proof of the bounded-defect obstruction, its definitions and audit logs.

For a graph `G`, let `d_G(n)` be the largest, over its finite `n`-vertex
subgraphs, of the minimum number of edges that must be deleted to make the
subgraph bipartite. The main formal statement is

```text
(for every n, d_G(n) ≤ B)  ⇒  G is colorable with 2^(B+1) colors.
```

Consequently infinite chromatic number forces unbounded finite-subgraph
bipartite defect. This is the rate-free obstruction: it does not construct
graphs for arbitrarily slowly diverging prescribed defect bounds.

## Proof and scope

The proof first colors each finite subgraph: start from a bipartite graph and
put back at most `B` deleted edges, doubling the color budget per edge. Graph
coloring compactness then gives a coloring of `G`. The numerical bound is
convenient for this proof and is not claimed sharp. The source labels the
mathematical result classical folklore; no novelty claim is made here.

The corollary excluding a bounded prescribed function is unconditional. The
separate `erdos74_hypothesis_sharp` statement assumes the function is monotone
when converting failure to tend to infinity into boundedness.

**Finite vertices are essential in these definitions.** Lean's `Set.ncard`
returns zero for an infinite set. The source supplies a complete-graph
counterexample showing how an unrestricted edge-deletion definition can
report zero for an infinite non-bipartite graph. The actual `d_G(n)` definition
includes a finite-vertex condition, and the zero-defect/bipartite equivalence
is stated with that condition.

## Reading map and verification

| File | Role |
|---|---|
| [Attack01.lean](research/lean/Attack01.lean) | Definitions, main theorem, corollaries and `ncard` calibration |
| [Build log](research/receipts/Attack01.log) | Historical compilation output |
| [Axiom audit](research/receipts/Audit01.log) | 16 named historical axiom checks |
| [Terminal record](research/TERMINAL.json) | Source hash, toolchain, proof boundary and historical assessment |

```sh
python verification/verify_source.py
```

The command checks byte identity with the pinned public source. The source
SHA-256 matches the historical terminal record. Its Lean environment was
`v4.31.0-rc1`, with Mathlib `919544d4309104b3f19724b0e6e48c701d27948f`;
the recorded build succeeded and the audit lists only standard Lean axioms.
This promotion did not rebuild Lean. Historical literature assessments in
the terminal record are preserved as dated source material.

## Provenance

All four research files are exact copies from the
[campaign archive](https://github.com/jaredwilder/erdos-campaign-archive).
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) pins the source commit and records
original paths, Git blobs, sizes and SHA-256 hashes. This focused repository
provides the mathematical reading map; the archive retains the original record.

Author: Jared Wilder. Campaign: 2026-09-05. Focused release: 2026-09-13.
License: inherited Apache-2.0; see [LICENSE](LICENSE).
