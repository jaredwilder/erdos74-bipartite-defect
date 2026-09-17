# Erdős #74 — bipartite defect versus chromatic number

For a graph `G`, let `d_G(n)` be the largest, over its finite `n`-vertex subgraphs, of the minimum number of edges that must be deleted to make the subgraph bipartite.

The main Lean theorem in this repository is

```text
(for every n, d_G(n) ≤ B)  ⇒  G is colorable with 2^(B+1) colors.
```

Therefore every graph of infinite chromatic number has unbounded finite-subgraph bipartite defect.

## Proof idea

For each finite subgraph, delete at most `B` edges to obtain a bipartite graph. Start with a 2-coloring of that graph and restore the deleted edges one at a time, doubling the available color palette at each step. Graph-coloring compactness then gives a coloring of the full graph.

The bound `2^(B+1)` is sufficient for this argument; no sharpness claim is made.

A separate formal calibration is important here: the definition of `d_G(n)` explicitly restricts to finite vertex sets. Without that condition, Lean's `Set.ncard` behavior on infinite sets can make an unrestricted deletion count degenerate. The repository includes a complete-graph example exposing that issue.

## Files

| File | Role |
|---|---|
| [`Attack01.lean`](research/lean/Attack01.lean) | Definitions, main theorem, corollaries, and finite-cardinality calibration |
| [`Attack01.log`](research/receipts/Attack01.log) | Recorded build output |
| [`Audit01.log`](research/receipts/Audit01.log) | Axiom checks for 16 named declarations |
| [`TERMINAL.json`](research/TERMINAL.json) | Toolchain and source record |

## Verification

```sh
python verification/verify_source.py
```

The source hash matches the recorded terminal receipt. The historical environment was Lean `v4.31.0-rc1` with Mathlib `919544d4309104b3f19724b0e6e48c701d27948f`; the recorded build succeeded and the axiom audit lists only standard Lean axioms.

The rate-free obstruction above is proved. The stronger problem of constructing graphs whose defect diverges according to an arbitrarily slowly growing prescribed rate is not resolved here.

Author: Jared Wilder. License: Apache-2.0.
