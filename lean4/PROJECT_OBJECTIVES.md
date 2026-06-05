# Project Objectives - Threshold Conjecture Roadmap

This public note summarizes the mathematical direction of the Lean package
for the paper *On Rado Numbers for x + by = bz: The b^k Pattern and a
Threshold Conjecture*.

## Main Conjecture

For integers `b >= 2` and `k >= 1`, let `R_k(b)` be the k-color Rado
number for `x + by = bz`. The working conjecture is

```text
R_k(b) = b^k  if and only if  k <= 2(b - 1).
```

The Lean code records this as a proposition and separates the analytic
arguments from the finite SAT-backed atoms used in the paper.

## Current Evidence

| Result family | Status |
| --- | --- |
| Lower bound `R_k(b) >= b^k` | Lean-formalized analytic proof |
| `R_2(b) = b^2` for all `b >= 2` | Lean-formalized analytic proof |
| `R_3(3) = 27` | Lean-formalized analytic route |
| `R_4(3) = 81` | Analytic reduction plus a SAT-backed `G*` atom |
| Distance Pair Lemma slab | SAT-backed for `k=3, b=3..10` and `k=4, b=3..5` |
| `R_5(3) > 296` | Public witness JSON plus verifier |
| Backward tower reduction | Lean-formalized conditional reduction |

The conjecture itself is not claimed as a theorem.

## Reproducibility Boundary

The paper-level trust split is visible from:

```bash
lake env lean RadoNumbers/AxiomAudit.lean
```

SAT-backed components are represented as named assumptions in Lean and are
backed by public Python verifiers and JSON artifacts in the repository root:

```text
../src/verify_gstar_tree.py
../src/verify_dpl_paper_slab.py
../src/verify_R5_witness.py
../data/results/gstar_tree_verification.json
../data/results/dpl_paper_slab_verification.json
../data/results/R5_witness_296.json
```

## Next Mathematical Directions

The most useful extensions are:

1. Analytic replacement for the SAT-backed Distance Pair Lemma slab.
2. Analytic replacement for the Combined-G*-Tree Lemma.
3. Exact determination of `R_5(3)`.
4. New computations at the first untested threshold boundary, especially
   `R_6(4)` and `R_7(4)`.

Any new Lean theorem should either reduce a paper-level SAT dependency,
support the threshold conjecture, or clarify the boundary between analytic
proof and finite verification.
