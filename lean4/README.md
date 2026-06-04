# Rado Numbers for x + by = bz - Lean 4 Formalization

Lean 4 + Mathlib formalization for the paper
*On Rado Numbers for x + by = bz: The b^k Pattern and a Threshold
Conjecture*.

The formalization covers the lower bound, the k=2 theorem, the
hybrid k=3, b=3 theorem, the Combined-G*-Tree route for k=4, b=3,
the Distance Pair Lemma SAT slab, the R_5(3) breakdown results, the
backward tower reduction, and the threshold-conjecture statement.

## Build

```bash
lake build
lake env lean RadoNumbers/AxiomAudit.lean
```

The toolchain is pinned by `lean-toolchain`.

## Current Trust Split

`RadoNumbers/AxiomAudit.lean` is the live trust surface. The current
paper-level split is:

| Result | Dependency class |
| --- | --- |
| `thm_lower` | Lean kernel + Mathlib axioms only |
| `thm_k2` | Lean kernel + Mathlib axioms only |
| `thm_k3b3` | Lean kernel + Mathlib axioms only |
| `thm_k4b3` | SAT atom `lem_gstartree` |
| `thm_sat` | SAT atom `lem_keypair_sat` |
| `thm_r5_243` | SAT atom `r5_witness_valid_sat` |
| `thm_r5_296` | SAT atom `r5_296_sat`, backed by public witness JSON |
| `rado_b3_backward_tower` | inherits the R_5(3) witness base case |
| `rado_backward_tower_general` | kernel-pure conditional reduction |

The threshold conjecture is a `def : Prop`, not an asserted theorem.

## Main Files

| File | Paper component |
| --- | --- |
| `RadoNumbers/Basic.lean` | Core definitions: Rado triples, valid colorings, lower/upper bound predicates |
| `RadoNumbers/LowerBound.lean` | b-adic lower bound `R_k(b) >= b^k` |
| `RadoNumbers/K2.lean` | Color compression route and `R_2(b) = b^2` |
| `RadoNumbers/K3B3.lean` | Kernel-checked `R_3(3) = 27` route |
| `RadoNumbers/K4B3.lean` | G* structure, SAT atom, and `R_4(3) = 81` |
| `RadoNumbers/SAT.lean` | Distance Pair Lemma SAT atom and verified slab theorem |
| `RadoNumbers/Breakdown.lean` | `R_5(3) > 243` Lean base witness and `R_5(3) > 296` public witness audit atom |
| `RadoNumbers/General/RadoLift.lean` | Lift lemma and backward tower reduction |
| `RadoNumbers/Threshold.lean` | Threshold conjecture statement |
| `RadoNumbers/AxiomAudit.lean` | Per-theorem axiom audit |
| `RadoNumbers/Ledger.lean` | Typed ledger for theorem and atom status |

## Public Evidence Links

The corresponding SAT scripts and JSON artifacts live one directory
above this Lean package:

```text
../src/verify_gstar_tree.py
../src/verify_dpl_paper_slab.py
../src/verify_R5_witness.py
../src/generate_R5_296_witness.py
../data/results/gstar_tree_verification.json
../data/results/dpl_paper_slab_verification.json
../data/results/R5_witness_296.json
../data/results/R5_witness_243.json
```

## License

See `LICENSE`.
