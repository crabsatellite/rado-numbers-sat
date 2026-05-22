# Rado Numbers for x + by = bz — Lean 4 Formalization

A Lean 4 + Mathlib formalization of the multicolor Rado numbers
R_k(b) for the equation x + by = bz, accompanying

> Li, Alex Chengyu. *On Rado Numbers for x + by = bz: The b^k
> Pattern and a Threshold Conjecture.* 2026.

The formalization machine-checks the lower bound R_k(b) >= b^k, the
upper-bound theorems, the independent-verification theorem, the b^k
pattern breakdown, and the statement of the threshold conjecture.

## Building

The build requires the Lean toolchain pinned in
[`lean-toolchain`](lean-toolchain) (installed automatically by
[`elan`](https://github.com/leanprover/elan)).

```bash
# Fetch the prebuilt Mathlib cache (run before `lake build`,
# otherwise Mathlib is recompiled from source).
lake exe cache get

# Build the project.
lake build
```

`lake build` completes with no errors. It emits some benign
Mathlib-style linter warnings, as is usual for a Mathlib-based
project.

## Axioms

Every paper-internal deduction is a genuine Lean 4 theorem. The
analytic core is kernel-pure: the lower bound, the k=2 theorem, the
b=3 upper-bound theorem, the cascade infrastructure, and the
backward-direction lift all depend only on the Lean kernel axioms
`[propext, Classical.choice, Quot.sound]`.

The formalization uses exactly **5 axioms**, all external atoms
verified by SAT solving (with DRAT-certifiable proofs):

| Axiom | Role |
|-------|------|
| `lem_compress3_general` | k=3 color-compression hypothesis, b in {3,...,10} |
| `lem_gstartree` | Combined-G*-Tree Lemma (boundary case R_4(3) = 81) |
| `lem_keypair_sat` | Distance Pair Lemma |
| `r5_witness_valid_sat` | validity of the explicit 243-entry witness coloring |
| `r5_296_sat` | the stronger bound R_5(3) > 296 |

Everything else reduces to the kernel. The SAT-verified theorems
(`thm_k3b3`, `thm_k4b3`, `thm_sat`, `thm_r5_243`, `thm_r5_296`)
depend additionally on the relevant axioms above.

### Axiom audit

```bash
lake env lean RadoNumbers/AxiomAudit.lean
```

[`RadoNumbers/AxiomAudit.lean`](RadoNumbers/AxiomAudit.lean) prints
`#print axioms` for every paper-level theorem, so the per-theorem
axiom dependencies can be inspected directly.
[`RadoNumbers/Ledger.lean`](RadoNumbers/Ledger.lean) carries a typed
record of every axiom and every closed top-level result.

## File structure

The `RadoNumbers/` directory contains:

| File | Contents |
|------|----------|
| `Basic.lean` | Core definitions: b-adic valuation, Rado triple x + by = bz, valid k-coloring, monochromatic-solution avoidance, Rado-number bounds |
| `LowerBound.lean` | The lower bound R_k(b) >= b^k via the valuation witness coloring |
| `K2.lean` | The Color Compression Lemma and R_2(b) = b^2 for all b >= 2 |
| `K3B3.lean` | R_3(3) = 27 |
| `K4B3.lean` | The boundary case R_4(3) = 81 (definitions of the obstruction graphs G27, Gext, Gstar) |
| `K3General.lean` | The k=3 color-compression analysis for general b |
| `SAT.lean` | The Distance Pair Lemma and the independent-verification theorem for R_3(b) and R_4(b) over the SAT-covered ranges |
| `Breakdown.lean` | The b^k pattern breakdown: R_5(3) > 243 (explicit witness) and R_5(3) > 296 |
| `DPLStructure.lean` | Structural analysis of the Distance Pair Lemma mechanism (DPL window structure, pigeonhole bound) |
| `Foundational.lean` | Universal structural lemmas for mono-free colorings (self-loop, distance-pair, triple-distinct-color) |
| `Ledger.lean` | Typed gap ledger over axioms and closed results |
| `Pillar3Structural.lean` | Structural framework for the analytic route to R_3(3) <= 27 |
| `Threshold.lean` | The threshold conjecture R_k(b) = b^k iff k <= 2(b-1), stated as a `def : Prop` with verified instances collated |
| `AxiomAudit.lean` | Trust audit: `#print axioms` for every paper-level theorem |
| `General/` | A Mathlib-style framework for partition regularity of arbitrary linear equations over Z, the b-adic equation as an instance, the bridge to the project's predicates, and the backward-direction Rado Lift Lemma |

## License

[MIT](LICENSE) (c) 2026 Alex Li.
