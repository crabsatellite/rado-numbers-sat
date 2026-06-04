# Project Objectives — Threshold Conjecture & Paper Upgrade

**唯一目标 / Sole Objective**:
> Prove the **Threshold Conjecture** (Li 2026, Conjecture 1)
> and use this to **upgrade the paper**.

This document is the authoritative project goal. **Do not forget**.

---

## The Threshold Conjecture

From `paper/latex/rado_numbers.tex`, Conjecture 1 (`conj:threshold`):

$$
R_k(b) = b^k \quad \text{if and only if} \quad k \le 2(b - 1)
$$

for all integers $b \ge 2$ and $k \ge 1$, where $R_k(b)$ is the $k$-color
Rado number for the equation $x + by = bz$.

---

## What this project is **NOT** about

- ❌ NOT about verifying SAT proofs in Lean.
- ❌ NOT about proving $R_4(3) \le 81$ specifically (this is a *boundary instance*, not the goal).
- ❌ NOT about replacing SAT axioms with kernel-pure proofs as an end in itself.
- ❌ NOT about LRAT certificate replay, RUP checker infrastructure, etc.

SAT is a **tool**, not a target. LRAT/RUP infrastructure was R401-R403
exploratory work; it is **archived** and does not service the Conjecture.

---

## What this project **IS** about

✅ Prove the Threshold Conjecture, in part or in whole.
✅ Upgrade the paper with new theorems, structural insights, or data.
✅ Use Lean as a **research assistant** to explore proof structure.
✅ Use Mathlib b-adic valuation infrastructure to accelerate paper-level proofs.

Every Lean work item must have a clear mapping to a **paper section upgrade**.

---

## Logical structure of the Conjecture

### Forward (⇒): $k \le 2(b-1) \Rightarrow R_k(b) = b^k$

Requires matching upper bound $R_k(b) \le b^k$ in the safe zone.

| (b, k) | Status |
|--------|--------|
| All (b, k) with k ≤ 2 | ✓ Theorem 2 (Color Compression, analytic) |
| (3, 3), (3, 4) | ✓ Theorems 3, 4 (hybrid analytic-SAT) |
| (4, 1..4), (5, 1..4) | ✓ Theorem 5 (SAT, Distance Pair Lemma) |
| **(b, k) for b ≥ 4, k ∈ {5, ..., 2(b-1)}** | **❌ ALL UNKNOWN** |

### Backward (⇐): $k > 2(b-1) \Rightarrow R_k(b) > b^k$

Requires constructive mono-free $k$-coloring of $\{1, \ldots, b^k\}$.

| (b, k) | Status |
|--------|--------|
| (2, 3), (2, 4..8) | ✓ Theorem 6 boundaries + Breakdown.lean |
| (3, 5) | ✓ Theorem 6 (constructive 5-coloring on [1, 296]) |
| **(b, k) for b ≥ 3 beyond boundary** | **❌ MOSTLY UNKNOWN** |

---

## Priority work items (ranked by paper-upgrade impact)

### Priority A — Mathematical breakthroughs

| ID | Task | Paper § upgraded | Lean impact |
|----|------|-----------------|-------------|
| **A1** | Color Compression analytic for k=3, general b | §7 | `K3General.lean` |
| **A2** | Distance Pair Lemma analytic for general (b, k≤2(b-1)) | §7 master | `SAT.lean`, `DPLStructure.lean` |
| **A3** | R₃(b) = b³ for all b ≥ 3 (kernel-pure) | §5 | `K3General.lean` |
| **A4** | Sharp R₅(3) = 297 | §6 | `Breakdown.lean` |
| **A5** | Threshold forward direction unified theorem | NEW § | new file |
| **A6** | Constructive witness for k > 2(b-1) general | §6, new § | new file |

### Priority B — Computational extension (data for Conjecture)

| ID | Task | Paper § | Resource |
|----|------|---------|----------|
| **B1** | Compute R₆(4) = 4⁶ (boundary at b=4) | §8 | cluster |
| **B2** | Compute R₇(4) > 4⁷ (breakdown at b=4) | §8 | cluster |
| **B3** | Sweep R_k(5) for k ∈ {5..9} (boundary at b=5) | §8 | cluster |
| **B4** | Sweep R_k(b) for b ∈ {6..10}, k ≥ 4 | Table 1 | cluster |

### Priority C — Lean rigor (paper reproducibility upgrade)

| ID | Task | SAT axiom replaced |
|----|------|---------------------|
| **C1** | Replace `r5_witness_valid_sat` with `decide` enumeration | `Breakdown.lean` |
| **C2** | Replace `lem_compress3_general` with analytic | `K3General.lean` |
| **C3** | Replace `lem_gstartree` with analytic G* proof | `K4B3.lean` |
| **C4** | Replace `lem_keypair_sat` with analytic DPL | `SAT.lean` |

### Priority D — DEPRIORITIZED

Proof-certificate replay infrastructure (R401-R403) is optional future
reproducibility work.  The paper currently relies on recorded SAT
instances, solver configuration, witnesses, and result manifests; do
not describe external proof certificates unless they are generated and
checked as public artifacts.  Replay verification is not a current Lean
goal.

---

## File classification

### 🟢 Layer 0 — Core infrastructure (keep)
- `Basic.lean`, `LowerBound.lean`, `BasicResults.lean`, `BAdicEquation.lean`

### 🟢 Layer 1 — Paper theorems (keep, active work surface)
- `K2.lean` — Theorem 2 (R₂(b)=b² all b)
- `K3B3.lean` — Theorem 3 (R₃(3)=27)
- `K3General.lean` — k=3 general b attack line
- `K4B3.lean` — Theorem 4 (R₄(3)=81)
- `SAT.lean` — Theorem 5 + Distance Pair Lemma
- `Breakdown.lean` — Theorem 6 (R₅(3)>243, 296)
- `Threshold.lean` — Conjecture 1 + verified instances

### 🟡 Layer 2 — Supporting (keep, indirect)
- `DPLStructure.lean`, `Pillar3Structural.lean`, `Foundational.lean`,
  `Ledger.lean`, `AxiomAudit.lean`, `PartitionRegular.lean`,
  `ColumnsCondition.lean`, `General/ThresholdConjecture.lean`

### 🔴 Layer 3 — Archive (does NOT serve the Conjecture)
- `General/Bridge.lean` (12,792 lines, R313-R392 single-triple Branch II case-by-case at n=81)
- `General/R396MUS_Pilot.lean`
- `General/R398ResolutionDemo.lean`
- `General/R399ResolutionReplayDemo.lean`
- `General/R400LRATCheckerToy.lean`
- `General/R401RUPChecker.lean`
- `General/R402LRATAddStep.lean`
- `General/R403LRATProofReplay.lean`
- `General/R403TraceSliceDemo.lean`

These files are kept for historical reference but are **not part of the
Conjecture proof line**. They explored an alternate path (SAT-via-LRAT-replay
verification) that does not upgrade the paper.

---

## Decision rule for new Lean work

Before adding ANY new Lean file or theorem, answer:

1. **Which paper section does this upgrade?** (Cite by name, e.g. "§5 Thm 5", "§7 DPL", "new §9 forward direction")
2. **Which Priority bucket** (A/B/C) does it belong to?
3. **Does it advance the Threshold Conjecture proof?** (forward, backward, evidence)

If the answers are vague or none, **do not write the file**.

---

## Current status (as of last audit)

- Paper: 6 theorems proved + 1 conjecture stated.
- Lean: All 6 theorems represented; 5 SAT-verified axioms (Cat 2).
- Threshold Conjecture: STATED in Lean, **NOT PROVEN**.
- Archive: ~14,000 lines (Bridge.lean + R396-R403 series).

## Next action requires user input

Choose one Priority A / B / C task. Recommended:
- **A3** (R₃(b) = b³ for all b, kernel-pure) — concrete, achievable, upgrades §5.
- **A2** (Distance Pair Lemma analytic) — highest impact, very hard.
- **B1** (R₆(4) computation) — needs compute resources but gives new data point.

Then we focus solely on that work item until it lands in the paper.
