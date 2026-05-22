/-
  RadoNumbers/General/ThresholdConjecture.lean

  Statement of the Rado THRESHOLD CONJECTURE for x + by - bz = 0.

  Conjecture (project's central claim):
    For all b ≥ 2 and 1 ≤ k ≤ 2(b-1), the Rado number R_k(b) equals b^k exactly.

  The lower bound R_k(b) ≥ b^k is PROVEN (via valuation coloring).
  The upper bound R_k(b) ≤ b^k for k ≤ 2(b-1) is the deep direction.

  This file STATES the conjecture as a Prop (real mathematical statement,
  no := True trick). Specific cases (e.g., R_3(3) = 27) reduce to instances
  of this conjecture.
-/

import RadoNumbers.General.Bridge

namespace RadoNumbers.General

/--
  **The Rado Threshold Conjecture** for b-adic equations.

  For all b ≥ 2 and 1 ≤ k ≤ 2(b-1), the Rado number of equation
  x + b·y - b·z = 0 with k colors is EXACTLY b^k.

  This is the CENTRAL CONJECTURE of the project. The lower bound
  R_k(b) ≥ b^k is proven (`not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one`).
  The upper bound is the open piece (= Pillar 3 specialization).

  Note: STATING the conjecture as a Prop is real mathematical content,
  not a `:= True` placeholder. Proving it is open work (multi-year
  Mathlib infra direction).
-/
def ThresholdConjecture : Prop :=
  ∀ b k : ℕ, 2 ≤ b → 1 ≤ k → k ≤ 2 * (b - 1) →
    IsRadoNumber (bAdicEquation b) k (b ^ k)

/--
  **R_3(3) = 27 from Threshold Conjecture**.

  Direct specialization to (b, k) = (3, 3). Since 3 ≤ 2(3-1) = 4 satisfies
  the threshold condition, the conjecture applied gives R_3(3) = 27.
-/
theorem isRadoNumber_radoEq_3_27_from_thresholdConjecture
    (h : ThresholdConjecture) :
    IsRadoNumber radoEq_3 3 27 := by
  have := h 3 3 (by omega) (by omega) (by omega)
  -- this : IsRadoNumber (bAdicEquation 3) 3 (3^3) = IsRadoNumber radoEq_3 3 27.
  show IsRadoNumber (bAdicEquation 3) 3 27
  have h27 : (3 : ℕ)^3 = 27 := by decide
  rw [← h27]
  exact this

/--
  **Threshold Conjecture for (3, 3) ⟺ Pillar 3** (upper bound only).

  Since lower bound R_3(3) ≥ 27 is proven, the conjecture for (3, 3)
  is equivalent to the Pillar 3 upper bound.
-/
theorem thresholdConjecture_3_3_iff_pillar3 :
    IsRadoNumber radoEq_3 3 27 ↔ IsKPartitionRegularAt radoEq_3 3 27 :=
  isRadoNumber_radoEq_3_27_iff_pillar3

/--
  **THRESHOLD DICHOTOMY**: for any (b, k) with b ≥ 2 and k ≥ 1,
  one of two regimes holds (CONJECTURALLY):
    - **Regime A** (threshold): k ≤ 2(b-1) → R_k(b) = b^k exactly.
    - **Regime B** (breakdown): k > 2(b-1) → R_k(b) > b^k.

  This Prop captures the FULL threshold conjecture as a single dichotomy
  statement. It STRENGTHENS `ThresholdConjecture` by adding the breakdown
  direction.

  Status: Both directions open in general. Specific instances proven:
  - Regime A: (b, 1) for b ≥ 2 unconditional, (b, 2) for b ≥ 2 unconditional,
    (b, 3) for 3 ≤ b ≤ 10 and (b, 4) for 3 ≤ b ≤ 5 via lem_keypair_sat,
    (3, 3) via lem_compress3_general, (3, 4) via lem_gstartree.
  - Regime B: (2, k) for k ∈ {3..8} kernel-pure, (3, 5) via r5_*_sat.
-/
def ThresholdDichotomy : Prop :=
  ∀ b k : ℕ, 2 ≤ b → 1 ≤ k →
    (k ≤ 2 * (b - 1) → IsRadoNumber (bAdicEquation b) k (b ^ k)) ∧
    (2 * (b - 1) < k → ¬ IsKPartitionRegularAt (bAdicEquation b) k (b ^ k))

/--
  **ThresholdDichotomy ⇒ ThresholdConjecture**: the dichotomy implies
  the conjecture (= upper bound side only).
-/
theorem thresholdConjecture_of_dichotomy (h : ThresholdDichotomy) :
    ThresholdConjecture := by
  intro b k hb hk hbk
  exact (h b k hb hk).1 hbk

/--
  **R_3(3) = 27 from scratch reduction**: IsRadoNumber radoEq_3 3 27 is
  equivalent to IsKPartitionRegularAt radoEq_3 3 27.

  This is the KERNEL-PURE FROM-SCRATCH reduction (using the new
  isRadoNumber_iff_isKPartitionRegularAt_from_scratch via valuation
  coloring lower bound). Replaces the previous
  isRadoNumber_radoEq_3_27_iff_pillar3 which used project bridge for
  lower bound.
-/
theorem isRadoNumber_radoEq_3_27_iff_pillar3_from_scratch :
    IsRadoNumber radoEq_3 3 27 ↔ IsKPartitionRegularAt radoEq_3 3 27 := by
  show IsRadoNumber (bAdicEquation 3) 3 27 ↔ IsKPartitionRegularAt (bAdicEquation 3) 3 27
  have h := isRadoNumber_iff_isKPartitionRegularAt_from_scratch 3 3 (by omega) (by omega)
  have h27 : (3 : ℕ) ^ 3 = 27 := by decide
  rw [h27] at h
  exact h

/--
  **R_3(3) = 27 from CompressionHyp 3 3 + OmittedPairHyp 3 3** —
  FROM-SCRATCH version (no project bridge for lower bound).

  This is the FINAL kernel-pure conditional reduction for R_3(3) = 27.
  Given the two open per-level hypotheses at j = 3 (which are SAT-verified
  in the project), R_3(3) = 27 follows kernel-pure end-to-end via:
    - The kernel-pure threshold equivalence (lower bound automatic).
    - The conditional threshold capstone (cascade reduction at k=3).
    - The k=2 hypotheses bridged from project (also kernel-pure).

  COMPARE with isRadoNumber_radoEq_3_three_27_from_hypotheses (in Bridge.lean,
  uses project bridge for lower bound). This version uses ONLY General/
  infrastructure for the lower bound side.

  THIS IS THE SHARPEST KERNEL-PURE STATEMENT of what remains open for
  R_3(3) = 27: prove CompressionHyp 3 3 and OmittedPairHyp 3 3 kernel-pure
  (multi-month structural enumeration).
-/
theorem isRadoNumber_radoEq_3_27_from_hypotheses_from_scratch
    (hComp : RadoNumbers.CompressionHyp 3 3)
    (hOmit : RadoNumbers.OmittedPairHyp 3 3) :
    IsRadoNumber radoEq_3 3 27 := by
  rw [isRadoNumber_radoEq_3_27_iff_pillar3_from_scratch]
  -- Need IsKPartitionRegularAt radoEq_3 3 27 = IsKPartitionRegularAt (bAdicEquation 3) 3 27.
  show IsKPartitionRegularAt (bAdicEquation 3) 3 27
  -- Apply conditional threshold via cascade.
  have h := isRadoNumber_bAdicEquation_threshold_conditional 3 (by omega) 3 (by omega)
    (fun j hj2 hj3 => by
      interval_cases j
      · exact compressionAndOmittedPair_k2 3 (by omega)
      · exact ⟨hComp, hOmit⟩)
  have h27 : (3 : ℕ) ^ 3 = 27 := by decide
  rw [h27] at h
  exact h.1

/-! ### §47. Threshold conjecture FULLY PROVEN for k ≤ 2 (universal). -/

/--
  **THRESHOLD CONJECTURE HOLDS FOR k ≤ 2**: for any b ≥ 2 and any k with
  1 ≤ k ≤ 2, the Rado number R_k(bAdicEquation b) = b^k exactly.

  UNCONDITIONAL, fully kernel-pure (depends only on Lean kernel axioms,
  no project axioms). Combines:
  - k = 1: `isRadoNumber_bAdicEquation_one` (b ≥ 2 → R_1(b) = b).
  - k = 2: `isRadoNumber_bAdicEquation_two_universal` (b ≥ 2 → R_2(b) = b^2).

  This is the LARGEST proven sub-range of the threshold conjecture
  currently available kernel-pure. The remaining range k ∈ [3, 2(b-1)]
  is still open for kernel purity (depends on Cat 2 SAT axioms or
  conditional CompressionHyp/OmittedPairHyp).
-/
theorem thresholdConjecture_holds_for_k_le_2 :
    ∀ b k : ℕ, 2 ≤ b → 1 ≤ k → k ≤ 2 →
    IsRadoNumber (bAdicEquation b) k (b ^ k) := by
  intro b k hb hk1 hk2
  interval_cases k
  · -- k = 1: R_1(b) = b^1 = b.
    have h := isRadoNumber_bAdicEquation_one b hb
    have hpow : b ^ 1 = b := pow_one b
    rw [hpow]
    exact h
  · -- k = 2: R_2(b) = b^2.
    exact isRadoNumber_bAdicEquation_two_universal b hb

/--
  **R_3(3) = 27 from ThresholdDichotomy** — convenient direct corollary.

  Composes thresholdConjecture_of_dichotomy with the central case to
  give R_3(3) = 27 directly from the dichotomy assumption.
-/
theorem isRadoNumber_radoEq_3_27_from_dichotomy
    (h : ThresholdDichotomy) :
    IsRadoNumber radoEq_3 3 27 :=
  isRadoNumber_radoEq_3_27_from_thresholdConjecture
    (thresholdConjecture_of_dichotomy h)

end RadoNumbers.General
