/-
  RadoNumbers/Threshold.lean

  Conjecture `conj:threshold` ($R_k(b) = b^k \iff k \le 2(b-1)$).
  Companion to Li 2026 "On Rado Numbers for $x + by = bz$".

  The paper proposes a precise boundary for the $b^k$ pattern:
  $R_k(b) = b^k$ if and only if $k \le 2(b-1)$. Evidence:

  * $b = 2$: threshold $2(b-1) = 2$. $R_3(2) = 14 > 8 = 2^3$
    (verified, Schur number $S(3)$).
  * $b = 3$: threshold $2(b-1) = 4$. $R_4(3) = 81 = 3^4$ (verified,
    `thm_k4b3`), $R_5(3) > 243 = 3^5$ (verified, `thm_r5_243`).
  * $b \ge 4$: threshold $2(b-1) \ge 6$, untested at boundary.

  Encoding:

  * `RadoThresholdConjecture` — stated as a `def : Prop`, not
    asserted as a theorem. The known instances are derived
    theorems; the bidirectional equivalence at the boundary is the
    Cat 3 phenomenological conjecture atom.

  Note: this file does NOT assert the conjecture. It records its
  statement, the verified instances, and the phenomenological-
  conjecture atomic stipulation.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.K2
import RadoNumbers.K3B3
import RadoNumbers.K4B3
import RadoNumbers.Breakdown
import RadoNumbers.Foundational
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Statement of the threshold conjecture. -/

/-- *The threshold conjecture* (Li 2026, Conjecture
    `conj:threshold`): for all $b \ge 2$ and $k \ge 1$,
    $R_k(b) = b^k$ if and only if $k \le 2(b - 1)$. -/
def RadoThresholdConjecture : Prop :=
  ∀ b k : ℕ, 2 ≤ b → 1 ≤ k →
    (IsRadoNumber b k (b ^ k) ↔ k ≤ 2 * (b - 1))

/-! ### Verified instances. -/

/-- Boundary case for $b = 3$: $R_4(3) = 81$ ($k = 4 = 2(b - 1)$
    is the equality side of the threshold). -/
theorem threshold_b3_k4_boundary : IsRadoNumber 3 4 81 := thm_k4b3

/-- Verified instance for $b = 3, k = 5$: the pattern breaks
    ($k = 5 > 2(b - 1) = 4$). Result: $R_5(3) > 243 = 3^5$. -/
theorem threshold_b3_k5_breaks : RadoNumberAtLeast 3 5 244 := thm_r5_243

/-- Verified instance for $b = 3, k = 5$ stronger: $R_5(3) > 296$. -/
theorem threshold_b3_k5_breaks_strong : RadoNumberAtLeast 3 5 297 := thm_r5_296

/-- General $b \ge 2, k = 2$ instance: $R_2(b) = b^2$. Always
    within the safe zone since $2 \le 2(b - 1) = 2b - 2$ iff
    $b \ge 2$. -/
theorem threshold_k2 (b : ℕ) (hb : 2 ≤ b) : IsRadoNumber b 2 (b ^ 2) :=
  thm_k2 b hb

/-- **** Verified breakdown at $(b, k) = (2, 3)$:
    $R_3(2) > 8 = 2^3$. Threshold predicts breakdown since
    $k = 3 > 2(b - 1) = 2$ for $b = 2$. Established via the
    explicit 3-coloring witness `r3_2_witness` (analytic, kernel-pure;
    no SAT axiom). -/
theorem threshold_b2_k3_breaks : RadoNumberAtLeast 2 3 9 := thm_r3_2_breakdown

/-- **** Verified breakdown at $(b, k) = (2, 4)$:
    $R_4(2) > 16 = 2^4$. Threshold predicts breakdown. Established
    via the explicit 4-coloring witness `r4_2_witness` (analytic,
    kernel-pure; no SAT axiom). -/
theorem threshold_b2_k4_breaks : RadoNumberAtLeast 2 4 17 := thm_r4_2_breakdown

/-- **** Verified breakdown at $(b, k) = (2, 5)$:
    $R_5(2) > 32 = 2^5$. Threshold predicts breakdown. Established
    via the explicit 5-coloring witness `r5_2_witness` (analytic,
    kernel-pure; no SAT axiom). Proof employs the $x = 2d, z = y + d$
    substitution to reduce $32^3 = 32{,}768$ case enumeration to a
    tractable $16 \cdot 32 = 512$. -/
theorem threshold_b2_k5_breaks : RadoNumberAtLeast 2 5 33 := thm_r5_2_breakdown

/-- **** Verified breakdown at $(b, k) = (2, 6)$:
    $R_6(2) > 64 = 2^6$. Threshold predicts breakdown. Established
    via the explicit 6-coloring witness `r6_2_witness` (analytic,
    kernel-pure; no SAT axiom). The block-and-echo construction
    iterates: Round 121 witness + fresh color 5 block + Round 121's
    first 16 positions echoed. -/
theorem threshold_b2_k6_breaks : RadoNumberAtLeast 2 6 65 := thm_r6_2_breakdown

/-- **** Verified breakdown at $(b, k) = (2, 7)$:
    $R_7(2) > 128 = 2^7$. Threshold predicts breakdown. Established
    via the explicit 7-coloring witness `r7_2_witness` (analytic,
    kernel-pure; no SAT axiom). The block-and-echo pattern iterates
    once more: Round 122 witness + fresh color 6 block (32 positions)
    + Round 122's first 32 positions echoed. -/
theorem threshold_b2_k7_breaks : RadoNumberAtLeast 2 7 129 := thm_r7_2_breakdown

/-- **** Verified breakdown at $(b, k) = (2, 8)$:
    $R_8(2) > 256 = 2^8$. Threshold predicts breakdown. Established
    via the explicit 8-coloring witness `r8_2_witness` (analytic,
    kernel-pure; no SAT axiom). Sixth iteration of the block-and-echo
    pattern; built in $\sim 20$ minutes with `maxHeartbeats` at 64M. -/
theorem threshold_b2_k8_breaks : RadoNumberAtLeast 2 8 257 := thm_r8_2_breakdown

/-- **** STRONGER breakdown bound at $(b, k) = (2, 3)$:
    $R_3(2) > 9$ (i.e., $R_3(2) \ge 10$). Improves Round 119's
    $R_3(2) \ge 9$ by exhibiting a mono-free 3-coloring of $\{1, \ldots,
    9\}$ that uses all 3 colors on $\{2, 4, 6\}$ (Round 119's witness
    uses only 2 colors there). Witness: `r3_2_witness_strong`. -/
theorem threshold_b2_k3_breaks_strong : RadoNumberAtLeast 2 3 10 := thm_r3_2_breakdown_strong

/-! ### cumulative breakdown evidence at $b = 2$. -/

/-- **Round 125 — cumulative analytic breakdown evidence at $b = 2$.**

  For each $k \in \{3, 4, 5, 6, 7, 8\}$, the threshold conjecture's
  breakdown direction holds: $R_k(2) > 2^k$. Established via the
  iterated block-and-echo construction (Rounds 119–124), kernel-pure
  throughout, no SAT axioms.

  This constitutes the strongest analytic support to date for the
  threshold conjecture's breakdown direction: six consecutive levels
  $k = 3, 4, 5, 6, 7, 8$ at the smallest $b = 2$.

  Build times grow $\sim 4 \times$ per level; further extension to
  $k \ge 9$ would require either an inductive proof of the
  block-and-echo construction (open) or alternative Lean automation. -/
theorem b2_breakdown_cumulative :
    RadoNumberAtLeast 2 3 9 ∧
    RadoNumberAtLeast 2 4 17 ∧
    RadoNumberAtLeast 2 5 33 ∧
    RadoNumberAtLeast 2 6 65 ∧
    RadoNumberAtLeast 2 7 129 ∧
    RadoNumberAtLeast 2 8 257 :=
  ⟨thm_r3_2_breakdown,
   thm_r4_2_breakdown,
   thm_r5_2_breakdown,
   thm_r6_2_breakdown,
   thm_r7_2_breakdown,
   thm_r8_2_breakdown⟩

/-! ### Cat 3 phenomenological conjecture atom. -/

/--
  **Cat 3 phenomenological conjecture atom (Li 2026,
  `conj:threshold`).**

  The full bidirectional equivalence
  $R_k(b) = b^k \iff k \le 2(b - 1)$ for general $b \ge 2, k \ge 1$.

  *Sub-type:* `phenomenologicalConjecture` (paper publishes the
  full equivalence as a conjecture supported by limited boundary
  evidence; resolution path is further computational verification
  at higher $b$, particularly $R_6(4)$ and $R_7(4)$). NOT a
  `workingAssumption` (paper does not commit to closing this
  before publication; it is published AS a conjecture).

  *Status:* `gapOpen` Cat 3 phenomenologicalConjecture; the
  resolution path is empirical / computational evidence at higher
  $b$, NOT in-Lean derivation. Recorded here as the formal
  statement; not asserted as an axiom that any downstream theorem
  consumes.
-/
def threshold_conjecture_statement : Prop := RadoThresholdConjecture

/-! ### cascade architecture validated at
    the boundary $k = 4, b = 3$.

  Rounds 31, 39 validated `thm_cascade_matching` end-to-end at
  $k = 2$ (`thm_k2_via_cascade`) and $k = 3$
  (`thm_k3_via_cascade_matching`). Round 40 completes the picture
  at the boundary $k = 4, b = 3$: the cascade compression
  hypothesis holds **vacuously** there (via `thm_k4b3`), so
  `thm_threshold_via_cascade` re-derives $R_4(3) = 81$ through the
  general iterated capstone.

  This is the architectural closure across all proven
  matching-direction levels. Note: at the boundary, the
  hypothesis holds vacuously (no mono-free 3-coloring of
  $\{1,\ldots,81\}$ exists), not analytically — the paper's
  $G^*$-tree mechanism is what proves $R_4(3) = 81$ in the first
  place. Round 40's contribution is showing the cascade
  architecture *covers* the boundary, not that it provides an
  independent proof there. -/

/--
  **Lemma — `CascadeCompressionHyp 3 4` holds (vacuously).**

  At $b = 3$, $k = 4$: `thm_k4b3` (via `lem_gstartree`) proves
  every valid 3-coloring of $\{1, \ldots, 81\}$ has a
  monochromatic solution, so the `AvoidsMonoSolution` premise is
  unsatisfiable.
-/
theorem cascade_compression_hyp_k4_b3 : CascadeCompressionHyp 3 4 := by
  intro χ hValid hAvoid
  exact absurd (thm_k4b3.2 χ hValid) hAvoid

/--
  **Theorem — `thm_k4b3_via_cascade_matching`: $R_4(3) =
  81$ through the general iterated capstone.**

  Composes `cascade_compression_hyp_k2/k3/k4_b3` through
  `thm_threshold_via_cascade` at $k = 4$, $b = 3$. End-to-end
  validation of `thm_cascade_matching` at the boundary case —
  completing the architectural coverage across all proven
  matching-direction levels ($k = 2, 3, 4$).
-/
theorem thm_k4b3_via_cascade_matching : IsRadoNumber 3 4 (3 ^ 4) := by
  apply thm_threshold_via_cascade 3 (by omega) 4 (by omega)
  intro j hj2 hjk
  interval_cases j
  · exact cascade_compression_hyp_k2 3 (by omega)
  · exact cascade_compression_hyp_k3 3 (by omega) (by omega)
  · exact cascade_compression_hyp_k4_b3

/-! ### the cascade compression hypothesis
    FAILS at the breakdown level.

  Round 42's equivalence
  `CascadeCompressionHyp b k ↔ RadoNumberAtMost b k (b^k)` (given
  $R_{k-1} \le b^{k-1}$) has a sharp consequence at $k = 5$,
  $b = 3$: since $R_5(3) > 243 = 3^5$ (paper's `thm_r5_243`,
  SAT-verified witness), `RadoNumberAtMost 3 5 (3^5)` is FALSE,
  hence `CascadeCompressionHyp 3 5` is FALSE.

  This is the breakdown direction of the threshold conjecture, at
  the smallest known instance ($k = 5 > 2(b-1) = 4$ at $b = 3$),
  derived purely as a CONSEQUENCE of the architecture
  composed with the SAT witness (`thm_r5_243`). The architecture
  mirrors the conjecture's threshold mechanism: compression holds
  vacuously at the boundary, then fails strictly beyond. -/

/--
  **Theorem — `CascadeCompressionHyp 3 5` is FALSE.**

  The cascade compression hypothesis fails at the smallest known
  breakdown instance $(b, k) = (3, 5)$.

  Proof: by Round 42's equivalence, with the induction hypothesis
  $R_4(3) \le 81$ from `thm_k4b3`,
  `CascadeCompressionHyp 3 5 ↔ RadoNumberAtMost 3 5 (3^5)`. The
  RHS is FALSE because `thm_r5_243` exhibits a valid mono-free
  5-coloring of $\{1, \ldots, 243\}$ (=$\{1, \ldots, 3^5\}$).

  **Significance**: the architecture's hypothesis tracks the
  conjecture's threshold mechanism — `CascadeCompressionHyp` is
  vacuously true up to and including the boundary $k = 2(b-1)$,
  then strictly fails at the breakdown $k > 2(b-1)$. This is the
  breakdown direction at the smallest known instance, derived
  from the Round-42 equivalence + the paper's SAT witness.
-/
theorem cascade_compression_fails_at_breakdown : ¬ CascadeCompressionHyp 3 5 := by
  obtain ⟨χ, hValid, hAvoid⟩ := thm_r5_243
  have hpow : (3 : ℕ) ^ 5 = 243 := by norm_num
  exact cascade_compression_fails_of_breakdown 3 5 (by omega) (by omega) thm_k4b3.2
    χ (by rw [hpow]; exact hValid) (by rw [hpow]; exact hAvoid)

end RadoNumbers
