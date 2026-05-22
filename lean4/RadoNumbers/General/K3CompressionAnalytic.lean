/-
  RadoNumbers/General/K3CompressionAnalytic.lean

   — analytic attack on `CascadeCompressionHyp b 3`
  for general $b \ge 3$, the kernel-pure replacement target for the
  Cat 2 SAT atom `lem_compress3_general` (`K3General.lean:683-686`).

  **Phase 1 — `lem_compress2` skeleton (extracted from `K2.lean:56-142`).**

  The k=2 proof closes the compression hypothesis on the
  smaller-domain form `CompressionHyp b 2` (= valid 2-coloring of
  $\{1, \ldots, b^2 - 1\}$ has all multiples $b, 2b, \ldots, (b-1)b$
  share color $c_0 := \chi(b)$). Proof structure:

  1. **Strong induction on $i$**, with $1 \le i \le b - 1$. Base
     $i = 1$ trivial.
  2. **Triple $(b, b - 1, b)$** from $b + b(b-1) = b \cdot b$
     forces $\chi(b - 1) \ne c_0$.
  3. **Triple $(b \cdot (i-1), b, b + (i-1))$** from
     $b(i-1) + b \cdot b = b(b + (i-1))$. IH gives
     $\chi(b(i-1)) = c_0 = \chi(b)$, so $\chi(b + (i-1)) \ne c_0$.
  4. **Pigeonhole step using $k = 2$**: with 2 colors, every value
     $\ne c_0$ equals $1 - c_0$. So $\chi(b \cdot i) = \chi(b - 1)
     = \chi(b + (i-1)) = 1 - c_0$.
  5. **Contradiction triple $(b \cdot i, b - 1, b + (i-1))$**
     from $b \cdot i + b(b-1) = b(b + (i-1))$: all three colored
     $1 - c_0$, monochromatic, contradicting `AvoidsMonoSolution`.

  Where $k = 2$ specifically enters: Step 4. At $k = 3$ the same
  triples force $\chi(b \cdot i), \chi(b-1), \chi(b+(i-1))$ all
  $\ne c_0$, but they may take TWO different values in
  $\{1, 2\} \setminus \{c_0\}$, so the contradiction triple from
  Step 5 is NOT automatically monochromatic.

  **Phase 2 — minimal $k = 3$ compression lemma (proposed).**

  The minimal analytic content equivalent to
  `cascade_compression_hyp_k3_analytic` is the following sublemma:

      For valid mono-free 3-coloring $\chi$ of $\{1, \ldots, b^3\}$,
      the multiples sub-coloring $\chi'(d) := \chi(b \cdot d)$ on
      $\{1, \ldots, b^2\}$ OMITS at least one color.

  This is the exact body of `CascadeCompressionHyp b 3` modulo
  domain bookkeeping. Stated as `multiples_omit_color_k3` below.

  **Phase 3 — proof attempt for general $b$ (FAILS; see Phase 5).**

  Two attempted reductions:

  (R1) **Reduce to `lem_compress2` via 2-coloring**: by
     `multiples_subcoloring_valid`, $\chi'$ is a valid mono-free
     3-coloring on $[1, b^2]$. To apply `lem_compress2`, $\chi'$
     must be a valid 2-coloring — i.e., must already OMIT a color.
     Circular: that is the conclusion.

  (R2) **Iterate `multiples_subcoloring_valid` and use $R_2(b) \le
     b^2$**: $\chi'$ is a 3-coloring on $[1, b^2]$. Applying
     `multiples_subcoloring_valid` once more gives
     $\chi''(d) := \chi(b^2 \cdot d)$ on $[1, b]$, also a valid
     mono-free 3-coloring. But $\chi''$ being valid mono-free
     3-coloring on $[1, b]$ is consistent (the domain is too small
     for any Rado triple at $b \ge 2$ to fit entirely in $[1, b]$:
     the smallest Rado triple $(b, 1, 2)$ requires only $b$ in the
     domain, but $b + b \cdot 1 = b \cdot 2 = 2b > b$ would not
     hold... wait, the triple $(b, 1, 2)$ has $z = 2$ which fits in
     $[1, b]$ for $b \ge 2$; this is exactly the $k = 1$ trivial
     triple. But the IH $R_2(b) \le b^2$ says only that every
     2-coloring on $[1, b^2]$ has a mono — it constrains
     2-colorings, not 3-colorings). No reduction.

  (R3) **Round 1-8 cascade attack on $\chi(b) = \chi(2b)$
     pair-agreement**: paper Lemma `lem:k3b3pair` for $b = 3$
     proves $\chi(3) = \chi(6)$; general $b$ attempt was the
     Rounds 1-8 work captured in `K3General.lean:1-635`. Round 8
     verdict (`K3General.lean:626-630`): "branches $\chi((b-1)b)
     = 0$ and $\chi((b-1)b) = 2$ require depth-2 case analysis on
     $\chi(b-1), \chi(b^2), \chi(2b-1), \ldots$ that does not
     terminate in finitely many uniform-in-$b$ steps without new
     structural machinery." Branch closure NOT achieved for
     general $b$.

  **Phase 5 — Stop C diagnosis.**

  By Round 42's `cascade_compression_iff_upper_bound`
  (`DPLStructure.lean:1209-1216`), proving
  `CascadeCompressionHyp b 3` is mathematically EQUIVALENT to
  proving `RadoNumberAtMost b 3 (b^3)` (given the kernel-pure
  $k = 2$ result). So the analytic content of the proposed lemma
  is exactly the matching direction conclusion at $k = 3$ for
  general $b$ — i.e., proving $R_3(b) \le b^3$.

  Paper §"Color Compression Thresholds" SAT-verifies for
  $b \in \{4, \ldots, 10\}$ at threshold $n = 2b^2 < b^3$. No
  analytic proof appears in the paper. $b \ge 11$ is open even
  in the paper.

  **Conclusion**: the proof is genuinely open mathematics, not a
  Lean infrastructure gap. We deliver the minimal lemma
  statement + structural blocker, and partial structural assets
  (Phase 4 below) that constrain the search space.

  **Phase 4 — partial deliverable.**

  We prove a strict sublemma — `multiples_subcoloring_three_color_constraints`
  — that bundles the constraints proved analytically in
  `K3General.lean` Rounds 1-7 into a single statement for general
  $b$. This is NOT the cascade hypothesis itself (no color is
  omitted) but localizes the structural obstacle.

  **Round 8's identification of the blocker** is the right diagnosis:
  the b=3 case closes via finite case analysis on $\chi((b-1)b)$
  (Rounds 5-7), but this case analysis at general $b \ge 4$ proliferates.
  The paper's SAT verification at $n = 2b^2$ exploits this
  proliferation directly; no analytic surrogate is known.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.K2
import RadoNumbers.DPLStructure
import RadoNumbers.K3General
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Phase 2 — minimal $k = 3$ compression lemma statement. -/

/--
  ** Sublemma 1 statement (target, OPEN for general $b \ge 3$).**

  The exact analytic content of `CascadeCompressionHyp b 3`:
  for every valid mono-free 3-coloring of $\{1, \ldots, b^3\}$,
  the multiples sub-coloring $\chi'(d) := \chi(b \cdot d)$ on
  $\{1, \ldots, b^2\}$ omits at least one color.

  **Status**: OPEN for general $b \ge 3$ (closed by SAT atom
  `lem_compress3_general` for $b \in \{4, \ldots, 10\}$).
  Equivalent to $R_3(b) \le b^3$ by `cascade_compression_iff_upper_bound`
  (`DPLStructure.lean:1209-1216`).

  Provided here as the lemma to attack. See `R438_k3_general_strategy.md`
  for the analysis of why direct attack is blocked.
-/
def MultiplesOmitColorK3 (b : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ 3) 3 χ →
    AvoidsMonoSolution b (b ^ 3) χ →
    ∃ c₀, c₀ < 3 ∧ ∀ d, 1 ≤ d → d ≤ b ^ 2 → χ (b * d) ≠ c₀

/--
  ** — definitional equivalence.**

  `MultiplesOmitColorK3 b` (the sublemma statement) is
  definitionally equal to `CascadeCompressionHyp b 3` after
  `pow_succ` unfolds $b^{3-1} = b^2$.
-/
theorem multiples_omit_color_k3_iff (b : ℕ) :
    MultiplesOmitColorK3 b ↔ CascadeCompressionHyp b 3 := by
  unfold MultiplesOmitColorK3 CascadeCompressionHyp
  -- pow exponent 3 - 1 = 2 reduces by `Nat.reduceSub`.
  rfl

/-! ### Phase 4 — Rounds 1-7 constraint bundle (PARTIAL).

  The Rounds 1-7 work in `K3General.lean` proved a chain of
  conditional constraints under the disagreement hypothesis
  $\chi(b) = 0, \chi(2b) = 1$. Round 8 verdict: branches on
  $\chi((b-1)b)$ do NOT terminate uniformly in $b$.

  We bundle the unconditional fragments (i.e., the lemmas that
  hold without the disagreement assumption) into a single
  statement. This is NOT the cascade hypothesis — but it
  enumerates the analytic structure that has been validated for
  general $b$ and isolates the precise obstruction.
-/

/--
  ** Phase 4 — Rounds 1-7 unconditional constraint bundle.**

  For every $b \ge 3$ and valid mono-free 3-coloring $\chi$ of
  $\{1, \ldots, n\}$ with $n \ge b^2$, the following hold:

  (a) `chi_b_minus_one_b_ne_chi_b_sq` (Lemma 2.1):
      $\chi((b-1) \cdot b) \ne \chi(b^2)$.
  (b) `chi_pred_b_ne` (Lemma 1.3):
      $\chi(b - 1) \ne \chi(b)$.
  (c) `chi_succ_b_ne` (Lemma 1.2):
      $\chi(b + 1) \ne \chi(b)$.

  These three are the unconditional fragments of the cascade
  attack — they constrain $\chi$ at positions $b - 1, b, b + 1,
  (b-1)b, b^2$ without any disagreement hypothesis.

  **Status**: kernel-pure.

  **Significance**: this is the maximum the cascade attack
  achieves WITHOUT case-splitting on $\chi((b-1)b)$. The Round
  8 verdict identifies the case-split as the non-terminating
  step; this lemma captures everything proved by Rounds 1-7
  that survives without that case-split.
-/
theorem rounds_1_7_constraint_bundle {b n : ℕ} (hb : 3 ≤ b)
    (hn_bsq : b ^ 2 ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution b n χ) :
    χ ((b - 1) * b) ≠ χ (b ^ 2) ∧
    χ (b - 1) ≠ χ b ∧
    (b + 1 ≤ n → χ (b + 1) ≠ χ b) := by
  have hb_pos : 0 < b := by linarith
  have hb_le_bsq : b ≤ b ^ 2 := by nlinarith
  have hb_le_n : b ≤ n := le_trans hb_le_bsq hn_bsq
  have hbm1b_le_bsq : (b - 1) * b ≤ b ^ 2 := by
    have h : (b - 1) * b + b = b ^ 2 := by
      have hsub : b - 1 + 1 = b := by omega
      have : (b - 1) * b + b = ((b - 1) + 1) * b := by ring
      rw [this, hsub]; ring
    omega
  have hbm1b_le_n : (b - 1) * b ≤ n := le_trans hbm1b_le_bsq hn_bsq
  refine ⟨?_, ?_, ?_⟩
  · -- (a) chi_b_minus_one_b_ne_chi_b_sq
    exact chi_b_minus_one_b_ne_chi_b_sq (by linarith : 2 ≤ b) hn_bsq hbm1b_le_n χ hAvoid
  · -- (b) chi_pred_b_ne
    exact chi_pred_b_ne (by linarith : 2 ≤ b) hb_le_n χ hAvoid
  · -- (c) chi_succ_b_ne (conditional on b + 1 ≤ n)
    intro hbp1
    exact chi_succ_b_ne (by linarith : 2 ≤ b) hb_le_n hbp1 χ hAvoid

/-! ### Phase 4 — explicit blocker theorem statement.

  The minimal sub-goal that, if proved, would unblock
  `MultiplesOmitColorK3 b` for general $b$. This isolates the
  specific case-split that Round 8 found non-terminating.

  **Claim (the open sub-goal)**: at $k = 3$ general $b$, for the
  multiples sub-coloring $\chi'$ on $[1, b^2]$, the value
  $\chi'(b-1) = \chi((b-1)b)$ is NOT free across branches — but
  the constraints from `rounds_1_7_constraint_bundle` plus
  $\chi(b) \ne \chi(b-1)$ from Lemma 1.3 do not pin down enough
  to force a contradiction without depth-3 case analysis.

  This Phase 4 deliverable is the precise STATEMENT of the
  blocker — the SMALLEST theorem signature that, if proved,
  closes Sublemma 1 for general $b$.
-/

/--
  ** Phase 4 — explicit blocker (Stop C diagnosis).**

  The smallest hypothesis that, conjoined with
  `rounds_1_7_constraint_bundle` and applied at $n = b^3$, would
  close `MultiplesOmitColorK3 b`:

  > For every valid mono-free 3-coloring of $\{1, \ldots, b^3\}$,
  > either (i) $\chi(b) = \chi(2b)$, or (ii) $\chi(b) = \chi((b-1)b)$.

  In words: the multiples $\{b, 2b, (b-1)b\}$ cannot use 3 distinct
  colors.

  **Status**: OPEN for general $b \ge 4$. Closed for $b = 3$ via
  the kernel-pure derivation (`K3B3.lean:79-80`).

  **Reduction to MultiplesOmitColorK3**: if the three multiples
  $\{b, 2b, (b-1)b\}$ use only 2 colors, then by iteration of
  Round 4-6 conditional lemmas applied to the remaining multiples
  $\{3b, 4b, \ldots, (b-2)b\}$, the whole sub-coloring on $[1, b^2]$
  collapses to a 2-coloring — closing `MultiplesOmitColorK3`. But
  the iteration itself requires the same depth of case analysis
  that Round 8 identified as non-terminating in $b$, so the
  reduction is bidirectional in difficulty.

  Stated below as a `def : Prop` (not asserted), parallel to the
  treatment of `RadoThresholdConjecture` itself.
-/
def K3MultiplesThreeColorImpossible (b : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ 3) 3 χ →
    AvoidsMonoSolution b (b ^ 3) χ →
    χ b = χ (2 * b) ∨ χ b = χ ((b - 1) * b) ∨ χ (2 * b) = χ ((b - 1) * b)

/-! ### — note on the iff with the main goal.

  We do NOT claim `K3MultiplesThreeColorImpossible b →
  MultiplesOmitColorK3 b` as a proved theorem, because the
  forward reduction itself requires the depth-2 case analysis
  that Round 8 identified as obstructive. Specifically:

  * If the three multiples $\{b, 2b, (b-1)b\}$ use 2 colors,
    one color (say $c_1$) is used by 2 of them. Iterating
    Round 4-6 lemmas, the constraint "color $c_1$ avoids
    distance $d$" propagates through pairs $(b, b+d)$ etc.
    But the choice of $d$ depends on WHICH multiples coincide,
    branching the proof.

  Thus `K3MultiplesThreeColorImpossible` is a CLEANER statement
  than `MultiplesOmitColorK3` but not strictly easier. Both are
  open at general $b \ge 4$.

  **The honest report**: STOPS at this point with Stop C —
  the structural obstruction (depth-2 case analysis on
  multiples-of-$b^2$) is exactly the boundary that separates
  $b = 3$ (closeable kernel-pure via 's partition-shape
  machinery, but hardcoded to $b = 3, n = 27$) from $b \ge 4$
  (open, paper falls back to SAT verification).
-/

end RadoNumbers
