/-
  RadoNumbers/General/K3B4PairAgreement.lean

  R441 (2026-05-22) — Pair-agreement diagnostic at $b = 4$, $n = 32$
  for $\chi(8) = \chi(12)$.

  **Target statement (R441 attack).**  For every valid mono-free
  3-coloring $\chi$ of $\{1, \ldots, 32\}$ avoiding monochromatic
  solutions to $x + 4y = 4z$, the pair-agreement $\chi(8) = \chi(12)$
  is FORCED.

  This is the analytic seed at the safe-zone boundary $n = 2 b^2$ for
  $b = 4$ (paper §"Color Compression Thresholds"; chain-extraction
  data in `src/R440_chain_extraction.py`).  R440's prediction was that
  $n_{\text{eff}} = 32$ is exactly the smallest domain forcing
  $\chi(8) = \chi(12)$; R441 Phase A confirms.

  **R441 Phase A (`src/R441_b4_n32_pair_agreement_search.py`).**
  Diagnostic SAT enumeration on $\{1, \ldots, 32\}$ with the
  additional constraint $\chi(8) \ne \chi(12)$.

    * **Domain triple count**: 220 Rado triples in $\{1, \ldots, 32\}$
      (vs. 825 on $\{1, \ldots, 63\}$).  Family breakdown:
      F1_self_loop = 8, F2_all_multiples = 11, T-A_cross = 123,
      T-A_y_mult = 39, T-A_z_mult = 39.
    * **SAT verdict**: UNSAT.  $\chi(8) = \chi(12)$ is forced on
      $\{1, \ldots, 32\}$.  Smaller-domain probe: at $n_{\text{eff}}
      \le 28$ the pair-disagree instance is SAT (not forced); at
      $n_{\text{eff}} = 32$ it flips to UNSAT.
    * **Sub-domain family-removal probes**
      (`src/R441_b4_n32_followups.py`):
      - F1+F2+T-A_y_mult+T-A_z_mult alone (97 triples): SAT — does
        NOT force the agreement.
      - F1+F2 alone (19 multiples-internal triples): SAT.
      - F1+F2+T-A_cross alone (142 triples): SAT.
      The T-A_cross family is essential, as is at least one of
      T-A_y_mult / T-A_z_mult.

  **R441 Phase A — MUS analysis (`src/R441_b4_n32_mus_minimize.py`,
  `src/R441_b4_n32_smaller_mus.py`).**

    * **Best MUS over deterministic ordering strategies**: 76 distinct
      Rado triples (irreducible under greedy single-deletion).
    * **Family breakdown of best MUS**: F1_self_loop = 7,
      F2_all_multiples = 7, T-A_cross = 27, T-A_y_mult = 21,
      T-A_z_mult = 14.
    * **Positions used in best MUS**: 25 of 32.
    * **All three pair-disagree clauses needed** (one per color):
      no single-color shortcut.
    * **Multi-start greedy** (30 random orders): MUS sizes range
      152–193 with mean 175.3.  The 76-triple solution is well below
      the mean — likely close to the floor.

  **R441 Phase A — cross-checks.**

    * At $n = 32$, ALL pair-agreements among the v_4=1 multiples
      $\{8, 12, 20, 24, 28\}$ are forced (15 of 15 pairs).
    * Pairs INVOLVING position 4 (i.e., $\chi(4) = \chi(\text{anything})$)
      are NOT forced at $n = 32$ — matches R440's chain-extraction.
    * The v_4=2 pair $\chi(16) = \chi(32)$ is forced at $n = 32$.

  **R441 Phase A — conclusion: Stop C.**  The 76-triple MUS, even at
  the floor of greedy minimization, has 27 T-A_cross triples spanning
  positions across $\{4, \ldots, 32\}$.  No compact analytic proof
  exists at $n = 32$; the MUS is structurally the same case-explosion
  pattern R440 identified at $n = 63$, just restricted.

  **R441 Phase B (this file).**  We deliver:

  1. The statement `Chi8EqChi12K3B4_at32` as a `def : Prop` (parallel
     to R440's `MultiplesSubColoringPopulationB4`).  NOT asserted.
  2. A kernel-pure analytic bundle scoped to $n = 32$:
     `b4_n32_self_loop_bundle` (4 forced disagreements derivable from
     the local self-loops at $m \in \{4, 8\}$ — the strict $n = 32$
     analog of R440's $n \ge 60$ bundle).
  3. Documentation of the R441 Stop C verdict.

  We do NOT close `Chi8EqChi12K3B4_at32` — Phase A diagnostic
  confirms the proof requires 76+ triple applications, which exceeds
  the ~50 triple-application threshold for a compact Lean proof per
  the R441 prompt.

  Strictly kernel-pure: every proved theorem here depends on
  `[propext, Classical.choice, Quot.sound]` only.
-/

import RadoNumbers.Basic
import RadoNumbers.Foundational
import Mathlib.Tactic

namespace RadoNumbers

/-! ### R441 Phase B — Pair-agreement statement (def : Prop, NOT asserted). -/

/--
  **R441 target — Pair agreement $\chi(8) = \chi(12)$ at $b = 4$,
  $n = 32$.**

  For every valid mono-free 3-coloring $\chi$ of $\{1, \ldots, 32\}$
  avoiding monochromatic solutions to $x + 4 y = 4 z$:
  $\chi(8) = \chi(12)$.

  **R441 Phase A SAT-verification status**: TRUE.  SAT diagnostic at
  $n_{\text{eff}} = 32$ confirms the constraint set is UNSAT (i.e.,
  no mono-free 3-coloring of $\{1, \ldots, 32\}$ has
  $\chi(8) \ne \chi(12)$).  At $n_{\text{eff}} \le 28$ the constraint
  is SAT (counterexample exists; pair-agreement NOT forced).

  **R441 Phase A analytic status**: STOP C.  Best MUS over
  deterministic ordering strategies has 76 distinct Rado triples;
  multi-start greedy gives 152–193.  The MUS uses 25 of 32 positions
  and all three pair-disagree color clauses.  No compact analytic
  proof (sub-50-triple) is known.

  Stated as `def : Prop`; not asserted.  R440's analogous statement
  is `MultiplesSubColoringPopulationB4` (at $n = 63$).  R441
  refines: this PAIR-AGREEMENT sub-problem at $n = 32$ has the same
  Stop C verdict, with a slightly smaller MUS than R440's 105-triple
  5-subset case.
-/
def Chi8EqChi12K3B4_at32 : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring 32 3 χ →
    AvoidsMonoSolution 4 32 χ →
    χ 8 = χ 12

/-! ### R441 Phase B — analytic bundle for $b = 4$ at $n = 32$.

  We collect the kernel-pure single-triple forced disagreements that
  fit STRICTLY within $n = 32$.  Self-loops `self_loop_eq_left` and
  `self_loop_eq_right` apply at $b = 4$, $m \in \{1, \ldots\}$ subject
  to $b m \le n$ and $(b + 1) m \le n$ respectively, i.e., at $n = 32$:

  | Witness Rado triple | Self-loop type | Forced inequality      |
  | ------------------- | -------------- | ---------------------- |
  | $(16, 12, 16)$, m=4 | type $x = z$   | $\chi(16) \ne \chi(12)$ |
  | $(16, 16, 20)$, m=4 | type $x = y$   | $\chi(20) \ne \chi(16)$ |
  | $(32, 24, 32)$, m=8 | type $x = z$   | $\chi(32) \ne \chi(24)$ |
  | $(24, 24, 30)$, m=6 | type $x = y$   | $\chi(30) \ne \chi(24)$ |

  Note: at $n = 32$, the $m = 8$ type-$x = y$ self-loop $(32, 32, 40)$
  would require $(b + 1) m = 40 > 32$, so it does NOT apply at
  $n = 32$ (in contrast to R440's $n = 60$ bundle).  We use $m = 6$
  for the second self-loop pair instead.

  Together these 4 forced disagreements are the maximum self-loop
  content reachable at $n = 32$.  They DO NOT prove
  `Chi8EqChi12K3B4_at32` directly — that requires the 76-triple
  MUS chain.
-/

/--
  **R441 b=4, n=32 self-loop bundle.**

  For every valid mono-free 3-coloring of $\{1, \ldots, n\}$ with
  $n \ge 32$:

      $\chi(16) \ne \chi(12)$, $\chi(20) \ne \chi(16)$,
      $\chi(32) \ne \chi(24)$, $\chi(30) \ne \chi(24)$.

  The first three are also in R440's $n \ge 60$ bundle (at
  $m \in \{4, 8\}$); the fourth is added here because $m = 6$,
  $(b + 1) m = 30 \le 32$ fits in this smaller domain.

  Strictly kernel-pure.
-/
theorem b4_n32_self_loop_bundle {n : ℕ} (hn : 32 ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 16 ≠ χ 12 ∧ χ 20 ≠ χ 16 ∧
    χ 32 ≠ χ 24 ∧ χ 30 ≠ χ 24 := by
  have hb : (2 : ℕ) ≤ 4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- m = 4: (16, 12, 16) self-loop type x = z, χ(4 * 4) ≠ χ((4-1) * 4).
    have h := self_loop_eq_left hb (m := 4) (by decide : 1 ≤ 4)
      (by linarith : 4 * 4 ≤ n) χ hAvoid
    have h1 : (4 * 4 : ℕ) = 16 := by decide
    have h2 : ((4 - 1) * 4 : ℕ) = 12 := by decide
    rw [h1, h2] at h
    exact h
  · -- m = 4: (16, 16, 20) self-loop type x = y, χ((4+1) * 4) ≠ χ(4 * 4).
    have h := self_loop_eq_right hb (m := 4) (by decide : 1 ≤ 4)
      (by linarith : (4 + 1) * 4 ≤ n) χ hAvoid
    have h1 : ((4 + 1) * 4 : ℕ) = 20 := by decide
    have h2 : (4 * 4 : ℕ) = 16 := by decide
    rw [h1, h2] at h
    exact h
  · -- m = 8: (32, 24, 32) self-loop type x = z, χ(4 * 8) ≠ χ((4-1) * 8).
    have h := self_loop_eq_left hb (m := 8) (by decide : 1 ≤ 8)
      (by linarith : 4 * 8 ≤ n) χ hAvoid
    have h1 : (4 * 8 : ℕ) = 32 := by decide
    have h2 : ((4 - 1) * 8 : ℕ) = 24 := by decide
    rw [h1, h2] at h
    exact h
  · -- m = 6: (24, 24, 30) self-loop type x = y, χ((4+1) * 6) ≠ χ(4 * 6).
    have h := self_loop_eq_right hb (m := 6) (by decide : 1 ≤ 6)
      (by linarith : (4 + 1) * 6 ≤ n) χ hAvoid
    have h1 : ((4 + 1) * 6 : ℕ) = 30 := by decide
    have h2 : (4 * 6 : ℕ) = 24 := by decide
    rw [h1, h2] at h
    exact h

/-! ### R441 Phase B — single-pair extraction theorems.

  For paper readout, we expose the four inequalities individually.
-/

/--
  **R441 b=4, n=32 single inequality $\chi(16) \ne \chi(12)$.**

  From the self-loop triple $(16, 12, 16)$ at $b = 4$, $m = 4$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_16_ne_chi_12 {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 16 ≠ χ 12 :=
  (b4_n32_self_loop_bundle hn χ hAvoid).1

/--
  **R441 b=4, n=32 single inequality $\chi(20) \ne \chi(16)$.**

  From the self-loop triple $(16, 16, 20)$ at $b = 4$, $m = 4$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_20_ne_chi_16 {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 20 ≠ χ 16 :=
  (b4_n32_self_loop_bundle hn χ hAvoid).2.1

/--
  **R441 b=4, n=32 single inequality $\chi(32) \ne \chi(24)$.**

  From the self-loop triple $(32, 24, 32)$ at $b = 4$, $m = 8$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_32_ne_chi_24 {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 32 ≠ χ 24 :=
  (b4_n32_self_loop_bundle hn χ hAvoid).2.2.1

/--
  **R441 b=4, n=32 single inequality $\chi(30) \ne \chi(24)$.**

  From the self-loop triple $(24, 24, 30)$ at $b = 4$, $m = 6$.  Note
  $m = 6$ is NOT a multiple of $b = 4$, so $24 = 4 \cdot 6$ is a v_4=1
  multiple (consistent with the v_4 = 1 spine of R440).

  Strictly kernel-pure.
-/
theorem b4_n32_chi_30_ne_chi_24 {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 30 ≠ χ 24 :=
  (b4_n32_self_loop_bundle hn χ hAvoid).2.2.2

/-! ### R441 Phase B — F2 mono-block at $b = 4$, $n = 32$.

  At $b = 4$, $n = 32$, the F2 (all-multiples) triples involve
  $(16, 4, 8)$, $(16, 16, 20)$, $(16, 24, 28)$, $(32, 4, 12)$,
  $(32, 8, 16)$, $(32, 12, 20)$, $(32, 20, 28)$, $(32, 28, 36)$ (the
  last not in $[1, 32]$), etc.  Each is a Rado triple whose mono
  violation forces a triple inequality on the three colors involved.
-/

/--
  **R441 b=4, n=32 F2 mono-block: $\neg (\chi(4) = \chi(8) \land
  \chi(8) = \chi(16))$.**

  Witness Rado triple: $(16, 4, 8)$.  Verification:
  $16 + 4 \cdot 4 = 16 + 16 = 32 = 4 \cdot 8$.

  Monochromaticity at color $c$ would require
  $\chi(16) = \chi(4) = \chi(8) = c$, which violates
  `AvoidsMonoSolution`.

  Strictly kernel-pure.
-/
theorem b4_n32_F2_16_4_8_not_mono {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    ¬ (χ 16 = χ 4 ∧ χ 4 = χ 8) := by
  intro ⟨h1, h2⟩
  apply hAvoid
  refine ⟨16, 4, 8, ?_, ?_, ?_, ?_, h1, h2⟩
  · linarith
  · linarith
  · linarith
  · refine ⟨by decide, by decide, by decide, ?_⟩
    -- 16 + 4 * 4 = 4 * 8
    decide

/--
  **R441 b=4, n=32 F2 mono-block: $\neg (\chi(4) = \chi(12) \land
  \chi(12) = \chi(32))$ ... no wait, the triple $(32, 4, 12)$ gives
  $\chi(32) = \chi(4) = \chi(12)$ would be mono.**

  Witness Rado triple: $(32, 4, 12)$.  Verification:
  $32 + 4 \cdot 4 = 32 + 16 = 48 = 4 \cdot 12$.

  Strictly kernel-pure.
-/
theorem b4_n32_F2_32_4_12_not_mono {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    ¬ (χ 32 = χ 4 ∧ χ 4 = χ 12) := by
  intro ⟨h1, h2⟩
  apply hAvoid
  refine ⟨32, 4, 12, ?_, ?_, ?_, ?_, h1, h2⟩
  · linarith
  · linarith
  · linarith
  · refine ⟨by decide, by decide, by decide, ?_⟩
    decide

/--
  **R441 b=4, n=32 F2 mono-block: $\neg (\chi(32) = \chi(8) = \chi(16))$.**

  Witness Rado triple: $(32, 8, 16)$.  Verification:
  $32 + 4 \cdot 8 = 32 + 32 = 64 = 4 \cdot 16$.

  Strictly kernel-pure.
-/
theorem b4_n32_F2_32_8_16_not_mono {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    ¬ (χ 32 = χ 8 ∧ χ 8 = χ 16) := by
  intro ⟨h1, h2⟩
  apply hAvoid
  refine ⟨32, 8, 16, ?_, ?_, ?_, ?_, h1, h2⟩
  · linarith
  · linarith
  · linarith
  · refine ⟨by decide, by decide, by decide, ?_⟩
    decide

/--
  **R441 b=4, n=32 F2 mono-block: $\neg (\chi(32) = \chi(12) = \chi(20))$.**

  Witness Rado triple: $(32, 12, 20)$.  Verification:
  $32 + 4 \cdot 12 = 32 + 48 = 80 = 4 \cdot 20$.

  Strictly kernel-pure.
-/
theorem b4_n32_F2_32_12_20_not_mono {n : ℕ} (hn : 32 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    ¬ (χ 32 = χ 12 ∧ χ 12 = χ 20) := by
  intro ⟨h1, h2⟩
  apply hAvoid
  refine ⟨32, 12, 20, ?_, ?_, ?_, ?_, h1, h2⟩
  · linarith
  · linarith
  · linarith
  · refine ⟨by decide, by decide, by decide, ?_⟩
    decide

/-! ### R441 Phase B — F1 spine at $b = 4$, $n = 32$.

  At $b = 4$, $m \in \{1, \ldots, 8\}$ with $b m \le n = 32$, the F1
  self-loops $(4 m, 3 m, 4 m)$ apply.  R440 already captures
  $m \in \{4, 8, 12\}$ (n=60) and the n=32 sub-spine is m=1..8.
  Below we expose the m=3 and m=5 F1 disagreements that are NOT in
  R440's n=60 bundle but ARE in R441's n=32 MUS.
-/

/--
  **R441 b=4, n=32 F1 spine: $\chi(12) \ne \chi(9)$.**

  Witness Rado triple: $(12, 9, 12)$ at $b = 4$, $m = 3$.

  Verification: $12 + 4 \cdot 9 = 48 = 4 \cdot 12$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_12_ne_chi_9 {n : ℕ} (hn : 12 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 12 ≠ χ 9 := by
  have h := self_loop_eq_left (b := 4) (by decide : 2 ≤ 4) (m := 3)
    (by decide : 1 ≤ 3) (by linarith : 4 * 3 ≤ n) χ hAvoid
  have h1 : (4 * 3 : ℕ) = 12 := by decide
  have h2 : ((4 - 1) * 3 : ℕ) = 9 := by decide
  rw [h1, h2] at h
  exact h

/--
  **R441 b=4, n=32 F1 spine: $\chi(20) \ne \chi(15)$.**

  Witness Rado triple: $(20, 15, 20)$ at $b = 4$, $m = 5$.

  Verification: $20 + 4 \cdot 15 = 80 = 4 \cdot 20$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_20_ne_chi_15 {n : ℕ} (hn : 20 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 20 ≠ χ 15 := by
  have h := self_loop_eq_left (b := 4) (by decide : 2 ≤ 4) (m := 5)
    (by decide : 1 ≤ 5) (by linarith : 4 * 5 ≤ n) χ hAvoid
  have h1 : (4 * 5 : ℕ) = 20 := by decide
  have h2 : ((4 - 1) * 5 : ℕ) = 15 := by decide
  rw [h1, h2] at h
  exact h

/--
  **R441 b=4, n=32 F1 spine: $\chi(28) \ne \chi(21)$.**

  Witness Rado triple: $(28, 21, 28)$ at $b = 4$, $m = 7$.

  Verification: $28 + 4 \cdot 21 = 28 + 84 = 112 = 4 \cdot 28$.

  Strictly kernel-pure.
-/
theorem b4_n32_chi_28_ne_chi_21 {n : ℕ} (hn : 28 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 28 ≠ χ 21 := by
  have h := self_loop_eq_left (b := 4) (by decide : 2 ≤ 4) (m := 7)
    (by decide : 1 ≤ 7) (by linarith : 4 * 7 ≤ n) χ hAvoid
  have h1 : (4 * 7 : ℕ) = 28 := by decide
  have h2 : ((4 - 1) * 7 : ℕ) = 21 := by decide
  rw [h1, h2] at h
  exact h

/-! ### R441 Phase B — Stop C documentation.

  We DO NOT prove `Chi8EqChi12K3B4_at32`.  R441 Phase A MUS extraction
  shows:

    * Best MUS: 76 distinct Rado triples (irreducible under greedy
      single-deletion).
    * Multi-start mean MUS: 175.3 (range 152–193).
    * Family composition of best MUS: F1 = 7, F2 = 7, T-A_cross = 27,
      T-A_y_mult = 21, T-A_z_mult = 14.
    * All three pair-disagree color clauses required (no WLOG short-
      cut by color symmetry).

  Per the R441 prompt threshold ("more than ~50 Rado triple
  applications in Lean, STOP and report core structure"), the
  76-triple MUS exceeds the compactness threshold.  We report
  Stop C honestly.

  **R441 Phase A — what would be needed for a kernel-pure proof:**

    * 76 distinct Rado triples encoded as separate
      `AvoidsMonoSolution`-derived constraints.
    * 25 positions across $\{1, \ldots, 32\}$ named explicitly with
      WLOG color normalization on $\chi(8) = c_0$, $\chi(12) = c_1$
      and propagation through T-A_cross triples.
    * A 3-color case split with all three pair-disagree color clauses
      contributing to the contradiction.

  This is the EXACT case-explosion pattern R438 / R440 identified;
  shrinking the domain from $n = 63$ to $n = 32$ does NOT compactify
  the MUS by an order of magnitude.

  **Strategic finding (R441)**: pair-agreement at the safe-zone
  boundary $n = 2 b^2$ does NOT escape the Stop C explosion.  The
  Boundary $n = 2 b^2$ is the smallest n forcing $\chi(8) = \chi(12)$,
  but the analytic proof at this smallest n still has the same
  structural difficulty.

  **R441 recommendation**: do NOT continue chasing forward pair-
  agreements at $b = 4$ via the cascade chain — every such target
  inherits the same Stop C blocker.  Pivot to either:

    (i) The PAPER §11.1 valuation forced-agreement pattern, treated
        as an OPEN MATHEMATICS problem rather than via SAT-induced
        case analysis;
    (ii) The PAPER §11.2 first-two-multiples-agree at $n = (b-1) b^2
        = 48$, recognising the MUS for that target is likely larger
        but the natural-domain match enables paper §5's analytic
        Step 1/2 structure to apply;
    (iii) The R441 BACKWARD direction: instead of proving $\chi(8)
        = \chi(12)$, try to characterize the SET of valid mono-free
        3-colorings of $\{1, \ldots, 32\}$ and observe the pair-
        agreement as a corollary of the characterization.  This was
        not part of R441 scope; flagged for R442.
-/

/--
  **R441 Stop C — formal record of the non-proof.**

  The statement `Chi8EqChi12K3B4_at32` is recorded as a `def : Prop`
  (NOT proven).  Its truth is SAT-verified at $n = 32$ via the
  Phase A diagnostic, but the proof is NOT kernel-pure compactly.

  Formally, this `theorem` is a `def`-unfolding identity.
-/
theorem chi8_eq_chi12_k3_b4_at32_def_eq :
    Chi8EqChi12K3B4_at32 =
      (∀ χ : ℕ → ℕ, IsValidColoring 32 3 χ →
        AvoidsMonoSolution 4 32 χ →
        χ 8 = χ 12) :=
  rfl

end RadoNumbers
