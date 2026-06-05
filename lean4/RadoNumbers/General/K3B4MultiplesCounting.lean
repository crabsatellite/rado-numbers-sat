/-
  RadoNumbers/General/K3B4MultiplesCounting.lean

  R440 (2026-05-22) — Diagnostic + analytic-bundle deliverable for
  Candidate I' at $b = 4$, $n = b^3 - 1 = 63$.

  **Candidate I' (statement, target of attack).**  For every valid
  mono-free 3-coloring $\chi$ of $\{1, \ldots, 63\}$ avoiding
  monochromatic solutions to $x + 4y = 4z$, the multiples
  sub-coloring on $\{4, 8, 12, \ldots, 60\}$ (15 positions) has SOME
  color appearing at least 6 times.

  **Diagnostic outcome (R440 Phase 1).**  SAT verification and
  structural probes on $\{1, \ldots, 63\}$ with $b = 4$ show:

    * The 5+5+5 balanced partition is UNSAT (Candidate I' holds).
    * Strictly more: the ONLY valid multiples-partition (up to color
      permutation) is $(12, 3, 0)$ — i.e., **some color is OMITTED
      from the 15 multiples**.  This is the Color Compression
      Hypothesis content at $b = 4$ (paper §"Color Compression
      Thresholds"; Lean `CompressionHyp 4 3`).
    * Every pair of multiples is FORCED-EQUAL or FORCED-DISAGREE
      (zero free pairs).  The 12 multiples with $v_4 = 1$ share one
      color; the 3 multiples $\{16, 32, 48\}$ with $v_4 = 2$ share a
      different color; the third color is omitted from multiples.

  **Conclusion (R440 Phase 3, Stop C).**  No compact analytic proof
  of Candidate I' exists at $b = 4$ that avoids both
  (i) `lem_compress3_general` / `cascade_compression_hyp_k3_analytic`
  and
  (ii) the full case explosion identified at R438's Stop C.

  The minimal unsatisfiable subset (MUS) for the SUB-PROBLEM "5-subset
  $\{8, 12, 20, 24, 28\}$ monochromatic on $\{1, \ldots, 32\}$"
  contains **105 distinct Rado triples** spanning ~32 positions
  (see `R440_mus_extract.py`).  This is the analytic burden of
  Candidate I' at $b = 4$ even for a sub-problem of the full
  statement.

  **Phase 4 deliverable (this file).**  We do NOT assert Candidate
  I'.  We deliver:

  1. The statement `MultiplesSubColoringPopulationB4` as a
     `def : Prop` (parallel to R438's `K3MultiplesThreeColorImpossible`).
  2. A strict POSITIVE kernel-pure analytic bundle at $b = 4$:
     `b4_multiples_local_self_loop_bundle` — the analytic constraints
     around the v_4=2 multiples $\{16, 32, 48\}$ that R440's structural
     probe identifies as the v_4=2 / v_4=1 boundary forcing the
     partition rigidity.
  3. Documentation of the Stop C verdict.

  Strictly kernel-pure: every proved theorem in this file depends on
  `[propext, Classical.choice, Quot.sound]` only.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.Foundational
import RadoNumbers.K3General
import RadoNumbers.DPLStructure
import RadoNumbers.General.K3CompressionAnalytic
import Mathlib.Tactic

namespace RadoNumbers

/-! ### R440 Phase 4 — Candidate I' statement (def : Prop, NOT asserted). -/

/--
  **Candidate I' at $b = 4$ — Multiples Population Lemma.**

  Statement: for every valid mono-free 3-coloring $\chi$ of
  $\{1, \ldots, 63\}$, the multiples sub-coloring on the 15 positions
  $\{4, 8, 12, \ldots, 60\}$ has SOME color $c$ appearing AT LEAST 6
  times.

  **R440 Phase 1 SAT-verification status**: TRUE at $b = 4$.  In fact,
  the SAT diagnostic confirms a STRICTLY STRONGER claim: the only valid
  multiples-partition (up to color permutation) is $(12, 3, 0)$.

  **R440 Phase 3 analytic status**: STOP C.  No compact analytic proof
  is known that avoids (i) the cascade compression hypothesis at
  $k = 3$ (`MultiplesOmitColorK3`, `cascade_compression_hyp_k3_analytic`)
  and (ii) the full case explosion identified at R438's Stop C.

  Stated as `def : Prop` (parallel to `K3MultiplesThreeColorImpossible`),
  not asserted.  The corresponding $b = 4$ instance of the cascade
  hypothesis is `CompressionHyp 4 3` (`DPLStructure.lean:961`), which
  is SAT-verified via the Cat 2 axiom `lem_compress3_general` (or its
  $b = 4$ specialization).
-/
def MultiplesSubColoringPopulationB4 : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring 63 3 χ →
    AvoidsMonoSolution 4 63 χ →
    ∃ c, c < 3 ∧
      ((Finset.Icc 1 15).filter (fun d => χ (4 * d) = c)).card ≥ 6

/-! ### R440 Phase 4 — analytic bundle for $b = 4$ at $n = 63$.

  We collect the kernel-pure analytic constraints that R440's structural
  probe identifies as the b=4 "spine" of the obstruction:

  * Self-loop type-($x = z$) at $m \in \{4, 8, 12\}$: at b=4, the v_4=2
    multiples are $\{16, 32, 48\}$, each of which sits on a self-loop
    triple $(b m, (b - 1) m, b m) = (4m, 3m, 4m)$ with $m$ a multiple
    of $b$ (and so $4m$ is a v_4=2 position).  For $m = 4$: triple
    $(16, 12, 16)$, forces $\chi(16) \ne \chi(12)$.  For $m = 8$:
    $(32, 24, 32)$, forces $\chi(32) \ne \chi(24)$.  For $m = 12$:
    $(48, 36, 48)$, forces $\chi(48) \ne \chi(36)$.
  * Self-loop type-($x = y$) at the same $m$ values: triple
    $(b m, b m, (b + 1) m)$ forces $\chi((b + 1) m) \ne \chi(b m)$.
    For $m = 4$: $\chi(20) \ne \chi(16)$.  For $m = 8$: $\chi(40) \ne
    \chi(32)$.  For $m = 12$: $\chi(60) \ne \chi(48)$.
  * Cross-position triples involving the v_4=2 multiples: $(16, 4, 8)$,
    $(32, 8, 16)$, $(48, 12, 24)$ etc., recorded as F2 in R440 Phase 1.

  Together these constraints force every $v_4 = 1$ multiple (positions
  $\{4, 8, 12, 20, 24, 28, 36, 40, 44, 52, 56, 60\}$, all multiples
  of 4 not divisible by 16) to disagree with at least one of $\{16,
  32, 48\}$.  By the SAT diagnostic, this disagreement propagates to a
  full color-class collapse, but the propagation step IS the obstruction
  (Stop C).

  This bundle DOES NOT prove `MultiplesSubColoringPopulationB4` —
  it is the maximum analytic content R440 extracts at $b = 4$
  kernel-pure, parallel to R438's `rounds_1_7_constraint_bundle`.
-/

/--
  **R440 b=4 self-loop bundle around the v_4 = 2 multiples.**

  For every valid mono-free 3-coloring of $\{1, \ldots, n\}$ with
  $n \ge 60$:

  (a) **v_4 = 2 forced disagreements**:
      $\chi(16) \ne \chi(12)$, $\chi(20) \ne \chi(16)$,
      $\chi(32) \ne \chi(24)$, $\chi(40) \ne \chi(32)$,
      $\chi(48) \ne \chi(36)$, $\chi(60) \ne \chi(48)$.

  All six inequalities come from $b = 4$ specializations of
  `self_loop_eq_left` and `self_loop_eq_right` at $m \in \{4, 8, 12\}$.

  Strictly kernel-pure.
-/
theorem b4_multiples_local_self_loop_bundle {n : ℕ} (hn : 60 ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ (4 * 4) ≠ χ ((4 - 1) * 4) ∧
    χ ((4 + 1) * 4) ≠ χ (4 * 4) ∧
    χ (4 * 8) ≠ χ ((4 - 1) * 8) ∧
    χ ((4 + 1) * 8) ≠ χ (4 * 8) ∧
    χ (4 * 12) ≠ χ ((4 - 1) * 12) ∧
    χ ((4 + 1) * 12) ≠ χ (4 * 12) := by
  have hb : (2 : ℕ) ≤ 4 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- m = 4: (16, 12, 16) self-loop type x=z, χ(4 * 4) ≠ χ((4-1) * 4).
    exact self_loop_eq_left hb (by decide : 1 ≤ 4) (by linarith) χ hAvoid
  · -- m = 4: (16, 16, 20) self-loop type x=y, χ((4+1) * 4) ≠ χ(4 * 4).
    exact self_loop_eq_right hb (by decide : 1 ≤ 4) (by linarith) χ hAvoid
  · -- m = 8: (32, 24, 32) self-loop type x=z, χ(4 * 8) ≠ χ((4-1) * 8).
    exact self_loop_eq_left hb (by decide : 1 ≤ 8) (by linarith) χ hAvoid
  · -- m = 8: (32, 32, 40) self-loop type x=y, χ((4+1) * 8) ≠ χ(4 * 8).
    exact self_loop_eq_right hb (by decide : 1 ≤ 8) (by linarith) χ hAvoid
  · -- m = 12: (48, 36, 48) self-loop type x=z, χ(4 * 12) ≠ χ((4-1) * 12).
    exact self_loop_eq_left hb (by decide : 1 ≤ 12) (by linarith) χ hAvoid
  · -- m = 12: (48, 48, 60) self-loop type x=y, χ((4+1) * 12) ≠ χ(4 * 12).
    exact self_loop_eq_right hb (by decide : 1 ≤ 12) (by linarith) χ hAvoid

/--
  **R440 b=4 self-loop bundle, in numeric form.**

  Same content as `b4_multiples_local_self_loop_bundle` but with the
  multiplications evaluated to numeric form for direct paper readout.

  Strictly kernel-pure.
-/
theorem b4_multiples_local_self_loop_bundle_numeric {n : ℕ} (hn : 60 ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 16 ≠ χ 12 ∧ χ 20 ≠ χ 16 ∧
    χ 32 ≠ χ 24 ∧ χ 40 ≠ χ 32 ∧
    χ 48 ≠ χ 36 ∧ χ 60 ≠ χ 48 := by
  have h := b4_multiples_local_self_loop_bundle hn χ hAvoid
  -- Convert each (b * m) and ((b-1)*m) / ((b+1)*m) to numeric.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- χ (4*4) = χ 16 and χ ((4-1)*4) = χ 12.
    have h1 : (4 * 4 : ℕ) = 16 := by decide
    have h2 : ((4 - 1) * 4 : ℕ) = 12 := by decide
    rw [h1, h2] at h
    exact h.1
  · have h1 : ((4 + 1) * 4 : ℕ) = 20 := by decide
    have h2 : (4 * 4 : ℕ) = 16 := by decide
    rw [h1, h2] at h
    exact h.2.1
  · have h1 : (4 * 8 : ℕ) = 32 := by decide
    have h2 : ((4 - 1) * 8 : ℕ) = 24 := by decide
    rw [h1, h2] at h
    exact h.2.2.1
  · have h1 : ((4 + 1) * 8 : ℕ) = 40 := by decide
    have h2 : (4 * 8 : ℕ) = 32 := by decide
    rw [h1, h2] at h
    exact h.2.2.2.1
  · have h1 : (4 * 12 : ℕ) = 48 := by decide
    have h2 : ((4 - 1) * 12 : ℕ) = 36 := by decide
    rw [h1, h2] at h
    exact h.2.2.2.2.1
  · have h1 : ((4 + 1) * 12 : ℕ) = 60 := by decide
    have h2 : (4 * 12 : ℕ) = 48 := by decide
    rw [h1, h2] at h
    exact h.2.2.2.2.2

/-! ### R440 Phase 4 — F2 multiple-of-multiple constraints at $b = 4$.

  At $b = 4$, the F2 triples among multiples include $(16, 16, 20)$,
  $(32, 8, 16)$, $(48, 12, 24)$, etc.  These force constraints among
  pairs of multiples (with one of $\{16, 32, 48\}$ involved).
-/

/--
  **R440 b=4 F2 constraint: $\chi(16) \ne \chi(20)$.**

  From the Rado triple $(16, 16, 20)$: $16 + 4 \cdot 16 = 16 + 64 = 80 =
  4 \cdot 20$.  Monochromaticity at color $c$ would require $\chi(16) =
  \chi(16) = \chi(20) = c$, i.e., $\chi(20) = \chi(16)$.

  This is a SPECIALIZATION of `self_loop_eq_right` at $b = 4, m = 4$:
  $\chi((b + 1) m) \ne \chi(b m) = \chi(5 \cdot 4) \ne \chi(4 \cdot 4)$,
  i.e., $\chi(20) \ne \chi(16)$.  Already captured in
  `b4_multiples_local_self_loop_bundle_numeric.2.1`.

  Strictly kernel-pure.
-/
theorem b4_chi_20_ne_chi_16 {n : ℕ} (hn : 60 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 20 ≠ χ 16 :=
  (b4_multiples_local_self_loop_bundle_numeric hn χ hAvoid).2.1

/--
  **R440 b=4 — pair-level forced-disagreements bundle.**

  A clean summary of the 6 forced-disagree inequalities at $b = 4$
  that R440's structural probe identifies as the local "spine".  Each
  pair is a single-triple consequence (self-loop family at $b = 4$,
  $m \in \{4, 8, 12\}$).

  Strictly kernel-pure.
-/
theorem b4_six_forced_disagreements {n : ℕ} (hn : 60 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 16 ≠ χ 12 ∧ χ 20 ≠ χ 16 ∧
    χ 32 ≠ χ 24 ∧ χ 40 ≠ χ 32 ∧
    χ 48 ≠ χ 36 ∧ χ 60 ≠ χ 48 :=
  b4_multiples_local_self_loop_bundle_numeric hn χ hAvoid

/-! ### R440 Phase 4 — Stop C documentation.

  We DO NOT prove `MultiplesSubColoringPopulationB4`.  Doing so would
  require either:

  1. Invoking the SAT atom `lem_compress3_general` at $b = 4$
     (forbidden by R440 prompt and would re-introduce Cat 2 axiom).
  2. Performing the full case explosion on positions $\{1, \ldots, 63\}$
     identified at R438 Stop C — equivalent to a 105-triple MUS
     case analysis (per `R440_mus_extract.py`).
  3. Inventing a non-cascade, non-SAT analytic mechanism — open
     mathematics (paper §11.1 valuation-pattern conjecture, no
     analytic derivation in the literature).

  The structural diagnostic confirms:

  * Candidate I' (≥ 6 in some color) is TRUE at $b = 4$.
  * The strictly stronger fact "$(12, 3, 0)$ is the only multiples
    partition" is ALSO TRUE at $b = 4$.
  * No compact (sub-100-line) analytic proof exists for either
    claim that avoids the cascade or the full case enumeration.

  **Verdict R440**: Stop C.  The R440 attack confirms Candidate I'
  at $b = 4$ is TRUE but cannot be compactly proved analytically
  without re-invoking the forbidden machinery.

  **Recommendation for R441**: pivot to either
  (a) Candidate II (Valuation Forced Agreement at $v_4 = 1$), which
      paper §11.1 records as the deepest forced-agreement pattern and
      which R440 confirms is equivalent to the partition rigidity at
      $b = 4$; OR
  (b) Candidate III (First-Two-Multiples-Agree at $(b-1) b^2 = 48$),
      which paper §5 proves for $b = 3$ via the analytic
      `lem:k3b3pair` Step 1/2 + SAT Step 3, and which R440's chain
      extraction shows is forced at
      $b = 4$ only at $n_{\text{eff}} \ge 48$ — a domain match with
      Candidate III's natural domain.
-/

/--
  **R440 Stop C — formal record of the non-proof.**

  The statement `MultiplesSubColoringPopulationB4` is recorded as a
  `def : Prop` (NOT proven).  Its truth is SAT-verified at $b = 4$ but
  not kernel-pure.

  This `theorem` documents R440's non-progress: any direct kernel-pure
  proof of `MultiplesSubColoringPopulationB4` would require invoking
  `lem_compress3_general` (the Cat 2 SAT axiom at $k = 3$, $b = 4$),
  which we DO NOT do.

  Formally, this is just a `def`-unfolding identity — the statement
  IS what it IS, no proof needed.
-/
theorem multiples_subcoloring_population_b4_def_eq :
    MultiplesSubColoringPopulationB4 =
      (∀ χ : ℕ → ℕ, IsValidColoring 63 3 χ →
        AvoidsMonoSolution 4 63 χ →
        ∃ c, c < 3 ∧
          ((Finset.Icc 1 15).filter (fun d => χ (4 * d) = c)).card ≥ 6) :=
  rfl

end RadoNumbers
