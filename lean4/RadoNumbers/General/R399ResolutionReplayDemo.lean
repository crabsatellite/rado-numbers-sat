import RadoNumbers.General.Bridge

/-! # R399 LRAT-style resolution replay demo

  Demonstrates the proof-replay primitive that R400 will use to convert
  cadical's LRAT proof of symbolic Branch II UNSAT into a kernel-pure
  Lean theorem.

  ## LRAT step structure

  An LRAT add step has the form:
    `<step_id> <literals> 0 <antecedent_ids> 0`

  meaning: a new clause (disjunction of `literals`) is derived from the
  earlier clauses with the given `antecedent_ids` via unit propagation.
  Specifically, asserting the negation of `literals` and unit-propagating
  through `antecedent_ids` produces a conflict.

  ## Replay primitive

  Each LRAT step becomes a Lean theorem of the form:

    theorem step_NNNN (... antecedent witnesses ...) :
        ⊢ disjunction_of_literals
      := by ...

  proved by introducing negations of literals (i.e., the `literals` clause
  is false), running unit propagation over the antecedents, and deriving
  the missing literal via R397 generic theorem or branch assumptions.

  The final step derives the empty clause, giving `False`.

  ## Initial clause translation

  Each initial CNF clause (line in the DIMACS file) is one of:

    | label-kind        | Lean derivation                                  |
    |-------------------|--------------------------------------------------|
    | alo(i)            | hχk i (by omega) (by omega) gives `χ i < 4`,    |
    |                   | hence one of `x[i,0..3]` holds                  |
    | amo(i,c,d)        | function uniqueness: `¬(χ i = c ∧ χ i = d)`     |
    | eq27_81_fwd(c)    | from `h27_eq_81`                                 |
    | eq27_81_bwd(c)    | from `h27_eq_81.symm`                            |
    | ne9_27(c)         | from `h9_ne_27`                                  |
    | ne18_9(c)         | from `h18_ne_9`                                  |
    | ne18_27(c)        | from `h18_ne_27` (or derivable from R314)        |
    | no_mono(x,y,z,k)  | from `bAdicEquation_3_same_color_excl` (R397)    |

  ## Demo: single LRAT step

  Below we demonstrate one resolution step in Lean. The example uses
  the no-mono clause for triple (60, 28, 48) at color B and the unit
  clauses χ48 = B, χ60 = B, χ28 = B — derived from the R398 prototype.

  We use position-with-color literals as `χ i = k` propositions.
-/

namespace RadoNumbers.General

/-- **R399 demo — initial clause translation: no-mono clause for
  triple (60, 28, 48) at color B**.

  Demonstrates that an initial CNF no-mono clause is mechanically
  derived from R397's `bAdicEquation_3_same_color_excl`.

  Clause: `¬x[60,B] ∨ ¬x[28,B] ∨ ¬x[48,B]`
  Equivalently: `χ 60 ≠ B ∨ χ 28 ≠ B ∨ χ 48 ≠ B`. -/
theorem r399_demo_initial_clause_no_mono_60_28_48_B
    {n : ℕ} (h60 : 60 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 60 ≠ χ 9 ∨ χ 28 ≠ χ 9 ∨ χ 48 ≠ χ 9 := by
  -- Decidable case split: avoid Classical/by_contra/push_neg.
  if h60_eq : χ 60 = χ 9 then
  if h28_eq : χ 28 = χ 9 then
    -- Both equal: derive χ 48 ≠ χ 9 via R397.
    refine Or.inr (Or.inr ?_)
    intro h48_eq
    apply bAdicEquation_3_same_color_excl χ hNoMono
      (d := 20) (y := 28) (k := χ 9)
      (by omega) (by omega) (by omega) (by omega)
      (by show χ (3 * 20) = χ 9; rw [show (3 * 20 : ℕ) = 60 by decide]; exact h60_eq)
      h28_eq
    show χ (28 + 20) = χ 9
    rw [show (28 + 20 : ℕ) = 48 by decide]
    exact h48_eq
  else
    exact Or.inr (Or.inl h28_eq)
  else
    exact Or.inl h60_eq

/-- **R399 demo — LRAT resolution step**: from the initial no-mono
  clause `χ60≠B ∨ χ28≠B ∨ χ48≠B` and unit clauses `χ60=B`, `χ28=B`,
  `χ48=B`, derive the empty clause (= False).

  This is one resolution step in LRAT format: three unit-propagation
  resolves from the three antecedents.

  Same content as `r398_demo_chi48B_chi60B_chi28B_resolution_false`
  but using the clausal `r399_demo_initial_clause_no_mono_60_28_48_B`
  as antecedent. -/
theorem r399_demo_resolution_step_to_false
    {n : ℕ} (h60 : 60 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (C1_h48_eq_9 : χ 48 = χ 9)
    (C2_h60_eq_9 : χ 60 = χ 9)
    (C3_h28_eq_9 : χ 28 = χ 9) :
    False := by
  -- Antecedent C4: the initial no-mono clause.
  have C4_clause := r399_demo_initial_clause_no_mono_60_28_48_B
    (h60 := h60) (χ := χ) (hNoMono := hNoMono)
  -- C4 : χ60 ≠ B ∨ χ28 ≠ B ∨ χ48 ≠ B.
  -- Resolution-replay: each disjunct contradicts the corresponding unit.
  rcases C4_clause with h60_ne | h28_ne | h48_ne
  · exact h60_ne C2_h60_eq_9
  · exact h28_ne C3_h28_eq_9
  · exact h48_ne C1_h48_eq_9

end RadoNumbers.General
