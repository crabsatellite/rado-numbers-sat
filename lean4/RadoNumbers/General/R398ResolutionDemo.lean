import RadoNumbers.General.Bridge

/-! # R398 resolution-style proof demo

  Demonstrates the proof-assembly pattern that R399 will scale to the
  full Branch II MUS: derive `False` from a small set of unit
  assumptions + a no-mono clause via simple resolution.

  The demo theorem is logically identical to R391 Part 1-E
  `chi48B_chi60B_chi28B_false` but written in resolution-replay style
  to illustrate the mechanical pattern:

    Clause C1 : χ 48 = χ 9
    Clause C2 : χ 60 = χ 9
    Clause C3 : χ 28 = χ 9
    Clause C4 : ¬(χ 48 = χ 9 ∧ χ 60 = χ 9 ∧ χ 28 = χ 9)
                (= no-mono on (60, 28, 48) at color B)

  Resolution: C4 + C1, C2, C3 → empty (False).
-/

namespace RadoNumbers.General

/-- **R398 demo — Branch II resolution-style False derivation**.

  Same content as R391 `chi48B_chi60B_chi28B_false`. Written explicitly
  in three-conjunction-then-resolve form to mirror the SAT proof trace
  that R399 will replay mechanically. -/
theorem r398_demo_chi48B_chi60B_chi28B_resolution_false
    {n : ℕ} (h60 : 60 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    -- Three unit clauses (R398 "C1", "C2", "C3"):
    (C1_h48_eq_9 : χ 48 = χ 9)
    (C2_h60_eq_9 : χ 60 = χ 9)
    (C3_h28_eq_9 : χ 28 = χ 9) :
    False := by
  -- Clause C4: no-mono on (60, 28, 48) at color χ9.
  -- Derived from R391 same-color exclusion (60, 28, 48):
  --   χ60 = χ9 ∧ χ28 = χ9 → χ48 ≠ χ9.
  have C4_h48_ne_9 :=
    bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
      χ h60 hNoMono C2_h60_eq_9 C3_h28_eq_9
  -- Resolution: C4 contradicts C1.
  exact C4_h48_ne_9 C1_h48_eq_9

/-- **R398 demo via generic theorem** — same derivation through the
  R397 generic same-color exclusion `bAdicEquation_3_same_color_excl`.

  Demonstrates that any concrete same-color exclusion clause can be
  obtained from the single generic theorem with appropriate (d, y, k)
  parameters. Triple (60, 28, 48) corresponds to d=20, y=28. -/
theorem r398_demo_via_generic_excl
    {n : ℕ} (h60 : 60 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h60_eq_9 : χ 60 = χ 9)
    (h28_eq_9 : χ 28 = χ 9) :
    False := by
  -- Use generic theorem with d=20, y=28: triple (3·20, 28, 28+20) = (60, 28, 48).
  have h48_ne_9 := bAdicEquation_3_same_color_excl χ hNoMono
    (d := 20) (y := 28) (k := χ 9)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 20) = χ 9; rw [show (3 * 20 : ℕ) = 60 by decide]; exact h60_eq_9)
    h28_eq_9
  -- result: χ (28 + 20) ≠ χ 9
  apply h48_ne_9
  show χ (28 + 20) = χ 9
  rw [show (28 + 20 : ℕ) = 48 by decide]
  exact h48_eq_9

end RadoNumbers.General
