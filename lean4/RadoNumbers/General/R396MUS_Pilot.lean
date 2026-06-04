import RadoNumbers.General.Bridge

/-! # R396 MUS Pilot — first 10 clauses

  Auto-generated from `data/r396_mus_core.csv` by
  `src/R397_generate_mus_lean.py`.

  Each clause encodes one no-mono triple `(x, y, z)` with color `k`
  satisfying `x + 3·y = 3·z`. The proof is a one-line invocation of
  `bAdicEquation_3_same_color_excl` (R397, Bridge.lean §226).

  Demonstrates that all 1504 R396 MUS clauses can be discharged
  mechanically through a single theorem template.
-/

namespace RadoNumbers.General

/-- **R396 MUS clause #0000** — same-color exclusion for triple
  `(9, 9, 12)` at color `1`. Arithmetic: 9 + 3·9 = 36 = 3·12.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0000 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 9 = 1) :
    χ 12 ≠ 1 := by
  intro h12_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 9) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (9 + 3) = 1
  rw [show (9 + 3 : ℕ) = 12 by decide]
  exact h12_eq

/-- **R396 MUS clause #0001** — same-color exclusion for triple
  `(9, 21, 24)` at color `1`. Arithmetic: 9 + 3·21 = 72 = 3·24.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0001 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 21 = 1) :
    χ 24 ≠ 1 := by
  intro h24_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 21) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (21 + 3) = 1
  rw [show (21 + 3 : ℕ) = 24 by decide]
  exact h24_eq

/-- **R396 MUS clause #0002** — same-color exclusion for triple
  `(9, 36, 39)` at color `1`. Arithmetic: 9 + 3·36 = 117 = 3·39.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0002 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 36 = 1) :
    χ 39 ≠ 1 := by
  intro h39_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 36) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (36 + 3) = 1
  rw [show (36 + 3 : ℕ) = 39 by decide]
  exact h39_eq

/-- **R396 MUS clause #0003** — same-color exclusion for triple
  `(9, 40, 43)` at color `1`. Arithmetic: 9 + 3·40 = 129 = 3·43.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0003 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 40 = 1) :
    χ 43 ≠ 1 := by
  intro h43_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 40) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (40 + 3) = 1
  rw [show (40 + 3 : ℕ) = 43 by decide]
  exact h43_eq

/-- **R396 MUS clause #0004** — same-color exclusion for triple
  `(9, 41, 44)` at color `1`. Arithmetic: 9 + 3·41 = 132 = 3·44.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0004 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 41 = 1) :
    χ 44 ≠ 1 := by
  intro h44_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 41) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (41 + 3) = 1
  rw [show (41 + 3 : ℕ) = 44 by decide]
  exact h44_eq

/-- **R396 MUS clause #0005** — same-color exclusion for triple
  `(9, 42, 45)` at color `1`. Arithmetic: 9 + 3·42 = 135 = 3·45.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0005 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 42 = 1) :
    χ 45 ≠ 1 := by
  intro h45_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 42) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (42 + 3) = 1
  rw [show (42 + 3 : ℕ) = 45 by decide]
  exact h45_eq

/-- **R396 MUS clause #0006** — same-color exclusion for triple
  `(9, 44, 47)` at color `1`. Arithmetic: 9 + 3·44 = 141 = 3·47.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0006 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 44 = 1) :
    χ 47 ≠ 1 := by
  intro h47_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 44) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (44 + 3) = 1
  rw [show (44 + 3 : ℕ) = 47 by decide]
  exact h47_eq

/-- **R396 MUS clause #0007** — same-color exclusion for triple
  `(9, 49, 52)` at color `1`. Arithmetic: 9 + 3·49 = 156 = 3·52.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0007 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 49 = 1) :
    χ 52 ≠ 1 := by
  intro h52_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 49) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (49 + 3) = 1
  rw [show (49 + 3 : ℕ) = 52 by decide]
  exact h52_eq

/-- **R396 MUS clause #0008** — same-color exclusion for triple
  `(9, 51, 54)` at color `1`. Arithmetic: 9 + 3·51 = 162 = 3·54.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0008 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 51 = 1) :
    χ 54 ≠ 1 := by
  intro h54_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 51) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (51 + 3) = 1
  rw [show (51 + 3 : ℕ) = 54 by decide]
  exact h54_eq

/-- **R396 MUS clause #0009** — same-color exclusion for triple
  `(9, 54, 57)` at color `1`. Arithmetic: 9 + 3·54 = 171 = 3·57.

  Auto-generated from R396 SAT MUS. -/
theorem mus_clause_0009 {n : ℕ} (h81 : 81 ≤ n) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hxk : χ 9 = 1) (hyk : χ 54 = 1) :
    χ 57 ≠ 1 := by
  intro h57_eq
  apply bAdicEquation_3_same_color_excl χ hNoMono
    (d := 3) (y := 54) (k := 1)
    (by omega) (by omega) (by omega) (by omega)
    (by show χ (3 * 3) = 1; rw [show (3 * 3 : ℕ) = 9 by decide]; exact hxk)
    hyk
  show χ (54 + 3) = 1
  rw [show (54 + 3 : ℕ) = 57 by decide]
  exact h57_eq


end RadoNumbers.General
