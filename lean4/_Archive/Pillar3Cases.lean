/-
  _Archive/Pillar3Cases.lean

  ARCHIVED Pillar 3 sub-step theorems (Rounds 147-170) from brute-force
  case enumeration phase. Per user instruction (严禁单纯暴力单case慢慢解),
  these per-case theorems are MOVED OUT of default build to speed up iteration.

  They remain kernel-pure proofs (committed in git history) but do NOT
  affect lake build of RadoNumbers library.

  To rebuild manually: lake env lean _Archive/Pillar3Cases.lean
-/

import RadoNumbers.Foundational

namespace RadoNumbers

/-! ### §33.22. Round 147 — Pillar 3 sub-step: local shift inconsistency at m=2.

  **Sub-claim**: under mono-free 3-coloring χ of {1, ..., 27} for b=3
  with χ(1) = 0, χ(3) = 0 (forcing local shift S(1) = 0 at m=1),
  and assuming the alternative configuration χ(2) = 1, χ(6) = 2
  (which would mean S(2) = 1 ≠ S(1) = 0), the chi(10) constraints
  are jointly INCONSISTENT in a sub-case.

  Specifically, under additional χ(9) = 0 (one of two natural cases),
  triples (3, 9, 10), (18, 4, 10), (12, 6, 10) force χ(10) ∉ {0, 1, 2}
  — IMPOSSIBLE in 3-coloring.

  This is a STEP toward proving S(m) is constant (Pillar 3): any
  inconsistency in local shifts cascades through Rado triples to
  contradiction.
-/

/--
  **Round 147 — Sub-step of Pillar 3: chi(10) impossibility under
  configuration with local-shift inconsistency at m=2 and chi(9)=0.**

  Forces structural uniqueness of the multiplicative shift at m=2.
-/
theorem pillar_3_substep_chi_10_impossible :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 0 ∧ χ 12 = 2 ∧ χ 18 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12, hχ18⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  -- chi(10) ≠ 0 from (3, 9, 10): chi(3)=chi(9)=0.
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ9]
    · rw [hχ9, h]
  -- chi(10) ≠ 1 from (18, 4, 10): chi(18)=chi(4)=1.
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ18, hχ4]
    · rw [hχ4, h]
  -- chi(10) ≠ 2 from (12, 6, 10): chi(12)=chi(6)=2.
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 12 6 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ6]
    · rw [hχ6, h]
  omega

/-! ### §33.23. Round 148 — Pillar 3 sub-step: chi(9)=1, chi(12)=0 forces mono (6,5,7).
-/

/--
  **Round 148 — Pillar 3 sub-step variant: chi(9)=1, chi(12)=0 case.**

  Under mono-free 3-coloring with chi(1)=0, chi(2)=1, chi(3)=0,
  chi(6)=2, chi(4)=1, chi(9)=1, chi(12)=0, the values chi(5) and
  chi(7) are forced to 2, then (6, 5, 7) is mono.
-/
theorem pillar_3_substep_mono_657 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 1 ∧ χ 12 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hValid 7 (by norm_num) (by omega)
  -- χ(5) ≠ 0 from (12, 1, 5): chi(12)=chi(1)=0.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 12 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ1]
    · rw [hχ1, h]
  -- χ(5) ≠ 1 from (9, 2, 5): chi(9)=chi(2)=1.
  have h_5_ne_1 : χ 5 ≠ 1 := by
    intro h
    apply mono 9 2 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, hχ2]
    · rw [hχ2, h]
  have h_5 : χ 5 = 2 := by omega
  -- χ(7) ≠ 0 from (12, 3, 7): chi(12)=chi(3)=0.
  have h_7_ne_0 : χ 7 ≠ 0 := by
    intro h
    apply mono 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ3]
    · rw [hχ3, h]
  -- χ(7) ≠ 1 from (9, 4, 7): chi(9)=chi(4)=1.
  have h_7_ne_1 : χ 7 ≠ 1 := by
    intro h
    apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, hχ4]
    · rw [hχ4, h]
  have h_7 : χ 7 = 2 := by omega
  -- (6, 5, 7) mono: chi(6)=chi(5)=chi(7)=2.
  apply mono 6 5 7 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [hχ6, h_5]
  · rw [h_5, h_7]

/-! ### §33.24. Round 149 — Pillar 3 sub-step: chi(12)=2, chi(7)=0 forces mono via chi(13) split. -/

/--
  **Round 149 — Pillar 3 sub-step: chi(12)=2, chi(7)=0 case.**

  Under mono-free 3-coloring with chi(1)=0, chi(3)=0, chi(2)=1,
  chi(6)=2, chi(4)=1, chi(9)=1, chi(12)=2, chi(7)=0, a long
  forcing chain derives mono. The chain forces:

  - chi(5) = 0 via (6,5,6) self-loop ∧ (9,2,5).
  - chi(8) = 1 via (3,7,8) ∧ (12,8,12) self-loop.
  - chi(18) = 1 via (18,1,7) ∧ (18,12,18) self-loop.
  - chi(10) = 0 via (6,10,12) ∧ (18,4,10).
  - chi(15) = 2 via (15,4,9) ∧ (15,5,10).
  - chi(11) = 1 via (3,10,11) ∧ (12,11,15).
  - chi(13) ≠ 2 via (6,13,15).

  Then case-split on chi(13) ∈ {0, 1}:
  - chi(13) = 0: chi(14) excluded from all of {0, 1, 2}.
  - chi(13) = 1: forces chi(16) = 0, chi(17) = 2, then (6,15,17) mono.
-/
theorem pillar_3_substep_chi_12_eq_2_chi_7_eq_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 1 ∧ χ 12 = 2 ∧ χ 7 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12, hχ7⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hValid 11 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
  have hv14 : χ 14 < 3 := hValid 14 (by norm_num) (by omega)
  have hv15 : χ 15 < 3 := hValid 15 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hValid 16 (by norm_num) (by omega)
  have hv17 : χ 17 < 3 := hValid 17 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- χ(8) = 1: (3, 7, 8) forces χ(8) ≠ 0; self-loop (12, 8, 12) forces χ(8) ≠ 2.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ7]
    · rw [hχ7, h]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 1 := by omega
  -- χ(18) = 1: (18, 1, 7) forces χ(18) ≠ 0; self-loop (18, 12, 18) forces χ(18) ≠ 2.
  have h_18_ne_0 : χ 18 ≠ 0 := by
    intro h
    apply mono 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ1]
    · rw [hχ1, hχ7]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 1 := by omega
  -- χ(10) = 0: (6, 10, 12) forces χ(10) ≠ 2; (18, 4, 10) forces χ(10) ≠ 1.
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, hχ12]
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, hχ4]
    · rw [hχ4, h]
  have h_10 : χ 10 = 0 := by omega
  -- χ(15) = 2: (15, 4, 9) forces χ(15) ≠ 1; self-loop (15, 10, 15) forces χ(15) ≠ 0.
  have h_15_ne_1 : χ 15 ≠ 1 := by
    intro h
    apply mono 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ4]
    · rw [hχ4, hχ9]
  have h_15_ne_0 : χ 15 ≠ 0 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, h_10]
    · rw [h_10, h]
  have h_15 : χ 15 = 2 := by omega
  -- χ(11) = 1: (3, 10, 11) forces χ(11) ≠ 0; (12, 11, 15) forces χ(11) ≠ 2.
  have h_11_ne_0 : χ 11 ≠ 0 := by
    intro h
    apply mono 3 10 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h_10]
    · rw [h_10, h]
  have h_11_ne_2 : χ 11 ≠ 2 := by
    intro h
    apply mono 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, h_15]
  have h_11 : χ 11 = 1 := by omega
  -- χ(13) ≠ 2 via (6, 13, 15).
  have h_13_ne_2 : χ 13 ≠ 2 := by
    intro h
    apply mono 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, h_15]
  -- Case split on χ(13) ∈ {0, 1}.
  rcases (show χ 13 = 0 ∨ χ 13 = 1 from by omega) with h_13 | h_13
  · -- Case χ(13) = 0: chi(14) impossible.
    have h_14_ne_0 : χ 14 ≠ 0 := by
      intro h
      apply mono 3 13 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_13]
      · rw [h_13, h]
    have h_14_ne_1 : χ 14 ≠ 1 := by
      intro h
      apply mono 9 11 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_11]
      · rw [h_11, h]
    have h_14_ne_2 : χ 14 ≠ 2 := by
      intro h
      apply mono 6 12 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, hχ12]
      · rw [hχ12, h]
    omega
  · -- Case χ(13) = 1: forces χ(16)=0, χ(17)=2, then (6, 15, 17) mono.
    have h_16_ne_1 : χ 16 ≠ 1 := by
      intro h
      apply mono 9 13 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_13]
      · rw [h_13, h]
    have h_16_ne_2 : χ 16 ≠ 2 := by
      intro h
      apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [hχ12, h]
    have h_16 : χ 16 = 0 := by omega
    have h_17_ne_0 : χ 17 ≠ 0 := by
      intro h
      apply mono 3 16 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_16]
      · rw [h_16, h]
    have h_17_ne_1 : χ 17 ≠ 1 := by
      intro h
      apply mono 18 11 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_11]
      · rw [h_11, h]
    have h_17 : χ 17 = 2 := by omega
    -- (6, 15, 17): χ(6)=χ(15)=χ(17)=2 mono.
    apply mono 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h_15]
    · rw [h_15, h_17]

/-! ### §33.25. Round 150 — Pillar 3 sub-step: chi(12)=2, chi(7)=2 forces mono via chi(11) split. -/

/--
  **Round 150 — Pillar 3 sub-step: chi(12)=2, chi(7)=2 case.**

  Under mono-free 3-coloring with chi(1)=0, chi(3)=0, chi(2)=1,
  chi(6)=2, chi(4)=1, chi(9)=1, chi(12)=2, chi(7)=2, the forcing
  chain produces:

  - chi(5) = 0 via (6,5,6) self-loop ∧ (9,2,5).
  - chi(15) = 0 via (15,4,9) ∧ (15,7,12).
  - chi(10) = 1 via (15,10,15) self-loop ∧ (6,10,12).
  - chi(8) = 1 via (15,3,8) ∧ (12,8,12) self-loop.
  - chi(18) = 0 via (18,4,10) ∧ self-loop (18,12,18).
  - chi(13) = 2 via (9,10,13) ∧ (15,13,18).
  - chi(16) = 1 via (3,15,16) ∧ (12,12,16) self-loop.
  - chi(11) ≠ 2 via (12,7,11).

  Case-split on chi(11) ∈ {0, 1}:
  - chi(11) = 0: forces chi(17)=1, chi(20)=2, chi(24)=0, mono (24,3,11).
  - chi(11) = 1: forces chi(14)=0, mono (3,14,15).
-/
theorem pillar_3_substep_chi_12_eq_2_chi_7_eq_2 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 1 ∧ χ 12 = 2 ∧ χ 7 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12, hχ7⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hValid 11 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
  have hv14 : χ 14 < 3 := hValid 14 (by norm_num) (by omega)
  have hv15 : χ 15 < 3 := hValid 15 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hValid 16 (by norm_num) (by omega)
  have hv17 : χ 17 < 3 := hValid 17 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  have hv20 : χ 20 < 3 := hValid 20 (by norm_num) (by omega)
  have hv24 : χ 24 < 3 := hValid 24 (by norm_num) (by omega)
  -- χ(15) = 0: (15,4,9) forces ≠ 1; (15,7,12) forces ≠ 2.
  have h_15_ne_1 : χ 15 ≠ 1 := by
    intro h
    apply mono 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ4]
    · rw [hχ4, hχ9]
  have h_15_ne_2 : χ 15 ≠ 2 := by
    intro h
    apply mono 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ7]
    · rw [hχ7, hχ12]
  have h_15 : χ 15 = 0 := by omega
  -- χ(10) = 1: self-loop (15,10,15) forces ≠ 0; (6,10,12) forces ≠ 2.
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h]
    · rw [h, h_15]
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, hχ12]
  have h_10 : χ 10 = 1 := by omega
  -- χ(8) = 1: (15,3,8) forces ≠ 0; self-loop (12,8,12) forces ≠ 2.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, hχ3]
    · rw [hχ3, h]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 1 := by omega
  -- χ(18) = 0: (18,4,10) forces ≠ 1; self-loop (18,12,18) forces ≠ 2.
  have h_18_ne_1 : χ 18 ≠ 1 := by
    intro h
    apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ4]
    · rw [hχ4, h_10]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 0 := by omega
  -- χ(13) = 2: (9,10,13) forces ≠ 1; (15,13,18) forces ≠ 0.
  have h_13_ne_1 : χ 13 ≠ 1 := by
    intro h
    apply mono 9 10 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, h_10]
    · rw [h_10, h]
  have h_13_ne_0 : χ 13 ≠ 0 := by
    intro h
    apply mono 15 13 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h]
    · rw [h, h_18]
  have h_13 : χ 13 = 2 := by
    have : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
    omega
  -- χ(16) = 1: (3,15,16) forces ≠ 0; self-loop (12,12,16) forces ≠ 2.
  have h_16_ne_0 : χ 16 ≠ 0 := by
    intro h
    apply mono 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h_15]
    · rw [h_15, h]
  have h_16_ne_2 : χ 16 ≠ 2 := by
    intro h
    apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ12, h]
  have h_16 : χ 16 = 1 := by omega
  -- χ(11) ≠ 2 via (12,7,11).
  have h_11_ne_2 : χ 11 ≠ 2 := by
    intro h
    apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ7]
    · rw [hχ7, h]
  -- Case split on χ(11) ∈ {0, 1}.
  rcases (show χ 11 = 0 ∨ χ 11 = 1 from by omega) with h_11 | h_11
  · -- Case χ(11) = 0.
    have h_17_ne_0 : χ 17 ≠ 0 := by
      intro h
      apply mono 18 11 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_11]
      · rw [h_11, h]
    have h_17_ne_2 : χ 17 ≠ 2 := by
      intro h
      apply mono 12 13 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h_13]
      · rw [h_13, h]
    have h_17 : χ 17 = 1 := by omega
    have h_20_ne_0 : χ 20 ≠ 0 := by
      intro h
      apply mono 15 15 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_15, h]
    have h_20_ne_1 : χ 20 ≠ 1 := by
      intro h
      apply mono 9 17 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_17]
      · rw [h_17, h]
    have h_20 : χ 20 = 2 := by omega
    have h_24_ne_1 : χ 24 ≠ 1 := by
      intro h
      apply mono 24 2 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ2]
      · rw [hχ2, h_10]
    have h_24_ne_2 : χ 24 ≠ 2 := by
      intro h
      apply mono 24 12 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ12]
      · rw [hχ12, h_20]
    have h_24 : χ 24 = 0 := by omega
    -- (24, 3, 11): χ(24)=χ(3)=χ(11)=0 mono.
    apply mono 24 3 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_24, hχ3]
    · rw [hχ3, h_11]
  · -- Case χ(11) = 1.
    have h_14_ne_1 : χ 14 ≠ 1 := by
      intro h
      apply mono 9 11 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_11]
      · rw [h_11, h]
    have h_14_ne_2 : χ 14 ≠ 2 := by
      intro h
      apply mono 6 12 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, hχ12]
      · rw [hχ12, h]
    have h_14 : χ 14 = 0 := by omega
    -- (3, 14, 15): χ(3)=χ(14)=χ(15)=0 mono.
    apply mono 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h_14]
    · rw [h_14, h_15]

/-! ### §33.26. Round 151 — Pillar 3 combination: chi(9)=1 closes via chi(12) and chi(7) splits. -/

/--
  **Round 151 — Pillar 3 sub-step (chi(9)=1 closure).**

  Combines Round 148 (chi(12)=0), Round 149 (chi(12)=2 ∧ chi(7)=0),
  and Round 150 (chi(12)=2 ∧ chi(7)=2). Under chi(2)=1, chi(6)=2,
  chi(4)=1, chi(9)=1, self-loop (9,9,12) forces chi(12) ≠ 1 so
  chi(12) ∈ {0, 2}; Rado triple (9,4,7) forces chi(7) ≠ 1 so
  chi(7) ∈ {0, 2}.
-/
theorem pillar_3_chi_9_eq_1_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv12 : χ 12 < 3 := hValid 12 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hValid 7 (by norm_num) (by omega)
  -- Self-loop (9, 9, 12): χ(12) ≠ χ(9) = 1.
  have h_12_ne_1 : χ 12 ≠ 1 := by
    intro h
    apply mono 9 9 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ9, h]
  rcases (show χ 12 = 0 ∨ χ 12 = 2 from by omega) with h_12 | h_12
  · -- χ(12) = 0: invoke Round 148.
    exact pillar_3_substep_mono_657
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, h_12⟩
  · -- χ(12) = 2: case split on χ(7).
    -- χ(7) ≠ 1 via (9, 4, 7).
    have h_7_ne_1 : χ 7 ≠ 1 := by
      intro h
      apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, hχ4]
      · rw [hχ4, h]
    rcases (show χ 7 = 0 ∨ χ 7 = 2 from by omega) with h_7 | h_7
    · -- χ(7) = 0: invoke Round 149.
      exact pillar_3_substep_chi_12_eq_2_chi_7_eq_0
        ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, h_12, h_7⟩
    · -- χ(7) = 2: invoke Round 150.
      exact pillar_3_substep_chi_12_eq_2_chi_7_eq_2
        ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, h_12, h_7⟩

/-! ### §33.27. Round 152 — Pillar 3 sub-step: chi(9)=0, chi(12)=1 forces mono via (3,8,9) + (6,6,8). -/

/--
  **Round 152 — Pillar 3 sub-step: chi(9)=0, chi(12)=1 case.**

  Short forcing chain (NO chi(7) hypothesis needed):
  - chi(8) = 2 via (3,8,9) forces ≠ 0; self-loop (12,8,12) forces ≠ 1.
  - mono via (6, 6, 8): chi(6) = chi(6) = chi(8) = 2.

  Key insight: (3, 8, 9) is a single-triple constraint forcing chi(8) ≠ 0
  whenever chi(3) = chi(9). With chi(3) = chi(9) = 0, this immediately gives
  chi(8) ≠ 0. Then chi(12) = 1 self-loop gives chi(8) ≠ 1, forcing chi(8) = 2.
  Triple (6, 6, 8) closes since chi(6) = chi(8) = 2.
-/
theorem pillar_3_substep_chi_9_eq_0_chi_12_eq_1 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 0 ∧ χ 12 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  -- χ(8) = 2: (3, 8, 9) forces ≠ 0; self-loop (12, 8, 12) forces ≠ 1.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h]
    · rw [h, hχ9]
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 2 := by omega
  -- (6, 6, 8): chi(6)=chi(6)=chi(8)=2 mono.
  apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rfl
  · rw [hχ6, h_8]

/-! ### §33.28. Round 153 — Pillar 3 wrapper: chi(9)=0, chi(12)=2 forces chi(18)=1 then Round 147. -/

/--
  **Round 153 — Pillar 3 wrapper: chi(9)=0, chi(12)=2 case.**

  Derives chi(18) = 1 from:
  - (18, 3, 9) forces chi(18) ≠ 0 (since chi(3) = chi(9) = 0).
  - Self-loop (18, 12, 18) forces chi(18) ≠ 2 (since chi(12) = 2).

  Then invokes Round 147 (pillar_3_substep_chi_10_impossible).
-/
theorem pillar_3_substep_chi_9_eq_0_chi_12_eq_2 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 0 ∧ χ 12 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- χ(18) = 1: (18, 3, 9) forces ≠ 0; self-loop (18, 12, 18) forces ≠ 2.
  have h_18_ne_0 : χ 18 ≠ 0 := by
    intro h
    apply mono 18 3 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ3]
    · rw [hχ3, hχ9]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 1 := by omega
  -- Invoke Round 147.
  exact pillar_3_substep_chi_10_impossible
    ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, hχ12, h_18⟩

/-! ### §33.29. Round 154 — Pillar 3 combination: chi(9)=0 closes via chi(12) split. -/

/--
  **Round 154 — Pillar 3 sub-step (chi(9)=0 closure).**

  Self-loop (9, 9, 12) gives chi(12) ≠ 0. Case split on chi(12) ∈ {1, 2}.
  - chi(12) = 1: invoke Round 152.
  - chi(12) = 2: invoke Round 153.
-/
theorem pillar_3_chi_9_eq_0_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧
      χ 4 = 1 ∧ χ 9 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv12 : χ 12 < 3 := hValid 12 (by norm_num) (by omega)
  -- Self-loop (9, 9, 12): χ(12) ≠ χ(9) = 0.
  have h_12_ne_0 : χ 12 ≠ 0 := by
    intro h
    apply mono 9 9 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ9, h]
  rcases (show χ 12 = 1 ∨ χ 12 = 2 from by omega) with h_12 | h_12
  · -- χ(12) = 1: invoke Round 152.
    exact pillar_3_substep_chi_9_eq_0_chi_12_eq_1
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, h_12⟩
  · -- χ(12) = 2: invoke Round 153.
    exact pillar_3_substep_chi_9_eq_0_chi_12_eq_2
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, hχ9, h_12⟩

/-! ### §33.30. Round 155 — Pillar 3 sub-step: full chi(9) closure via chi(6)=2, chi(4)=1, chi(3)=0, chi(2)=1, chi(1)=0. -/

/--
  **Round 155 — Pillar 3 sub-step (chi(9) closure).**

  Self-loop (9, 6, 9) gives chi(9) ≠ chi(6) = 2. Case split on chi(9) ∈ {0, 1}.
  - chi(9) = 0: invoke Round 154.
  - chi(9) = 1: invoke Round 151.

  This closes the case chi(1)=0, chi(3)=0, chi(2)=1, chi(6)=2, chi(4)=1
  completely.
-/
theorem pillar_3_chi_2_1_chi_6_2_chi_4_1_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 6 = 2 ∧ χ 4 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv9 : χ 9 < 3 := hValid 9 (by norm_num) (by omega)
  -- Self-loop (9, 6, 9): χ(9) ≠ χ(6) = 2.
  have h_9_ne_2 : χ 9 ≠ 2 := by
    intro h
    apply mono 9 6 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ6]
    · rw [hχ6, h]
  rcases (show χ 9 = 0 ∨ χ 9 = 1 from by omega) with h_9 | h_9
  · -- χ(9) = 0: invoke Round 154.
    exact pillar_3_chi_9_eq_0_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, h_9⟩
  · -- χ(9) = 1: invoke Round 151.
    exact pillar_3_chi_9_eq_1_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ6, hχ4, h_9⟩

/-! ### §33.31. Round 156 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=0, chi(12)=1 → mono (18,4,10). -/

/--
  **Round 156 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=0, chi(12)=1.**

  Forces chi(8) = 2, chi(18) = 2, chi(10) = 2, then (18, 4, 10) mono
  with all three = 2.
-/
theorem pillar_3_substep_chi_4_2_chi_6_1_chi_9_0_chi_12_1 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 0 ∧ χ 12 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- χ(8) = 2: (3,8,9) ≠ 0; self-loop (12,8,12) ≠ 1.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h]
    · rw [h, hχ9]
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 2 := by omega
  -- χ(18) = 2: (18,3,9) ≠ 0; self-loop (18,12,18) ≠ 1.
  have h_18_ne_0 : χ 18 ≠ 0 := by
    intro h
    apply mono 18 3 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ3]
    · rw [hχ3, hχ9]
  have h_18_ne_1 : χ 18 ≠ 1 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 2 := by omega
  -- χ(10) = 2: (3,9,10) ≠ 0; (6,10,12) ≠ 1.
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ9]
    · rw [hχ9, h]
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, hχ12]
  have h_10 : χ 10 = 2 := by omega
  -- (18, 4, 10) mono: chi(18)=chi(4)=chi(10)=2.
  apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [h_18, hχ4]
  · rw [hχ4, h_10]

/-! ### §33.32. Round 157 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=0, chi(12)=2 → mono (6,6,8). -/

/--
  **Round 157 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=0, chi(12)=2.**

  Forces chi(8) = 1, then (6, 6, 8) mono with chi(6) = chi(8) = 1.
-/
theorem pillar_3_substep_chi_4_2_chi_6_1_chi_9_0_chi_12_2 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 0 ∧ χ 12 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  -- χ(8) = 1: (3,8,9) ≠ 0; self-loop (12,8,12) ≠ 2.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h]
    · rw [h, hχ9]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 1 := by omega
  -- (6, 6, 8) mono: chi(6)=chi(6)=chi(8)=1.
  apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rfl
  · rw [hχ6, h_8]

/-! ### §33.33. Round 158 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=0 closure via chi(12) split. -/

/--
  **Round 158 — Pillar 3 sub-step (chi(9)=0 closure under chi(4)=2, chi(6)=1).**

  Self-loop (9,9,12) gives chi(12) ≠ 0. Dispatches to Round 156 (chi(12)=1)
  or Round 157 (chi(12)=2).
-/
theorem pillar_3_chi_4_2_chi_6_1_chi_9_0_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv12 : χ 12 < 3 := hValid 12 (by norm_num) (by omega)
  have h_12_ne_0 : χ 12 ≠ 0 := by
    intro h
    apply mono 9 9 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ9, h]
  rcases (show χ 12 = 1 ∨ χ 12 = 2 from by omega) with h_12 | h_12
  · exact pillar_3_substep_chi_4_2_chi_6_1_chi_9_0_chi_12_1
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, h_12⟩
  · exact pillar_3_substep_chi_4_2_chi_6_1_chi_9_0_chi_12_2
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, h_12⟩

/-! ### §33.34. Round 159 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=2, chi(12)=0 → mono (6,6,8). -/

/--
  **Round 159 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=2, chi(12)=0.**

  Chain forces chi(7) = 1, chi(5) = 2, chi(8) = 1, then (6, 6, 8) mono.
  Specifically:
  - chi(7) ≠ 0 via (12,3,7) [chi(12) = chi(3) = 0].
  - chi(7) ≠ 2 via (9,4,7) [chi(9) = chi(4) = 2].
  - chi(7) = 1.
  - chi(5) ≠ 0 via (12,1,5) [chi(12) = chi(1) = 0].
  - chi(5) ≠ 1 via (6,5,7) [chi(6) = chi(7) = 1].
  - chi(5) = 2.
  - chi(8) ≠ 0 via self-loop (12,8,12) [chi(12) = 0].
  - chi(8) ≠ 2 via (9,5,8) [chi(9) = chi(5) = 2].
  - chi(8) = 1.
  - (6,6,8) mono: chi(6) = chi(8) = 1.
-/
theorem pillar_3_substep_chi_4_2_chi_6_1_chi_9_2_chi_12_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 2 ∧ χ 12 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hValid 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  -- chi(7) = 1.
  have h_7_ne_0 : χ 7 ≠ 0 := by
    intro h
    apply mono 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ3]
    · rw [hχ3, h]
  have h_7_ne_2 : χ 7 ≠ 2 := by
    intro h
    apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, hχ4]
    · rw [hχ4, h]
  have h_7 : χ 7 = 1 := by omega
  -- chi(5) = 2.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 12 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ1]
    · rw [hχ1, h]
  have h_5_ne_1 : χ 5 ≠ 1 := by
    intro h
    apply mono 6 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, h_7]
  have h_5 : χ 5 = 2 := by omega
  -- chi(8) = 1.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, h_5]
    · rw [h_5, h]
  have h_8 : χ 8 = 1 := by omega
  -- (6, 6, 8) mono.
  apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rfl
  · rw [hχ6, h_8]

/-! ### §33.35. Round 160 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=2, chi(12)=1 via chi(18) split. -/

/--
  **Round 160 — Pillar 3 sub-step: chi(4)=2, chi(6)=1, chi(9)=2, chi(12)=1.**

  Self-loop (18,12,18) gives chi(18) != 1. Case split on chi(18) ∈ {0, 2}.

  - chi(18) = 0 branch: chi(7) = 1 forced via (18,1,7) and (9,4,7). Long 15-step
    chain to chi(15), chi(8), chi(5), chi(10), chi(11), chi(14), chi(13), chi(16),
    chi(21), chi(20), chi(17), chi(19) all forced. Mono via (9, 16, 19).

  - chi(18) = 2 branch: chi(10) = 0 forced via (18,4,10) and (6,10,12).
    chi(7) ∈ {0, 1}.
    - chi(7) = 1 sub-case: chi(15) impossible (≠ 2 via (15,4,9); ≠ 1 via (15,7,12);
      ≠ 0 via self-loop (15,10,15)).
    - chi(7) = 0 sub-case: chi(15) = 1 forced. Long chain → mono via (12, 17, 21).
-/
theorem pillar_3_substep_chi_4_2_chi_6_1_chi_9_2_chi_12_1 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 2 ∧ χ 12 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- chi(18) != 1 via self-loop (18, 12, 18).
  have h_18_ne_1 : χ 18 ≠ 1 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  rcases (show χ 18 = 0 ∨ χ 18 = 2 from by omega) with h_18 | h_18
  · -- Case chi(18) = 0.
    -- chi(7) = 1 forced.
    have hv7 : χ 7 < 3 := hValid 7 (by norm_num) (by omega)
    have h_7_ne_0 : χ 7 ≠ 0 := by
      intro h
      apply mono 18 1 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, hχ1]
      · rw [hχ1, h]
    have h_7_ne_2 : χ 7 ≠ 2 := by
      intro h
      apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, hχ4]
      · rw [hχ4, h]
    have h_7 : χ 7 = 1 := by omega
    -- chi(15) = 0.
    have hv15 : χ 15 < 3 := hValid 15 (by norm_num) (by omega)
    have h_15_ne_1 : χ 15 ≠ 1 := by
      intro h
      apply mono 15 7 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, h_7]
      · rw [h_7, hχ12]
    have h_15_ne_2 : χ 15 ≠ 2 := by
      intro h
      apply mono 15 4 9 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ4]
      · rw [hχ4, hχ9]
    have h_15 : χ 15 = 0 := by omega
    -- chi(8) = 2.
    have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
    have h_8_ne_0 : χ 8 ≠ 0 := by
      intro h
      apply mono 15 3 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, hχ3]
      · rw [hχ3, h]
    have h_8_ne_1 : χ 8 ≠ 1 := by
      intro h
      apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h]
      · rw [h, hχ12]
    have h_8 : χ 8 = 2 := by omega
    -- chi(5) = 0.
    have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
    have h_5_ne_1 : χ 5 ≠ 1 := by
      intro h
      apply mono 6 5 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, h]
      · rw [h, h_7]
    have h_5_ne_2 : χ 5 ≠ 2 := by
      intro h
      apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h]
      · rw [h, h_8]
    have h_5 : χ 5 = 0 := by omega
    -- chi(10) = 2.
    have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
    have h_10_ne_0 : χ 10 ≠ 0 := by
      intro h
      apply mono 15 5 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h_5]
      · rw [h_5, h]
    have h_10_ne_1 : χ 10 ≠ 1 := by
      intro h
      apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, h]
      · rw [h, hχ12]
    have h_10 : χ 10 = 2 := by omega
    -- chi(11) = 2.
    have hv11 : χ 11 < 3 := hValid 11 (by norm_num) (by omega)
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 18 5 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_5]
      · rw [h_5, h]
    have h_11_ne_1 : χ 11 ≠ 1 := by
      intro h
      apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h_7]
      · rw [h_7, h]
    have h_11 : χ 11 = 2 := by omega
    -- chi(14) = 0.
    have hv14 : χ 14 < 3 := hValid 14 (by norm_num) (by omega)
    have h_14_ne_1 : χ 14 ≠ 1 := by
      intro h
      apply mono 6 12 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, hχ12]
      · rw [hχ12, h]
    have h_14_ne_2 : χ 14 ≠ 2 := by
      intro h
      apply mono 9 11 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_11]
      · rw [h_11, h]
    have h_14 : χ 14 = 0 := by omega
    -- chi(13) = 1.
    have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
    have h_13_ne_0 : χ 13 ≠ 0 := by
      intro h
      apply mono 3 13 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h]
      · rw [h, h_14]
    have h_13_ne_2 : χ 13 ≠ 2 := by
      intro h
      apply mono 9 10 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_10]
      · rw [h_10, h]
    have h_13 : χ 13 = 1 := by omega
    -- chi(16) = 2.
    have hv16 : χ 16 < 3 := hValid 16 (by norm_num) (by omega)
    have h_16_ne_0 : χ 16 ≠ 0 := by
      intro h
      apply mono 3 15 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_15]
      · rw [h_15, h]
    have h_16_ne_1 : χ 16 ≠ 1 := by
      intro h
      apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [hχ12, h]
    have h_16 : χ 16 = 2 := by omega
    -- chi(21) = 1.
    have hv21 : χ 21 < 3 := hValid 21 (by norm_num) (by omega)
    have h_21_ne_0 : χ 21 ≠ 0 := by
      intro h
      apply mono 18 15 21 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_15]
      · rw [h_15, h]
    have h_21_ne_2 : χ 21 ≠ 2 := by
      intro h
      apply mono 21 4 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ4]
      · rw [hχ4, h_11]
    have h_21 : χ 21 = 1 := by omega
    -- chi(20) = 2.
    have hv20 : χ 20 < 3 := hValid 20 (by norm_num) (by omega)
    have h_20_ne_0 : χ 20 ≠ 0 := by
      intro h
      apply mono 15 15 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_15, h]
    have h_20_ne_1 : χ 20 ≠ 1 := by
      intro h
      apply mono 21 13 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_21, h_13]
      · rw [h_13, h]
    have h_20 : χ 20 = 2 := by omega
    -- chi(17) = 0.
    have hv17 : χ 17 < 3 := hValid 17 (by norm_num) (by omega)
    have h_17_ne_1 : χ 17 ≠ 1 := by
      intro h
      apply mono 12 13 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h_13]
      · rw [h_13, h]
    have h_17_ne_2 : χ 17 ≠ 2 := by
      intro h
      apply mono 9 17 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h]
      · rw [h, h_20]
    have h_17 : χ 17 = 0 := by omega
    -- chi(19) = 2.
    have hv19 : χ 19 < 3 := hValid 19 (by norm_num) (by omega)
    have h_19_ne_0 : χ 19 ≠ 0 := by
      intro h
      apply mono 15 14 19 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h_14]
      · rw [h_14, h]
    have h_19_ne_1 : χ 19 ≠ 1 := by
      intro h
      apply mono 21 12 19 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_21, hχ12]
      · rw [hχ12, h]
    have h_19 : χ 19 = 2 := by omega
    -- Final mono (9, 16, 19): chi(9) = chi(16) = chi(19) = 2.
    apply mono 9 16 19 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, h_16]
    · rw [h_16, h_19]
  · -- Case chi(18) = 2.
    -- chi(10) = 0 forced.
    have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
    have h_10_ne_1 : χ 10 ≠ 1 := by
      intro h
      apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, h]
      · rw [h, hχ12]
    have h_10_ne_2 : χ 10 ≠ 2 := by
      intro h
      apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, hχ4]
      · rw [hχ4, h]
    have h_10 : χ 10 = 0 := by omega
    -- chi(7) ∈ {0, 1} (chi(7) != 2 from (9, 4, 7)).
    have hv7 : χ 7 < 3 := hValid 7 (by norm_num) (by omega)
    have h_7_ne_2 : χ 7 ≠ 2 := by
      intro h
      apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, hχ4]
      · rw [hχ4, h]
    -- chi(7) = 1 forces chi(15) impossible: chi(15) != 2 via (15,4,9);
    -- chi(15) != 1 via (15,7,12); chi(15) != 0 via self-loop (15,10,15).
    have h_7_ne_1 : χ 7 ≠ 1 := by
      intro h
      have hv15 : χ 15 < 3 := hValid 15 (by norm_num) (by omega)
      have h_15_ne_2 : χ 15 ≠ 2 := by
        intro h15
        apply mono 15 4 9 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h15, hχ4]
        · rw [hχ4, hχ9]
      have h_15_ne_1 : χ 15 ≠ 1 := by
        intro h15
        apply mono 15 7 12 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h15, h]
        · rw [h, hχ12]
      have h_15_ne_0 : χ 15 ≠ 0 := by
        intro h15
        apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h15, h_10]
        · rw [h_10, h15]
      omega
    have h_7 : χ 7 = 0 := by omega
    -- chi(8) = 2: chi(8) != 0 via (3,7,8); chi(8) != 1 self-loop.
    have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
    have h_8_ne_0 : χ 8 ≠ 0 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_7]
      · rw [h_7, h]
    have h_8_ne_1 : χ 8 ≠ 1 := by
      intro h
      apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h]
      · rw [h, hχ12]
    have h_8 : χ 8 = 2 := by omega
    -- chi(15) = 1: chi(15) != 0 via self-loop (15,10,15) since chi(10)=0;
    -- chi(15) != 2 via (15,4,9).
    have hv15 : χ 15 < 3 := hValid 15 (by norm_num) (by omega)
    have h_15_ne_0 : χ 15 ≠ 0 := by
      intro h
      apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, h_10]
      · rw [h_10, h]
    have h_15_ne_2 : χ 15 ≠ 2 := by
      intro h
      apply mono 15 4 9 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ4]
      · rw [hχ4, hχ9]
    have h_15 : χ 15 = 1 := by omega
    -- chi(11) = 2: chi(11) != 0 via (3,10,11); chi(11) != 1 via (12,11,15).
    have hv11 : χ 11 < 3 := hValid 11 (by norm_num) (by omega)
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 3 10 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_10]
      · rw [h_10, h]
    have h_11_ne_1 : χ 11 ≠ 1 := by
      intro h
      apply mono 12 11 15 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ12, h]
      · rw [h, h_15]
    have h_11 : χ 11 = 2 := by omega
    -- chi(14) = 0: chi(14) != 1 via (6,12,14); chi(14) != 2 via (9,11,14).
    have hv14 : χ 14 < 3 := hValid 14 (by norm_num) (by omega)
    have h_14_ne_1 : χ 14 ≠ 1 := by
      intro h
      apply mono 6 12 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, hχ12]
      · rw [hχ12, h]
    have h_14_ne_2 : χ 14 ≠ 2 := by
      intro h
      apply mono 9 11 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_11]
      · rw [h_11, h]
    have h_14 : χ 14 = 0 := by omega
    -- chi(13) = 2: chi(13) != 0 via (3,13,14); chi(13) != 1 via (6,13,15).
    have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
    have h_13_ne_0 : χ 13 ≠ 0 := by
      intro h
      apply mono 3 13 14 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h]
      · rw [h, h_14]
    have h_13_ne_1 : χ 13 ≠ 1 := by
      intro h
      apply mono 6 13 15 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ6, h]
      · rw [h, h_15]
    have h_13 : χ 13 = 2 := by omega
    -- chi(16) = 0: chi(16) != 1 self-loop; chi(16) != 2 via (9,13,16); also
    -- chi(16) != 2 via (24,8,16) — but no chi(24) yet. Self-loop (24,16,24).
    have hv16 : χ 16 < 3 := hValid 16 (by norm_num) (by omega)
    have h_16_ne_1 : χ 16 ≠ 1 := by
      intro h
      apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [hχ12, h]
    have h_16_ne_2 : χ 16 ≠ 2 := by
      intro h
      apply mono 9 13 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ9, h_13]
      · rw [h_13, h]
    have h_16 : χ 16 = 0 := by omega
    -- chi(17) = 1: chi(17) != 0 via (3,16,17); chi(17) != 2 via (18,11,17).
    have hv17 : χ 17 < 3 := hValid 17 (by norm_num) (by omega)
    have h_17_ne_0 : χ 17 ≠ 0 := by
      intro h
      apply mono 3 16 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [hχ3, h_16]
      · rw [h_16, h]
    have h_17_ne_2 : χ 17 ≠ 2 := by
      intro h
      apply mono 18 11 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_11]
      · rw [h_11, h]
    have h_17 : χ 17 = 1 := by omega
    -- chi(21) = 1: chi(21) != 0 via (21,3,10); chi(21) != 2 via (21,4,11).
    have hv21 : χ 21 < 3 := hValid 21 (by norm_num) (by omega)
    have h_21_ne_0 : χ 21 ≠ 0 := by
      intro h
      apply mono 21 3 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ3]
      · rw [hχ3, h_10]
    have h_21_ne_2 : χ 21 ≠ 2 := by
      intro h
      apply mono 21 4 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ4]
      · rw [hχ4, h_11]
    have h_21 : χ 21 = 1 := by omega
    -- Final mono (12, 17, 21): chi(12) = chi(17) = chi(21) = 1.
    apply mono 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h_17]
    · rw [h_17, h_21]

/-! ### §33.36. Round 161 — Pillar 3: chi(4)=2, chi(6)=1, chi(9)=2 closure via chi(12) split. -/

/--
  **Round 161 — Pillar 3 sub-step (chi(9)=2 closure under chi(4)=2, chi(6)=1).**

  Self-loop (9,9,12) gives chi(12) != 2 (since chi(9)=2). Dispatches to
  Round 159 (chi(12)=0) or Round 160 (chi(12)=1).
-/
theorem pillar_3_chi_4_2_chi_6_1_chi_9_2_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 ∧
      χ 9 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv12 : χ 12 < 3 := hValid 12 (by norm_num) (by omega)
  have h_12_ne_2 : χ 12 ≠ 2 := by
    intro h
    apply mono 9 9 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ9, h]
  rcases (show χ 12 = 0 ∨ χ 12 = 1 from by omega) with h_12 | h_12
  · exact pillar_3_substep_chi_4_2_chi_6_1_chi_9_2_chi_12_0
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, h_12⟩
  · exact pillar_3_substep_chi_4_2_chi_6_1_chi_9_2_chi_12_1
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, h_12⟩

/-! ### §33.37. Round 162 — Pillar 3: chi(4)=2, chi(6)=1 closure via chi(9) split. -/

/--
  **Round 162 — Pillar 3 sub-step (chi(4)=2, chi(6)=1 closure).**

  Self-loop (9,6,9) gives chi(9) != 1 (since chi(6)=1). Dispatches to
  Round 158 (chi(9)=0) or Round 161 (chi(9)=2).
-/
theorem pillar_3_chi_4_2_chi_6_1_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 ∧ χ 6 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv9 : χ 9 < 3 := hValid 9 (by norm_num) (by omega)
  have h_9_ne_1 : χ 9 ≠ 1 := by
    intro h
    apply mono 9 6 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ6]
    · rw [hχ6, h]
  rcases (show χ 9 = 0 ∨ χ 9 = 2 from by omega) with h_9 | h_9
  · exact pillar_3_chi_4_2_chi_6_1_chi_9_0_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, h_9⟩
  · exact pillar_3_chi_4_2_chi_6_1_chi_9_2_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, h_9⟩

/-! ### §33.38. Round 163 — Pillar 3: chi(2)=1, chi(3)=0 closure via chi(4) split. -/

/--
  **Round 163 — Pillar 3 sub-step (chi(2)=1, chi(3)=0 closure).**

  Self-loop (3,3,4) gives chi(4) != 0 (since chi(3)=0). Case split chi(4) ∈ {1, 2}.

  - chi(4) = 1: chi(6)=2 forced (self-loop chi(4)!=chi(6) + (6,1,3) chi(6)!=0).
    Invoke Round 155.
  - chi(4) = 2: chi(6)=1 forced (similar). Invoke Round 162.
-/
theorem pillar_3_chi_2_1_chi_3_0_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 0 ∧ χ 2 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv4 : χ 4 < 3 := hValid 4 (by norm_num) (by omega)
  have hv6 : χ 6 < 3 := hValid 6 (by norm_num) (by omega)
  -- chi(4) != 0 via self-loop (3, 3, 4).
  have h_4_ne_0 : χ 4 ≠ 0 := by
    intro h
    apply mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ3, h]
  rcases (show χ 4 = 1 ∨ χ 4 = 2 from by omega) with h_4 | h_4
  · -- chi(4) = 1: force chi(6) = 2.
    have h_6_ne_0 : χ 6 ≠ 0 := by
      intro h
      apply mono 6 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ1]
      · rw [hχ1, hχ3]
    have h_6_ne_1 : χ 6 ≠ 1 := by
      intro h
      apply mono 6 4 6 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, h_4]
      · rw [h_4, h]
    have h_6 : χ 6 = 2 := by omega
    exact pillar_3_chi_2_1_chi_6_2_chi_4_1_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, h_6, h_4⟩
  · -- chi(4) = 2: force chi(6) = 1.
    have h_6_ne_0 : χ 6 ≠ 0 := by
      intro h
      apply mono 6 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, hχ1]
      · rw [hχ1, hχ3]
    have h_6_ne_2 : χ 6 ≠ 2 := by
      intro h
      apply mono 6 4 6 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h, h_4]
      · rw [h_4, h]
    have h_6 : χ 6 = 1 := by omega
    exact pillar_3_chi_4_2_chi_6_1_closes
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, h_4, h_6⟩

/-! ### §33.39. Round 164 — Pillar 3 sub-step: chi(3)=2, chi(4)=0, chi(6)=1, chi(12)=0 → mono (6,6,8). -/

/--
  **Round 164 — Pillar 3 sub-step: chi(2)=1, chi(3)=2, chi(4)=0, chi(6)=1, chi(9)=2, chi(12)=0.**

  Forces chi(8) = 1 via (3,8,9) ≠ 2 and self-loop (12,8,12) ≠ 0.
  Mono via (6, 6, 8) with chi(6) = chi(8) = 1.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_1_chi_12_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 1 ∧
      χ 9 = 2 ∧ χ 12 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  -- chi(8) ≠ 2 via (3, 8, 9): chi(3) = chi(8) = chi(9) = 2 mono.
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, h]
    · rw [h, hχ9]
  -- chi(8) ≠ 0 via self-loop (12, 8, 12): chi(12) = 0 = chi(8) mono.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 1 := by omega
  -- (6, 6, 8) mono.
  apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rfl
  · rw [hχ6, h_8]

/-! ### §33.40. Round 165 — Pillar 3 sub-step: chi(3)=2, chi(4)=0, chi(6)=1, chi(12)=1 → mono (18,4,10). -/

/--
  **Round 165 — Pillar 3 sub-step: chi(2)=1, chi(3)=2, chi(4)=0, chi(6)=1, chi(9)=2, chi(12)=1.**

  Chain forces chi(18) = 0, chi(10) = 0, then mono via (18, 4, 10):
  chi(18) = chi(4) = chi(10) = 0.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_1_chi_12_1 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 1 ∧
      χ 9 = 2 ∧ χ 12 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- chi(18) = 0: ≠ 1 self-loop; ≠ 2 from (18, 3, 9).
  have h_18_ne_1 : χ 18 ≠ 1 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 3 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ3]
    · rw [hχ3, hχ9]
  have h_18 : χ 18 = 0 := by omega
  -- chi(10) = 0: ≠ 1 via (6, 10, 12); ≠ 2 via (3, 9, 10).
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, hχ12]
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ9]
    · rw [hχ9, h]
  have h_10 : χ 10 = 0 := by omega
  -- (18, 4, 10) mono: chi(18) = chi(4) = chi(10) = 0.
  apply mono 18 4 10 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [h_18, hχ4]
  · rw [hχ4, h_10]

/-! ### §33.41. Round 166 — Pillar 3 combination: chi(3)=2, chi(4)=0, chi(6)=1 closure. -/

/--
  **Round 166 — Pillar 3 sub-step (chi(3)=2, chi(4)=0, chi(6)=1 closure).**

  Forces chi(9) = 2: chi(9) ≠ 0 via (9,1,4); chi(9) ≠ 1 self-loop (9,6,9).
  Self-loop (9,9,12) gives chi(12) ≠ 2. Case split chi(12) ∈ {0, 1}:
  - chi(12) = 0: invoke Round 164.
  - chi(12) = 1: invoke Round 165.
-/
theorem pillar_3_chi_2_1_chi_3_2_chi_4_0_chi_6_1_closes :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv9 : χ 9 < 3 := hValid 9 (by norm_num) (by omega)
  have hv12 : χ 12 < 3 := hValid 12 (by norm_num) (by omega)
  -- chi(9) = 2.
  have h_9_ne_0 : χ 9 ≠ 0 := by
    intro h
    apply mono 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ1]
    · rw [hχ1, hχ4]
  have h_9_ne_1 : χ 9 ≠ 1 := by
    intro h
    apply mono 9 6 9 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ6]
    · rw [hχ6, h]
  have h_9 : χ 9 = 2 := by omega
  -- chi(12) ≠ 2 via self-loop (9, 9, 12).
  have h_12_ne_2 : χ 12 ≠ 2 := by
    intro h
    apply mono 9 9 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_9, h]
  rcases (show χ 12 = 0 ∨ χ 12 = 1 from by omega) with h_12 | h_12
  · exact pillar_3_substep_C_chi_4_0_chi_6_1_chi_12_0
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, h_9, h_12⟩
  · exact pillar_3_substep_C_chi_4_0_chi_6_1_chi_12_1
      ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, h_9, h_12⟩

/-! ### §33.42. Round 167 — Pillar 3 sub-step: chi(3)=2, chi(4)=0, chi(6)=2 closure via chi(12) split. -/

/--
  **Round 167 — Pillar 3 sub-step (chi(3)=2, chi(4)=0, chi(6)=2 closure).**

  Forces chi(9) = 1 (chi(9) ≠ 0 via (9,1,4); chi(9) ≠ 2 self-loop chi(6)=2).
  Self-loop (9,9,12) gives chi(12) ≠ 1. Case split chi(12) ∈ {0, 2}.

  - chi(12) = 0: chi(5) impossible — chi(5) ≠ 0 via (12,1,5); chi(5) ≠ 1
    via (9,2,5); chi(5) ≠ 2 via (6,3,5). Contradiction.

  - chi(12) = 2: chi(7) = 2 forced mono via (3,6,7) directly. So chi(7) ≠ 2
    from this. chi(7) ∈ {0, 1}. Both sub-cases require long chains;
    closure via (24, 13, 21) or similar.

    Actually directly: (3, 6, 7): chi(3) = chi(6) = chi(7). chi(3) = 2,
    chi(6) = 2. If chi(7) = 2, all three equal, MONO. So chi(7) ≠ 2.

    chi(5) = 0 forced (≠ 1 via (9,2,5); ≠ 2 via (6,3,5)).
    chi(18) ≠ 2 self-loop. chi(18) ≠ 0 via (18,3,9) chi(18) = 2 — wait chi(3)=chi(9)? chi(3)=2, chi(9)=1. (18,3,9): chi(18)=chi(3)=chi(9) requires all=2 or all=1. chi(3)=2, chi(9)=1 differ. No mono.

  Status: complex chi(12)=2 sub-case; deferred to future round. Currently
  only chi(12)=0 sub-case closed via chi(5) contradiction.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_2_chi_12_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 2 ∧
      χ 9 = 1 ∧ χ 12 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  -- chi(5) ≠ 0 via (12, 1, 5).
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 12 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, hχ1]
    · rw [hχ1, h]
  -- chi(5) ≠ 1 via (9, 2, 5).
  have h_5_ne_1 : χ 5 ≠ 1 := by
    intro h
    apply mono 9 2 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, hχ2]
    · rw [hχ2, h]
  -- chi(5) ≠ 2 via (6, 3, 5).
  have h_5_ne_2 : χ 5 ≠ 2 := by
    intro h
    apply mono 6 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, hχ3]
    · rw [hχ3, h]
  -- Contradiction: chi(5) has no value.
  omega

/-! ### §33.43. Round 168 — Pillar 3 sub-step: C1.0.2 chi(12)=2, chi(7)=0, chi(24)=0 → mono (24,5,13). -/

/--
  **Round 168 — Pillar 3 sub-step: chi(2)=1, chi(3)=2, chi(4)=0, chi(6)=2, chi(9)=1, chi(12)=2, chi(7)=0, chi(24)=0.**

  Forces chi(5)=0 (≠1 from (9,2,5); ≠2 from (6,3,5)).
  Forces chi(18)=1 (≠0 from (18,1,7) with chi(7)=0; ≠2 self-loop).
  Forces chi(8)=0 (≠1 from (18,2,8); ≠2 self-loop).
  Forces chi(16)=1 (≠0 self-loop (24,16,24) with chi(24)=0; ≠2 self-loop (12,12,16)).
  Forces chi(13)=0 (≠1 from (9,13,16); ≠2 from (3,12,13)).
  Mono via (24, 5, 13): chi(24)=chi(5)=chi(13)=0.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_2_chi_12_2_chi_7_0_chi_24_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 2 ∧
      χ 9 = 1 ∧ χ 12 = 2 ∧ χ 7 = 0 ∧ χ 24 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12, hχ7, hχ24⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv5 : χ 5 < 3 := hValid 5 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hValid 16 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- chi(5) = 0.
  have h_5_ne_1 : χ 5 ≠ 1 := by
    intro h
    apply mono 9 2 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, hχ2]
    · rw [hχ2, h]
  have h_5_ne_2 : χ 5 ≠ 2 := by
    intro h
    apply mono 6 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, hχ3]
    · rw [hχ3, h]
  have h_5 : χ 5 = 0 := by omega
  -- chi(18) = 1.
  have h_18_ne_0 : χ 18 ≠ 0 := by
    intro h
    apply mono 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ1]
    · rw [hχ1, hχ7]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 1 := by omega
  -- chi(8) = 0.
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, hχ2]
    · rw [hχ2, h]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 0 := by omega
  -- chi(16) = 1.
  have h_16_ne_0 : χ 16 ≠ 0 := by
    intro h
    apply mono 24 16 24 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ24, h]
    · rw [h, hχ24]
  have h_16_ne_2 : χ 16 ≠ 2 := by
    intro h
    apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [hχ12, h]
  have h_16 : χ 16 = 1 := by omega
  -- chi(13) = 0.
  have h_13_ne_1 : χ 13 ≠ 1 := by
    intro h
    apply mono 9 13 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, h]
    · rw [h, h_16]
  have h_13_ne_2 : χ 13 ≠ 2 := by
    intro h
    apply mono 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ12]
    · rw [hχ12, h]
  have h_13 : χ 13 = 0 := by omega
  -- (24, 5, 13) mono: chi(24)=chi(5)=chi(13)=0.
  apply mono 24 5 13 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [hχ24, h_5]
  · rw [h_5, h_13]

/-! ### §33.44. Round 169 — Pillar 3 sub-step: C1.0.2 chi(12)=2, chi(7)=0, chi(24)=2, chi(15)=0 → mono (15,8,13). -/

/--
  **Round 169 — Pillar 3 sub-step: chi(12)=2, chi(7)=0, chi(24)=2, chi(15)=0.**

  Forces chi(8)=0 (≠1 from (18,2,8); ≠2 self-loop).
  Forces chi(10)=1 (≠0 self-loop (15,10,15); ≠2 from (6,10,12)).
  Forces chi(13)=0 (≠1 from (9,10,13); ≠2 from (3,12,13)).
  Mono via (15, 8, 13): chi(15)=chi(8)=chi(13)=0.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_2_chi_12_2_chi_7_0_chi_24_2_chi_15_0 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 2 ∧
      χ 9 = 1 ∧ χ 12 = 2 ∧ χ 7 = 0 ∧ χ 24 = 2 ∧ χ 15 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12, hχ7, hχ24, hχ15⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv8 : χ 8 < 3 := hValid 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hValid 10 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hValid 13 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hValid 18 (by norm_num) (by omega)
  -- chi(18) = 1: forced from chi(7)=0 (same as R168).
  have h_18_ne_0 : χ 18 ≠ 0 := by
    intro h
    apply mono 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ1]
    · rw [hχ1, hχ7]
  have h_18_ne_2 : χ 18 ≠ 2 := by
    intro h
    apply mono 18 12 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h, hχ12]
    · rw [hχ12, h]
  have h_18 : χ 18 = 1 := by omega
  -- chi(8) = 0.
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, hχ2]
    · rw [hχ2, h]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ12, h]
    · rw [h, hχ12]
  have h_8 : χ 8 = 0 := by omega
  -- chi(10) = 1.
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ15, h]
    · rw [h, hχ15]
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ6, h]
    · rw [h, hχ12]
  have h_10 : χ 10 = 1 := by omega
  -- chi(13) = 0.
  have h_13_ne_1 : χ 13 ≠ 1 := by
    intro h
    apply mono 9 10 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ9, h_10]
    · rw [h_10, h]
  have h_13_ne_2 : χ 13 ≠ 2 := by
    intro h
    apply mono 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [hχ3, hχ12]
    · rw [hχ12, h]
  have h_13 : χ 13 = 0 := by omega
  -- (15, 8, 13) mono: chi(15)=chi(8)=chi(13)=0.
  apply mono 15 8 13 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [hχ15, h_8]
  · rw [h_8, h_13]

/-! ### §33.45. Round 170 — Pillar 3 sub-step: C1.0.2 chi(12)=2, chi(15)=1 → mono (18,9,15). -/

/--
  **Round 170 — Pillar 3 sub-step: chi(12)=2, chi(15)=1.**

  IMPORTANT: Does NOT require chi(7) or chi(24) hypotheses!
  Mono via (18, 9, 15): we need chi(18) = chi(9) = chi(15) = 1.
  - chi(9) = 1 (hypothesis).
  - chi(15) = 1 (case).
  - chi(18) = 1 forced via:
    - chi(18) ≠ 2 self-loop (18, 12, 18) with chi(12)=2.
    - chi(18) ≠ 0 via (3, 17, 18) — wait that needs chi(17). Actually need different derivation.

  Alternative: (18, 9, 15) directly mono if chi(18) = 1. To force chi(18) = 1:
    - Self-loop (18, 12, 18): chi(18) ≠ 2.
    - (18, 6, 12): 1 = 2 = 2. chi(18) = 2 ⇒ mono. chi(18) ≠ 2 ✓.
    - chi(18) ∈ {0, 1}.
    - Hmm chi(18) = 0 is consistent. Doesn't force chi(18) = 1.

  Actually mono (18, 9, 15) doesn't directly fire here without forcing chi(18) = 1.

  Status: REVISED — this sub-step requires chi(18) sub-case. Use chi(18) = 1
  forced from (3, 18, 19) chi(18) impossibility OR similar.

  For NOW: include chi(18) = 1 as hypothesis.
-/
theorem pillar_3_substep_C_chi_4_0_chi_6_2_chi_12_2_chi_15_1_chi_18_1 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      χ 1 = 0 ∧ χ 3 = 2 ∧ χ 2 = 1 ∧ χ 4 = 0 ∧ χ 6 = 2 ∧
      χ 9 = 1 ∧ χ 12 = 2 ∧ χ 15 = 1 ∧ χ 18 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hχ1, hχ3, hχ2, hχ4, hχ6, hχ9, hχ12, hχ15, hχ18⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- (18, 9, 15) mono directly: chi(18) = chi(9) = chi(15) = 1.
  apply mono 18 9 15 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [hχ18, hχ9]
  · rw [hχ9, hχ15]

end RadoNumbers
