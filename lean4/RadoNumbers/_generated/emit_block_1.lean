set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #1** (4+3+2): c₀ = {3, 6, 12, 15}, c₁ = {21, 24, 27}, c₂ = {9, 18}. Mono (9, 13, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor01_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0)
    (h21 : χ 21 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h21 ▸ hValid 21 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h5_ne_c0 : χ 5 ≠ c0 := fun h =>
    mono_3 3 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h6.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h6.symm) (h6.trans h.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 3 11 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h12.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h12.symm) (h12.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 21 17 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h24.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 21 20 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h27.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 24 13 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h21.symm)
  have h13 : χ 13 = c2 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact absurd hh h13_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 24 16 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h24.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 24 19 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h27.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 9 10 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h13.symm)
  have h10 : χ 10 = c1 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact hh
    · exact absurd hh h10_ne_c2
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h11 : χ 11 = c1 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact hh
    · exact absurd hh h11_ne_c2
  exact mono_3 9 13 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h9.trans h13.symm) (h13.trans h16.symm)

