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

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #2** (4+3+2): c₀ = {3, 6, 12, 24}, c₁ = {9, 15, 27}, c₂ = {18, 21}. Mono (18, 4, 10) at c2. -/
theorem compression_3_3_4_3_2_survivor02_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h18 : χ 18 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h18 ▸ hValid 18 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h9.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 15 9 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h9.symm) (h9.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 15 22 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h27.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  exact mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h4.symm) (h4.trans h10.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #3** (4+3+2): c₀ = {3, 6, 12, 24}, c₁ = {15, 21, 27}, c₂ = {9, 18}. Mono (18, 10, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor03_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0)
    (h15 : χ 15 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h15 ▸ hValid 15 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 15 16 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h21.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 15 22 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h27.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h10.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  exact mono_3 18 10 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h10.symm) (h10.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #4** (4+3+2): c₀ = {3, 6, 12, 24}, c₁ = {9, 21, 27}, c₂ = {15, 18}. Mono (21, 13, 20) at c1. -/
theorem compression_3_3_4_3_2_survivor04_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h15 : χ 15 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h15 ▸ hValid 15 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c1 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact hh
    · exact absurd hh h10_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 15 13 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h18.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 15 18 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h18.symm) (h18.trans h.symm)
  have h23 : χ 23 = c1 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact hh
    · exact absurd hh h23_ne_c2
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 21 2 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h9.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 21 9 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h9.symm) (h9.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 21 10 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h10.symm) (h10.trans h.symm)
  exact mono_3 21 13 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h13.symm) (h13.trans h20.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #5** (4+3+2): c₀ = {3, 6, 15, 18}, c₁ = {9, 21, 27}, c₂ = {12, 24}. Mono (21, 9, 16) at c1. -/
theorem compression_3_3_4_3_2_survivor05_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h15 : χ 15 = c0) (h18 : χ 18 = c0)
    (h9 : χ 9 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h12 : χ 12 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 15 6 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h6.symm) (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 15 18 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 21 1 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h8.symm)
  have h1 : χ 1 = c2 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact absurd hh h1_ne_c1
    · exact hh
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 21 2 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h9.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  exact mono_3 21 9 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h9.symm) (h9.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #6** (4+3+2): c₀ = {3, 6, 15, 18}, c₁ = {12, 24, 27}, c₂ = {9, 21}. Mono (21, 9, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor06_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h15 : χ 15 = c0) (h18 : χ 18 = c0)
    (h12 : χ 12 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 15 6 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h6.symm) (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 15 18 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h18.symm) (h18.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 21 1 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h8.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 21 2 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h9.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  exact mono_3 21 9 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h9.symm) (h9.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #7** (4+3+2): c₀ = {3, 6, 15, 18}, c₁ = {12, 21, 24}, c₂ = {9, 27}. Mono (27, 4, 13) at c2. -/
theorem compression_3_3_4_3_2_survivor07_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h15 : χ 15 = c0) (h18 : χ 18 = c0)
    (h12 : χ 12 = c1) (h21 : χ 21 = c1) (h24 : χ 24 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 15 6 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h6.symm) (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 15 18 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h18.symm) (h18.trans h.symm)
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 21 5 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h12.symm)
  have h5 : χ 5 = c2 := by
    rcases chi_in_3colors 5 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h5_ne_c0
    · exact absurd hh h5_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 21 12 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h12.symm) (h12.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 24 4 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h12.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
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
  exact mono_3 27 4 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h27.trans h4.symm) (h4.trans h13.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #8** (4+3+2): c₀ = {3, 6, 15, 21}, c₁ = {12, 24, 27}, c₂ = {9, 18}. Mono (24, 2, 10) at c1. -/
theorem compression_3_3_4_3_2_survivor08_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0)
    (h12 : χ 12 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 15 6 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h6.symm) (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 18 10 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h16.symm)
  have h10 : χ 10 = c1 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact hh
    · exact absurd hh h10_ne_c2
  have h22_ne_c2 : χ 22 ≠ c2 := fun h =>
    mono_3 18 16 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h16.symm) (h16.trans h.symm)
  have h22 : χ 22 = c1 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact hh
    · exact absurd hh h22_ne_c2
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 18 17 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h23.symm)
  have h17 : χ 17 = c1 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact hh
    · exact absurd hh h17_ne_c2
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h20.symm) (h20.trans h.symm)
  have h26 : χ 26 = c1 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact hh
    · exact absurd hh h26_ne_c2
  exact mono_3 24 2 10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h24.trans h2.symm) (h2.trans h10.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #9** (4+3+2): c₀ = {3, 6, 18, 21}, c₁ = {9, 15, 24}, c₂ = {12, 27}. Mono (24, 8, 16) at c1. -/
theorem compression_3_3_4_3_2_survivor09_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h18 : χ 18 = c0) (h21 : χ 21 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h24 : χ 24 = c1)
    (h12 : χ 12 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c1 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact hh
    · exact absurd hh h23_ne_c2
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h9.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 15 9 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h9.symm) (h9.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 15 11 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h16.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 15 19 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h24.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 21 3 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h3.symm) (h3.trans h.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h6.symm) (h6.trans h.symm)
  have h13 : χ 13 = c2 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact absurd hh h13_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 21 11 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h18.symm)
  have h11 : χ 11 = c2 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact absurd hh h11_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 21 18 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 24 1 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h9.symm)
  have h1 : χ 1 = c2 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact absurd hh h1_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 24 7 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h15.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  exact mono_3 24 8 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h24.trans h8.symm) (h8.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #10** (4+3+2): c₀ = {3, 6, 18, 21}, c₁ = {9, 15, 27}, c₂ = {12, 24}. Mono (15, 15, 20) at c1. -/
theorem compression_3_3_4_3_2_survivor10_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h18 : χ 18 = c0) (h21 : χ 21 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h12 : χ 12 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h9.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 15 9 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h9.symm) (h9.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 15 11 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h16.symm)
  exact mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl (h15.trans h20.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #11** (4+3+2): c₀ = {3, 6, 18, 21}, c₁ = {12, 24, 27}, c₂ = {9, 15}. Mono (15, 15, 20) at c2. -/
theorem compression_3_3_4_3_2_survivor11_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h18 : χ 18 = c0) (h21 : χ 21 = c0)
    (h12 : χ 12 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h15 : χ 15 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h9.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 15 9 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h9.symm) (h9.trans h.symm)
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 15 11 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h16.symm)
  exact mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl (h15.trans h20.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #12** (4+3+2): c₀ = {9, 15, 21, 27}, c₁ = {3, 6, 18}, c₂ = {12, 24}. Mono (15, 15, 20) at c0. -/
theorem compression_3_3_4_3_2_survivor12_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h6 : χ 6 = c1) (h18 : χ 18 = c1)
    (h12 : χ 12 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 3 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h6.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h6.symm) (h6.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c0 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h8_ne_c1
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c0 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h16_ne_c1
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c0 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h20_ne_c1
    · exact absurd hh h20_ne_c2
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h9.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 15 9 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h9.symm) (h9.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 15 11 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h16.symm)
  exact mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl (h15.trans h20.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #13** (4+3+2): c₀ = {3, 6, 18, 21}, c₁ = {12, 15, 27}, c₂ = {9, 24}. Mono (24, 8, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor13_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h18 : χ 18 = c0) (h21 : χ 21 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 15 22 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h27.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 21 3 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h3.symm) (h3.trans h.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h6.symm) (h6.trans h.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 21 11 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h18.symm)
  have h11 : χ 11 = c2 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact absurd hh h11_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 21 18 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 24 1 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h9.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 24 2 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h10.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  exact mono_3 24 8 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h24.trans h8.symm) (h8.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #14** (4+3+2): c₀ = {3, 6, 18, 21}, c₁ = {12, 15, 24}, c₂ = {9, 27}. Mono (27, 7, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor14_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h18 : χ 18 = c0) (h21 : χ 21 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h24 : χ 24 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 21 3 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h3.symm) (h3.trans h.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h6.symm) (h6.trans h.symm)
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 21 11 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h18.symm)
  have h11 : χ 11 = c2 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact absurd hh h11_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 21 18 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 24 4 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h12.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 24 15 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h15.symm) (h15.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 27 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h.symm) (h.trans h10.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 27 2 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h.symm) (h.trans h11.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 27 4 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h4.symm) (h4.trans h.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  exact mono_3 27 7 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h27.trans h7.symm) (h7.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #15** (4+3+2): c₀ = {12, 15, 21, 24}, c₁ = {3, 6, 18}, c₂ = {9, 27}. Mono (27, 7, 16) at c2. -/
theorem compression_3_3_4_3_2_survivor15_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h6 : χ 6 = c1) (h18 : χ 18 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 3 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h6.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h6.symm) (h6.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h5_ne_c0 : χ 5 ≠ c0 := fun h =>
    mono_3 21 5 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h12.symm)
  have h5 : χ 5 = c2 := by
    rcases chi_in_3colors 5 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h5_ne_c0
    · exact absurd hh h5_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 21 15 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h15.symm) (h15.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 24 4 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h12.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 24 13 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 24 15 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h15.symm) (h15.trans h.symm)
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 27 4 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h4.symm) (h4.trans h.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 27 5 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h5.symm) (h5.trans h.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  exact mono_3 27 7 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h27.trans h7.symm) (h7.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #16** (4+3+2): c₀ = {3, 6, 21, 24}, c₁ = {12, 15, 27}, c₂ = {9, 18}. Mono (21, 17, 24) at c0. -/
theorem compression_3_3_4_3_2_survivor16_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 15 22 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h27.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h7.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 7 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h7.symm) (h7.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 18 16 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h22.symm)
  have h16 : χ 16 = c0 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h16_ne_c1
    · exact absurd hh h16_ne_c2
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 18 17 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h23.symm)
  have h17 : χ 17 = c0 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h17_ne_c1
    · exact absurd hh h17_ne_c2
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h19.symm) (h19.trans h.symm)
  have h25 : χ 25 = c1 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact hh
    · exact absurd hh h25_ne_c2
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h20.symm) (h20.trans h.symm)
  have h26 : χ 26 = c1 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact hh
    · exact absurd hh h26_ne_c2
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 21 3 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h3.symm) (h3.trans h.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h6.symm) (h6.trans h.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  exact mono_3 21 17 24 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h17.symm) (h17.trans h24.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #17** (4+3+2): c₀ = {3, 6, 21, 27}, c₁ = {12, 15, 24}, c₂ = {9, 18}. Mono (9, 4, 7) at c2. -/
theorem compression_3_3_4_3_2_survivor17_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h24 : χ 24 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h7.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 7 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h7.symm) (h7.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h19.symm) (h19.trans h.symm)
  have h25 : χ 25 = c1 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact hh
    · exact absurd hh h25_ne_c2
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h20.symm) (h20.trans h.symm)
  have h26 : χ 26 = c1 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact hh
    · exact absurd hh h26_ne_c2
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 21 3 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h3.symm) (h3.trans h.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h6.symm) (h6.trans h.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 24 4 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h12.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 24 5 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h13.symm)
  have h5 : χ 5 = c2 := by
    rcases chi_in_3colors 5 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h5_ne_c0
    · exact absurd hh h5_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 24 14 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h14.symm) (h14.trans h.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 24 15 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h15.symm) (h15.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  exact mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h9.trans h4.symm) (h4.trans h7.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #18** (4+3+2): c₀ = {3, 6, 24, 27}, c₁ = {12, 15, 21}, c₂ = {9, 18}. Mono (24, 6, 14) at c0. -/
theorem compression_3_3_4_3_2_survivor18_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h6 : χ 6 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h21 : χ 21 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h7.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 7 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h7.symm) (h7.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h25.symm)
  have h19 : χ 19 = c0 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h19_ne_c1
    · exact absurd hh h19_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h26.symm)
  have h20 : χ 20 = c0 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h20_ne_c1
    · exact absurd hh h20_ne_c2
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 21 5 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h12.symm)
  have h5 : χ 5 = c2 := by
    rcases chi_in_3colors 5 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h5_ne_c0
    · exact absurd hh h5_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c0 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h14_ne_c1
    · exact absurd hh h14_ne_c2
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 21 15 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h15.symm) (h15.trans h.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 24 3 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h3.symm) (h3.trans h.symm)
  have h11 : χ 11 = c2 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact absurd hh h11_ne_c1
    · exact hh
  exact mono_3 24 6 14 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h24.trans h6.symm) (h6.trans h14.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #19** (4+3+2): c₀ = {12, 15, 21, 24}, c₁ = {3, 6, 27}, c₂ = {9, 18}. Mono (3, 13, 14) at c1. -/
theorem compression_3_3_4_3_2_survivor19_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h6 : χ 6 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h5_ne_c1 : χ 5 ≠ c1 := fun h =>
    mono_3 3 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h6.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h6.symm) (h6.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h3.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h7.symm)
  have h1 : χ 1 = c0 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h1_ne_c1
    · exact absurd hh h1_ne_c2
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c0 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h2_ne_c1
    · exact absurd hh h2_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 7 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h7.symm) (h7.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h25.symm)
  have h19 : χ 19 = c1 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact hh
    · exact absurd hh h19_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h26.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h5_ne_c0 : χ 5 ≠ c0 := fun h =>
    mono_3 21 5 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h12.symm)
  have h5 : χ 5 = c2 := by
    rcases chi_in_3colors 5 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h5_ne_c0
    · exact absurd hh h5_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 21 14 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h.symm) (h.trans h21.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 21 15 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h21.trans h15.symm) (h15.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 24 4 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h12.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 24 13 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h.symm) (h.trans h21.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 24 15 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h24.trans h15.symm) (h15.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 27 10 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h.symm) (h.trans h19.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 27 11 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h.symm) (h.trans h20.symm)
  have h11 : χ 11 = c2 := by
    rcases chi_in_3colors 11 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h11_ne_c0
    · exact absurd hh h11_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 27 13 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h13.symm) (h13.trans h.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 27 14 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h27.trans h14.symm) (h14.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  exact mono_3 3 13 14 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h3.trans h13.symm) (h13.trans h14.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #20** (4+3+2): c₀ = {3, 9, 15, 24}, c₁ = {6, 12, 27}, c₂ = {18, 21}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor20_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h27 : χ 27 = c1)
    (h18 : χ 18 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h18 ▸ hValid 18 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 15 19 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h24.symm)
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #21** (4+3+2): c₀ = {3, 9, 15, 27}, c₁ = {6, 12, 24}, c₂ = {18, 21}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor21_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h24 : χ 24 = c1)
    (h18 : χ 18 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h18 ▸ hValid 18 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 15 22 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h27.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #22** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {3, 9, 15}, c₂ = {18, 21}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor22_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h9 : χ 9 = c1) (h15 : χ 15 = c1)
    (h18 : χ 18 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h18 ▸ hValid 18 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #23** (4+3+2): c₀ = {6, 12, 15, 24}, c₁ = {3, 9, 27}, c₂ = {18, 21}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor23_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h9 : χ 9 = c1) (h27 : χ 27 = c1)
    (h18 : χ 18 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h18 ▸ hValid 18 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 15 1 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h6.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #24** (4+3+2): c₀ = {3, 9, 21, 27}, c₁ = {6, 12, 24}, c₂ = {15, 18}. Mono (15, 10, 15) at c2. -/
theorem compression_3_3_4_3_2_survivor24_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h24 : χ 24 = c1)
    (h15 : χ 15 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h15 ▸ hValid 15 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 15 2 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h2.symm) (h2.trans h.symm)
  have h5_ne_c2 : χ 5 ≠ c2 := fun h =>
    mono_3 15 5 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h10.symm)
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  exact mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h10.symm) (h10.trans h15.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #25** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {3, 9, 21}, c₂ = {15, 18}. Mono (15, 10, 15) at c2. -/
theorem compression_3_3_4_3_2_survivor25_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h9 : χ 9 = c1) (h21 : χ 21 = c1)
    (h15 : χ 15 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h15 ▸ hValid 15 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 15 2 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h2.symm) (h2.trans h.symm)
  have h5_ne_c2 : χ 5 ≠ c2 := fun h =>
    mono_3 15 5 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h10.symm)
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  exact mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h10.symm) (h10.trans h15.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #26** (4+3+2): c₀ = {6, 12, 21, 24}, c₁ = {3, 9, 27}, c₂ = {15, 18}. Mono (15, 10, 15) at c2. -/
theorem compression_3_3_4_3_2_survivor26_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h9 : χ 9 = c1) (h27 : χ 27 = c1)
    (h15 : χ 15 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h15 ▸ hValid 15 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 15 2 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h2.symm) (h2.trans h.symm)
  have h5_ne_c2 : χ 5 ≠ c2 := fun h =>
    mono_3 15 5 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h10.symm)
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h8.symm) (h8.trans h.symm)
  exact mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h10.symm) (h10.trans h15.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #27** (4+3+2): c₀ = {3, 9, 15, 21}, c₁ = {12, 24, 27}, c₂ = {6, 18}. Mono (12, 4, 8) at c1. -/
theorem compression_3_3_4_3_2_survivor27_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0)
    (h12 : χ 12 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #28** (4+3+2): c₀ = {3, 9, 15, 24}, c₁ = {6, 18, 21}, c₂ = {12, 27}. Mono (12, 4, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor28_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h18 : χ 18 = c1) (h21 : χ 21 = c1)
    (h12 : χ 12 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #29** (4+3+2): c₀ = {3, 9, 15, 27}, c₁ = {6, 18, 21}, c₂ = {12, 24}. Mono (12, 4, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor29_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h18 : χ 18 = c1) (h21 : χ 21 = c1)
    (h12 : χ 12 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #30** (4+3+2): c₀ = {3, 9, 15, 27}, c₁ = {12, 21, 24}, c₂ = {6, 18}. Mono (12, 4, 8) at c1. -/
theorem compression_3_3_4_3_2_survivor30_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h27 : χ 27 = c0)
    (h12 : χ 12 = c1) (h21 : χ 21 = c1) (h24 : χ 24 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #31** (4+3+2): c₀ = {3, 9, 21, 27}, c₁ = {6, 15, 18}, c₂ = {12, 24}. Mono (12, 4, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor31_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h15 : χ 15 = c1) (h18 : χ 18 = c1)
    (h12 : χ 12 = c2) (h24 : χ 24 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #32** (4+3+2): c₀ = {3, 9, 21, 27}, c₁ = {12, 15, 24}, c₂ = {6, 18}. Mono (12, 4, 8) at c1. -/
theorem compression_3_3_4_3_2_survivor32_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h9 : χ 9 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h12 : χ 12 = c1) (h15 : χ 15 = c1) (h24 : χ 24 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #33** (4+3+2): c₀ = {12, 15, 21, 24}, c₁ = {3, 9, 27}, c₂ = {6, 18}. Mono (12, 4, 8) at c0. -/
theorem compression_3_3_4_3_2_survivor33_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h9 : χ 9 = c1) (h27 : χ 27 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h12 ▸ hValid 12 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 3 8 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h9.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 3 9 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h9.symm) (h9.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c0 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h4_ne_c1
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h8 : χ 8 = c0 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h8_ne_c1
    · exact absurd hh h8_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  exact mono_3 12 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h4.symm) (h4.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #34** (4+3+2): c₀ = {3, 12, 15, 24}, c₁ = {6, 18, 21}, c₂ = {9, 27}. Mono (12, 15, 19) at c0. -/
theorem compression_3_3_4_3_2_survivor34_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h18 : χ 18 = c1) (h21 : χ 21 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 9 13 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h16.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 16 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h16.symm) (h16.trans h.symm)
  have h19 : χ 19 = c0 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h19_ne_c1
    · exact absurd hh h19_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 9 20 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h23.symm)
  have h20 : χ 20 = c0 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h20_ne_c1
    · exact absurd hh h20_ne_c2
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h23.symm) (h23.trans h.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  exact mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h15.symm) (h15.trans h19.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #35** (4+3+2): c₀ = {3, 12, 15, 24}, c₁ = {9, 21, 27}, c₂ = {6, 18}. Mono (18, 7, 13) at c2. -/
theorem compression_3_3_4_3_2_survivor35_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 9 13 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h16.symm)
  have h13 : χ 13 = c2 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact absurd hh h13_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 9 16 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h16.symm) (h16.trans h.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h7.symm)
  have h1 : χ 1 = c0 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h1_ne_c1
    · exact absurd hh h1_ne_c2
  exact mono_3 18 7 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h7.symm) (h7.trans h13.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #36** (4+3+2): c₀ = {3, 12, 15, 21}, c₁ = {6, 24, 27}, c₂ = {9, 18}. Mono (12, 21, 25) at c0. -/
theorem compression_3_3_4_3_2_survivor36_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0)
    (h6 : χ 6 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h25 : χ 25 = c0 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h25_ne_c1
    · exact absurd hh h25_ne_c2
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c1 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact hh
    · exact absurd hh h19_ne_c2
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  exact mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h21.symm) (h21.trans h25.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #37** (4+3+2): c₀ = {3, 12, 15, 24}, c₁ = {6, 21, 27}, c₂ = {9, 18}. Mono (18, 19, 25) at c2. -/
theorem compression_3_3_4_3_2_survivor37_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 9 20 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h23.symm)
  have h22_ne_c2 : χ 22 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h25.symm)
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h23.symm) (h23.trans h.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h4.symm) (h4.trans h.symm)
  have h10 : χ 10 = c1 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact hh
    · exact absurd hh h10_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 13 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h19.symm)
  have h13 : χ 13 = c1 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact hh
    · exact absurd hh h13_ne_c2
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 18 17 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h23.symm)
  have h17 : χ 17 = c1 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact hh
    · exact absurd hh h17_ne_c2
  exact mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h19.symm) (h19.trans h25.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #38** (4+3+2): c₀ = {6, 21, 24, 27}, c₁ = {3, 12, 15}, c₂ = {9, 18}. Mono (21, 6, 13) at c0. -/
theorem compression_3_3_4_3_2_survivor38_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h12 : χ 12 = c1) (h15 : χ 15 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 3 11 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h12.symm)
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h12.symm) (h12.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c0 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h7_ne_c1
    · exact absurd hh h7_ne_c2
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 15 12 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h12.symm) (h12.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h8.symm)
  have h2 : χ 2 = c0 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h2_ne_c1
    · exact absurd hh h2_ne_c2
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h4.symm) (h4.trans h.symm)
  have h10 : χ 10 = c0 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h10_ne_c1
    · exact absurd hh h10_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 8 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h8.symm) (h8.trans h.symm)
  have h14 : χ 14 = c0 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h14_ne_c1
    · exact absurd hh h14_ne_c2
  have h13_ne_c2 : χ 13 ≠ c2 := fun h =>
    mono_3 18 13 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h19.symm)
  have h13 : χ 13 = c0 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h13_ne_c1
    · exact absurd hh h13_ne_c2
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 18 19 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h19.symm) (h19.trans h.symm)
  have h25 : χ 25 = c1 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact hh
    · exact absurd hh h25_ne_c2
  exact mono_3 21 6 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h6.symm) (h6.trans h13.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #39** (4+3+2): c₀ = {3, 12, 21, 24}, c₁ = {6, 15, 18}, c₂ = {9, 27}. Mono (12, 12, 16) at c0. -/
theorem compression_3_3_4_3_2_survivor39_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h15 : χ 15 = c1) (h18 : χ 18 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 3 11 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h12.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h12.symm) (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h13 : χ 13 = c2 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact absurd hh h13_ne_c1
    · exact hh
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 9 10 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h13.symm)
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 9 13 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h13.symm) (h13.trans h.symm)
  have h16 : χ 16 = c0 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h16_ne_c1
    · exact absurd hh h16_ne_c2
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 17 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h20.symm)
  have h17 : χ 17 = c0 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h17_ne_c1
    · exact absurd hh h17_ne_c2
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 9 20 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h20.symm) (h20.trans h.symm)
  have h23 : χ 23 = c1 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact hh
    · exact absurd hh h23_ne_c2
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  exact mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl (h12.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #40** (4+3+2): c₀ = {3, 12, 21, 24}, c₁ = {9, 15, 27}, c₂ = {6, 18}. Mono (15, 4, 9) at c1. -/
theorem compression_3_3_4_3_2_survivor40_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 3 11 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h12.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h12.symm) (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 9 17 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h20.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 9 20 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h20.symm) (h20.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #41** (4+3+2): c₀ = {9, 15, 21, 27}, c₁ = {3, 12, 24}, c₂ = {6, 18}. Mono (15, 4, 9) at c0. -/
theorem compression_3_3_4_3_2_survivor41_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h12 : χ 12 = c1) (h24 : χ 24 = c1)
    (h6 : χ 6 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 3 11 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h12.symm)
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h12.symm) (h12.trans h.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c0 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h4_ne_c1
    · exact absurd hh h4_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 6 16 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h18.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 6 18 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h18.symm) (h18.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 12 3 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h3.symm) (h3.trans h.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h12.symm)
  have h8 : χ 8 = c0 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h8_ne_c1
    · exact absurd hh h8_ne_c2
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c0 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h16_ne_c1
    · exact absurd hh h16_ne_c2
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c0 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h20_ne_c1
    · exact absurd hh h20_ne_c2
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #42** (4+3+2): c₀ = {6, 12, 21, 24}, c₁ = {3, 15, 18}, c₂ = {9, 27}. Mono (12, 12, 16) at c0. -/
theorem compression_3_3_4_3_2_survivor42_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h15 : χ 15 = c1) (h18 : χ 18 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h19 : χ 19 = c2 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact absurd hh h19_ne_c1
    · exact hh
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h17 : χ 17 = c0 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h17_ne_c1
    · exact absurd hh h17_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 9 16 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h19.symm)
  have h16 : χ 16 = c0 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h16_ne_c1
    · exact absurd hh h16_ne_c2
  have h22_ne_c2 : χ 22 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h19.symm) (h19.trans h.symm)
  have h22 : χ 22 = c1 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact hh
    · exact absurd hh h22_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  exact mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl (h12.trans h16.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #43** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {3, 15, 18}, c₂ = {9, 21}. Mono (21, 2, 9) at c2. -/
theorem compression_3_3_4_3_2_survivor43_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h15 : χ 15 = c1) (h18 : χ 18 = c1)
    (h9 : χ 9 = c2) (h21 : χ 21 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h17 : χ 17 = c0 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h17_ne_c1
    · exact absurd hh h17_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 12 13 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h17.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h3.symm) (h3.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 15 13 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h18.symm)
  have h13 : χ 13 = c2 := by
    rcases chi_in_3colors 13 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h13_ne_c0
    · exact absurd hh h13_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 15 18 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h18.symm) (h18.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  exact mono_3 21 2 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h2.symm) (h2.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #44** (4+3+2): c₀ = {3, 15, 21, 24}, c₁ = {6, 12, 27}, c₂ = {9, 18}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor44_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h22_ne_c2 : χ 22 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h25.symm)
  have h22 : χ 22 = c1 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact hh
    · exact absurd hh h22_ne_c2
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 12 22 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h22.symm) (h22.trans h.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h3.symm) (h3.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 15 19 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #45** (4+3+2): c₀ = {3, 15, 21, 27}, c₁ = {6, 12, 24}, c₂ = {9, 18}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor45_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h24 : χ 24 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h26.symm)
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h3.symm) (h3.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #46** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {3, 15, 21}, c₂ = {9, 18}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor46_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h15 : χ 15 = c1) (h21 : χ 21 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h25 : χ 25 = c1 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact hh
    · exact absurd hh h25_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h3.symm) (h3.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h21.symm) (h21.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #47** (4+3+2): c₀ = {6, 12, 21, 24}, c₁ = {3, 15, 27}, c₂ = {9, 18}. Mono (18, 2, 8) at c2. -/
theorem compression_3_3_4_3_2_survivor47_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 3 14 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 3 15 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h15.symm) (h15.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h11_ne_c2 : χ 11 ≠ c2 := fun h =>
    mono_3 9 11 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h14.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h14.symm) (h14.trans h.symm)
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h26.symm)
  have h23 : χ 23 = c1 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact hh
    · exact absurd hh h23_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h17 : χ 17 = c1 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact hh
    · exact absurd hh h17_ne_c2
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 15 3 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h3.symm) (h3.trans h.symm)
  have h8 : χ 8 = c2 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact absurd hh h8_ne_c1
    · exact hh
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h15.symm)
  have h10 : χ 10 = c2 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact absurd hh h10_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 15 17 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h17.symm) (h17.trans h.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  exact mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h2.symm) (h2.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #48** (4+3+2): c₀ = {6, 12, 15, 24}, c₁ = {3, 18, 21}, c₂ = {9, 27}. Mono (12, 15, 19) at c0. -/
theorem compression_3_3_4_3_2_survivor48_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h18 : χ 18 = c1) (h21 : χ 21 = c1)
    (h9 : χ 9 = c2) (h27 : χ 27 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h17 : χ 17 = c2 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact absurd hh h17_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h17.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 9 17 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h17.symm) (h17.trans h.symm)
  have h20 : χ 20 = c0 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h20_ne_c1
    · exact absurd hh h20_ne_c2
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h19 : χ 19 = c0 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h19_ne_c1
    · exact absurd hh h19_ne_c2
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  exact mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h12.trans h15.symm) (h15.trans h19.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #49** (4+3+2): c₀ = {6, 12, 15, 24}, c₁ = {9, 21, 27}, c₂ = {3, 18}. Mono (18, 1, 7) at c2. -/
theorem compression_3_3_4_3_2_survivor49_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h3 : χ 3 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h17 : χ 17 = c1 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact hh
    · exact absurd hh h17_ne_c2
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 9 14 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h17.symm)
  have h14 : χ 14 = c2 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact absurd hh h14_ne_c1
    · exact hh
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 9 17 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h17.symm) (h17.trans h.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c1 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact hh
    · exact absurd hh h19_ne_c2
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 15 1 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h6.symm)
  have h1 : χ 1 = c2 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact absurd hh h1_ne_c1
    · exact hh
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c2 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact absurd hh h7_ne_c1
    · exact hh
  exact mono_3 18 1 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h1.symm) (h1.trans h7.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #50** (4+3+2): c₀ = {3, 21, 24, 27}, c₁ = {6, 12, 15}, c₂ = {9, 18}. Mono (21, 1, 8) at c0. -/
theorem compression_3_3_4_3_2_survivor50_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h3 : χ 3 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h15 : χ 15 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
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
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c1 : χ 13 ≠ c1 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h11_ne_c1 : χ 11 ≠ c1 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 15 1 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h6.symm)
  have h1 : χ 1 = c0 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h1_ne_c1
    · exact absurd hh h1_ne_c2
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c0 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h7_ne_c1
    · exact absurd hh h7_ne_c2
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h2.symm) (h2.trans h.symm)
  have h8 : χ 8 = c0 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h8_ne_c1
    · exact absurd hh h8_ne_c2
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h4.symm) (h4.trans h.symm)
  have h10 : χ 10 = c0 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h10_ne_c1
    · exact absurd hh h10_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 14 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h20.symm)
  have h14 : χ 14 = c0 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h14_ne_c1
    · exact absurd hh h14_ne_c2
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h20.symm) (h20.trans h.symm)
  have h26 : χ 26 = c1 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact hh
    · exact absurd hh h26_ne_c2
  exact mono_3 21 1 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h21.trans h1.symm) (h1.trans h8.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #51** (4+3+2): c₀ = {6, 12, 15, 24}, c₁ = {3, 21, 27}, c₂ = {9, 18}. Mono (18, 20, 26) at c2. -/
theorem compression_3_3_4_3_2_survivor51_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h24 : χ 24 = c0)
    (h3 : χ 3 = c1) (h21 : χ 21 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h26 : χ 26 = c2 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h26_ne_c0
    · exact absurd hh h26_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h23_ne_c2 : χ 23 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h26.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 12 15 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h15.symm) (h15.trans h.symm)
  have h19 : χ 19 = c1 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact hh
    · exact absurd hh h19_ne_c2
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 15 1 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h6.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h8_ne_c2 : χ 8 ≠ c2 := fun h =>
    mono_3 18 2 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h2.symm) (h2.trans h.symm)
  have h8 : χ 8 = c1 := by
    rcases chi_in_3colors 8 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h8_ne_c0
    · exact hh
    · exact absurd hh h8_ne_c2
  have h10_ne_c2 : χ 10 ≠ c2 := fun h =>
    mono_3 18 4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h4.symm) (h4.trans h.symm)
  have h10 : χ 10 = c1 := by
    rcases chi_in_3colors 10 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h10_ne_c0
    · exact hh
    · exact absurd hh h10_ne_c2
  have h14_ne_c2 : χ 14 ≠ c2 := fun h =>
    mono_3 18 14 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h20.symm)
  have h14 : χ 14 = c1 := by
    rcases chi_in_3colors 14 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h14_ne_c0
    · exact hh
    · exact absurd hh h14_ne_c2
  have h16_ne_c2 : χ 16 ≠ c2 := fun h =>
    mono_3 18 16 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h18.trans h.symm) (h.trans h22.symm)
  have h16 : χ 16 = c1 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact hh
    · exact absurd hh h16_ne_c2
  exact mono_3 18 20 26 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h18.trans h20.symm) (h20.trans h26.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #52** (4+3+2): c₀ = {6, 12, 15, 21}, c₁ = {3, 24, 27}, c₂ = {9, 18}. Mono (15, 21, 26) at c0. -/
theorem compression_3_3_4_3_2_survivor52_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0)
    (h3 : χ 3 = c1) (h24 : χ 24 = c1) (h27 : χ 27 = c1)
    (h9 : χ 9 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h23_ne_c1 : χ 23 ≠ c1 := fun h =>
    mono_3 3 23 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h24.symm)
  have h25_ne_c1 : χ 25 ≠ c1 := fun h =>
    mono_3 3 24 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h24.symm) (h24.trans h.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 3 26 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h27.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h13_ne_c0 : χ 13 ≠ c0 := fun h =>
    mono_3 6 13 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h15.symm)
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 6 15 17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h15.symm) (h15.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h23 : χ 23 = c2 := by
    rcases chi_in_3colors 23 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h23_ne_c0
    · exact absurd hh h23_ne_c1
    · exact hh
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h20_ne_c2 : χ 20 ≠ c2 := fun h =>
    mono_3 9 20 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h23.symm)
  have h26_ne_c2 : χ 26 ≠ c2 := fun h =>
    mono_3 9 23 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h23.symm) (h23.trans h.symm)
  have h26 : χ 26 = c0 := by
    rcases chi_in_3colors 26 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h26_ne_c1
    · exact absurd hh h26_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h11_ne_c0 : χ 11 ≠ c0 := fun h =>
    mono_3 12 11 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h15.symm)
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  have h25 : χ 25 = c2 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact absurd hh h25_ne_c1
    · exact hh
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 12 22 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h26.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 15 1 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h6.symm)
  have h1 : χ 1 = c1 := by
    rcases chi_in_3colors 1 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h1_ne_c0
    · exact hh
    · exact absurd hh h1_ne_c2
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 15 7 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h15.trans h.symm) (h.trans h12.symm)
  have h7 : χ 7 = c1 := by
    rcases chi_in_3colors 7 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h7_ne_c0
    · exact hh
    · exact absurd hh h7_ne_c2
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 15 15 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h15.trans h.symm)
  have h20 : χ 20 = c1 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact hh
    · exact absurd hh h20_ne_c2
  exact mono_3 15 21 26 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h21.symm) (h21.trans h26.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #53** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {3, 18, 21}, c₂ = {9, 15}. Mono (15, 4, 9) at c2. -/
theorem compression_3_3_4_3_2_survivor53_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h3 : χ 3 = c1) (h18 : χ 18 = c1) (h21 : χ 21 = c1)
    (h9 : χ 9 = c2) (h15 : χ 15 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c1 : χ 17 ≠ c1 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c1 : χ 19 ≠ c1 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 3 20 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h21.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 3 21 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h21.symm) (h21.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c2 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact absurd hh h4_ne_c1
    · exact hh
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c2 : χ 1 ≠ c2 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c2 : χ 7 ≠ c2 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h22.symm)
  have h19 : χ 19 = c0 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h19_ne_c1
    · exact absurd hh h19_ne_c2
  have h25_ne_c2 : χ 25 ≠ c2 := fun h =>
    mono_3 9 22 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h22.symm) (h22.trans h.symm)
  have h25 : χ 25 = c1 := by
    rcases chi_in_3colors 25 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h25_ne_c0
    · exact hh
    · exact absurd hh h25_ne_c2
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c2 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact absurd hh h2_ne_c1
    · exact hh
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 19 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h19.symm) (h19.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h20 : χ 20 = c2 := by
    rcases chi_in_3colors 20 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h20_ne_c0
    · exact absurd hh h20_ne_c1
    · exact hh
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #54** (4+3+2): c₀ = {6, 12, 21, 24}, c₁ = {9, 15, 27}, c₂ = {3, 18}. Mono (15, 4, 9) at c1. -/
theorem compression_3_3_4_3_2_survivor54_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h21 : χ 21 = c0) (h24 : χ 24 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h27 : χ 27 = c1)
    (h3 : χ 3 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h19_ne_c0 : χ 19 ≠ c0 := fun h =>
    mono_3 6 19 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h21.symm)
  have h19 : χ 19 = c1 := by
    rcases chi_in_3colors 19 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h19_ne_c0
    · exact hh
    · exact absurd hh h19_ne_c2
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 6 21 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h21.symm) (h21.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 9 16 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h19.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 9 19 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h19.symm) (h19.trans h.symm)
  have h22 : χ 22 = c2 := by
    rcases chi_in_3colors 22 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h22_ne_c0
    · exact absurd hh h22_ne_c1
    · exact hh
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h16 : χ 16 = c2 := by
    rcases chi_in_3colors 16 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h16_ne_c0
    · exact absurd hh h16_ne_c1
    · exact hh
  have h17_ne_c0 : χ 17 ≠ c0 := fun h =>
    mono_3 12 17 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h21.symm)
  have h17 : χ 17 = c1 := by
    rcases chi_in_3colors 17 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h17_ne_c0
    · exact hh
    · exact absurd hh h17_ne_c2
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 12 21 25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h21.symm) (h21.trans h.symm)
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #55** (4+3+2): c₀ = {6, 12, 24, 27}, c₁ = {9, 15, 21}, c₂ = {3, 18}. Mono (15, 4, 9) at c1. -/
theorem compression_3_3_4_3_2_survivor55_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h6 : χ 6 = c0) (h12 : χ 12 = c0) (h24 : χ 24 = c0) (h27 : χ 27 = c0)
    (h9 : χ 9 = c1) (h15 : χ 15 = c1) (h21 : χ 21 = c1)
    (h3 : χ 3 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c0 : χ 4 ≠ c0 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c1 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h4_ne_c0
    · exact hh
    · exact absurd hh h4_ne_c2
  have h8_ne_c0 : χ 8 ≠ c0 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c0 : χ 10 ≠ c0 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c0 : χ 14 ≠ c0 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c0 : χ 22 ≠ c0 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c0 : χ 26 ≠ c0 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h25_ne_c0 : χ 25 ≠ c0 := fun h =>
    mono_3 6 25 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h27.symm)
  have h1_ne_c1 : χ 1 ≠ c1 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c1 : χ 7 ≠ c1 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h2_ne_c0 : χ 2 ≠ c0 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c1 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact absurd hh h2_ne_c0
    · exact hh
    · exact absurd hh h2_ne_c2
  have h16_ne_c0 : χ 16 ≠ c0 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c0 : χ 20 ≠ c0 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  have h23_ne_c0 : χ 23 ≠ c0 := fun h =>
    mono_3 12 23 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h27.symm)
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

set_option maxHeartbeats 16000000 in
/-- **R433 Survivor #56** (4+3+2): c₀ = {9, 15, 21, 27}, c₁ = {6, 12, 24}, c₂ = {3, 18}. Mono (15, 4, 9) at c0. -/
theorem compression_3_3_4_3_2_survivor56_infeasible
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hAvoid : AvoidsMonoSolution 3 27 χ)
    {c0 c1 c2 : ℕ}
    (h9 : χ 9 = c0) (h15 : χ 15 = c0) (h21 : χ 21 = c0) (h27 : χ 27 = c0)
    (h6 : χ 6 = c1) (h12 : χ 12 = c1) (h24 : χ 24 = c1)
    (h3 : χ 3 = c2) (h18 : χ 18 = c2)
    (hc01 : c0 ≠ c1) (hc02 : c0 ≠ c2) (hc12 : c1 ≠ c2) :
    False := by
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hc0_lt : c0 < 3 := h9 ▸ hValid 9 (by norm_num) (by norm_num)
  have hc1_lt : c1 < 3 := h6 ▸ hValid 6 (by norm_num) (by norm_num)
  have hc2_lt : c2 < 3 := h3 ▸ hValid 3 (by norm_num) (by norm_num)
  have chi_in_3colors : ∀ p, 0 < p → p ≤ 27 → χ p = c0 ∨ χ p = c1 ∨ χ p = c2 := by
    intro p hp1 hp2
    have hp_lt : χ p < 3 := hValid p hp1 hp2
    by_contra hne
    have hne0 : χ p ≠ c0 := fun h => hne (Or.inl h)
    have hne1 : χ p ≠ c1 := fun h => hne (Or.inr (Or.inl h))
    have hne2 : χ p ≠ c2 := fun h => hne (Or.inr (Or.inr h))
    omega
  have h2_ne_c2 : χ 2 ≠ c2 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h3.symm)
  have h4_ne_c2 : χ 4 ≠ c2 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h3.trans h.symm)
  have h17_ne_c2 : χ 17 ≠ c2 := fun h =>
    mono_3 3 17 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h.symm) (h.trans h18.symm)
  have h19_ne_c2 : χ 19 ≠ c2 := fun h =>
    mono_3 3 18 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h3.trans h18.symm) (h18.trans h.symm)
  have h4_ne_c1 : χ 4 ≠ c1 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h6.symm)
  have h4 : χ 4 = c0 := by
    rcases chi_in_3colors 4 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h4_ne_c1
    · exact absurd hh h4_ne_c2
  have h8_ne_c1 : χ 8 ≠ c1 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h6.trans h.symm)
  have h10_ne_c1 : χ 10 ≠ c1 := fun h =>
    mono_3 6 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h12.symm)
  have h14_ne_c1 : χ 14 ≠ c1 := fun h =>
    mono_3 6 12 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h12.symm) (h12.trans h.symm)
  have h22_ne_c1 : χ 22 ≠ c1 := fun h =>
    mono_3 6 22 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h.symm) (h.trans h24.symm)
  have h26_ne_c1 : χ 26 ≠ c1 := fun h =>
    mono_3 6 24 26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h6.trans h24.symm) (h24.trans h.symm)
  have h1_ne_c0 : χ 1 ≠ c0 := fun h =>
    mono_3 9 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h.symm) (h.trans h4.symm)
  have h7_ne_c0 : χ 7 ≠ c0 := fun h =>
    mono_3 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h9.trans h4.symm) (h4.trans h.symm)
  have h2_ne_c1 : χ 2 ≠ c1 := fun h =>
    mono_3 12 2 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h6.symm)
  have h2 : χ 2 = c0 := by
    rcases chi_in_3colors 2 (by norm_num) (by norm_num) with hh | hh | hh
    · exact hh
    · exact absurd hh h2_ne_c1
    · exact absurd hh h2_ne_c2
  have h16_ne_c1 : χ 16 ≠ c1 := fun h =>
    mono_3 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rfl (h12.trans h.symm)
  have h20_ne_c1 : χ 20 ≠ c1 := fun h =>
    mono_3 12 20 24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (h12.trans h.symm) (h.trans h24.symm)
  exact mono_3 15 4 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (h15.trans h4.symm) (h4.trans h9.symm)

