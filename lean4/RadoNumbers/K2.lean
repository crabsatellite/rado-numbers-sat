/-
  RadoNumbers/K2.lean

  Lemma `lem:compress2` (Color Compression Lemma; paper-novel
  analytic claim) and Theorem `thm:k2` ($R_2(b) = b^2$ for all
  $b \ge 2$). Companion to Li 2026 "On Rado Numbers for
  $x + by = bz$".

  The Color Compression Lemma is a paper-novel structural claim:
  any valid 2-coloring of $\{1, …, b^2 - 1\}$ avoiding monochromatic
  solutions assigns ALL multiples of $b$ the same color. We encode
  it here as a Cat 3 paper-novel working assumption (status
  `gapOpen`) pending direct in-Lean derivation; the analytic proof
  appears in the paper's Lemma `lem:compress2`.

  The case $b = 2$ is a small finite-enumeration result attributable
  to Landman–Robertson ($R_2(2) = 4 = S(3)$ via the auxiliary
  equation $x + 2y = 2z$, reducing to a $4$-element check); we
  encode it as a Cat 2 external citation.

  Theorem `thm_k2` then derives `IsRadoNumber b 2 (b^2)` by
  combining `thm_lower` (Cat 2 b-adic-valuation atoms) with the
  upper bound, which goes by case analysis on `χ(b^2)` using the
  Color Compression Lemma for $b \ge 3$ and by direct finite check
  for $b = 2$.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Color Compression Lemma `lem:compress2` — ANALYTIC PROOF.

  Previously a Cat 3 `gapOpen` working assumption; Round 14
  Lean-derives the paper's minimal-deviation argument, converting
  it to a `gapClosed` theorem.

  **Paper proof structure** (Li 2026, §4 Lemma `lem:compress2`):
  strong induction on $i$. Base $i = 1$ trivial. For $i \ge 2$,
  with $\chi(b \cdot j) = \chi(b) =: c_0$ for all $j < i$ (IH):
  suppose $\chi(b \cdot i) \ne c_0$.

  * For each $j \in [1, i-1]$, the triple $(b \cdot j, b, b + j)$
    forces $\chi(b + j) \ne c_0$ (since $\chi(b \cdot j) = c_0 =
    \chi(b)$). In particular $\chi(b + (i-1)) \ne c_0$.
  * The triple $(b, b-1, b)$ (satisfying $b + b(b-1) = b^2$) forces
    $\chi(b-1) \ne c_0$.
  * With 2 colors, $\chi(b-1) = \chi(b+(i-1)) = \chi(b \cdot i) =
    1 - c_0$. The triple $(b \cdot i, b-1, b+(i-1))$ (satisfying
    $b i + b(b-1) = b(b + i - 1)$) is then monochromatic —
    contradiction.
-/
theorem lem_compress2 (b : ℕ) (hb : 3 ≤ b) (χ : ℕ → ℕ)
    (hValid : IsValidColoring (b ^ 2 - 1) 2 χ)
    (hAvoid : AvoidsMonoSolution b (b ^ 2 - 1) χ) :
    ∀ i, 1 ≤ i → i ≤ b - 1 → χ (b * i) = χ b := by
  have hb_pos : 0 < b := by linarith
  have hsq : b ^ 2 = b * b := by ring
  -- Key product identity: b·(b-1) + b = b·b.
  have hbb : b * (b - 1) + b = b * b := by
    have hbm1 : (b - 1) + 1 = b := by omega
    calc b * (b - 1) + b
        = b * (b - 1) + b * 1 := by ring
      _ = b * ((b - 1) + 1) := by ring
      _ = b * b := by rw [hbm1]
  have h3b : 3 * b ≤ b * b := Nat.mul_le_mul_right b hb
  have h2b : 2 * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
  -- b ≤ b^2 - 1.
  have hb_le : b ≤ b ^ 2 - 1 := by omega
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi_lb hi_ub
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · -- Base: i = 1.
      have : i = 1 := by omega
      rw [this, Nat.mul_one]
    · -- Inductive: i ≥ 2.
      by_contra hne
      set c0 := χ b with hc0_def
      have hc0_lt : c0 < 2 := hValid b hb_pos hb_le
      -- b * i ≤ b^2 - 1, since i ≤ b - 1.
      have hbi_mul_le : b * i ≤ b * (b - 1) := Nat.mul_le_mul_left b hi_ub
      have hbi_le : b * i ≤ b ^ 2 - 1 := by omega
      have hbi_pos : 1 ≤ b * i := by
        have : 0 < b * i := Nat.mul_pos hb_pos (by omega)
        omega
      have hχbi_lt : χ (b * i) < 2 := hValid (b * i) hbi_pos hbi_le
      -- b - 1 bounds.
      have hbm1_pos : 1 ≤ b - 1 := by omega
      have hbm1_le : b - 1 ≤ b ^ 2 - 1 := by omega
      have hχbm1_lt : χ (b - 1) < 2 := hValid (b - 1) hbm1_pos hbm1_le
      -- b + (i-1) bounds: b + (i-1) ≤ 2b - 2 ≤ b^2 - 1.
      have hbplus_le : b + (i - 1) ≤ b ^ 2 - 1 := by omega
      have hbplus_pos : 1 ≤ b + (i - 1) := by omega
      have hχbplus_lt : χ (b + (i - 1)) < 2 :=
        hValid (b + (i - 1)) hbplus_pos hbplus_le
      -- (1) χ(b-1) ≠ c0 via triple (b, b-1, b): b + b(b-1) = b·b.
      have hχbm1_ne : χ (b - 1) ≠ c0 := by
        intro hcon
        apply hAvoid
        refine ⟨b, b - 1, b, hb_le, hbm1_le, hb_le, ?_, hcon.symm, hcon⟩
        refine ⟨hb_pos, hbm1_pos, hb_pos, ?_⟩
        omega
      -- (2) χ(b + (i-1)) ≠ c0 via triple (b·(i-1), b, b+(i-1)).
      have hi1_lt : i - 1 < i := by omega
      have hi1_lb : 1 ≤ i - 1 := by omega
      have hi1_ub : i - 1 ≤ b - 1 := by omega
      have hχbi1 : χ (b * (i - 1)) = c0 := IH (i - 1) hi1_lt hi1_lb hi1_ub
      have hbi1_mul_le : b * (i - 1) ≤ b * (b - 1) :=
        Nat.mul_le_mul_left b hi1_ub
      have hbi1_le : b * (i - 1) ≤ b ^ 2 - 1 := by omega
      have hbi1_pos : 1 ≤ b * (i - 1) := by
        have : 0 < b * (i - 1) := Nat.mul_pos hb_pos (by omega)
        omega
      have hχbplus_ne : χ (b + (i - 1)) ≠ c0 := by
        intro hcon
        apply hAvoid
        refine ⟨b * (i - 1), b, b + (i - 1), hbi1_le, hb_le, hbplus_le,
                ?_, hχbi1, hcon.symm⟩
        refine ⟨hbi1_pos, hb_pos, hbplus_pos, ?_⟩
        -- b·(i-1) + b·b = b·(b + (i-1))
        ring
      -- (3) Final contradiction via triple (b·i, b-1, b+(i-1)).
      apply hAvoid
      refine ⟨b * i, b - 1, b + (i - 1), hbi_le, hbm1_le, hbplus_le, ?_, ?_, ?_⟩
      · refine ⟨hbi_pos, hbm1_pos, hbplus_pos, ?_⟩
        -- b·i + b·(b-1) = b·(b + (i-1))
        have hi_split : b * i = b * (i - 1) + b := by
          have hi_eq : i = (i - 1) + 1 := by omega
          calc b * i = b * ((i - 1) + 1) := by rw [← hi_eq]
            _ = b * (i - 1) + b := by ring
        have hrhs : b * (b + (i - 1)) = b * b + b * (i - 1) := by ring
        rw [hi_split, hrhs]
        omega
      · -- χ(b·i) = χ(b-1): both ≠ c0, both < 2 ⟹ both = 1 - c0.
        omega
      · -- χ(b-1) = χ(b+(i-1)): both ≠ c0, both < 2 ⟹ both = 1 - c0.
        omega

/-! ### Small finite case $b = 2$ — ANALYTIC PROOF. -/

/--
  **Theorem `thm_k2_b2`.** $R_2(2) \le 4$: every valid 2-coloring
  of $\{1, 2, 3, 4\}$ contains a monochromatic solution to
  $x + 2y = 2z$.

  Previously a Cat 2 `gapOpen` axiom; Round 15
  Lean-derives it by explicit case analysis, converting to a
  `gapClosed` theorem.

  **Proof**: the five Rado triples in $\{1,2,3,4\}$ for $b = 2$
  are $(2,1,2), (2,2,3), (2,3,4), (4,1,3), (4,2,4)$ with mono
  conditions $\chi_1 = \chi_2$, $\chi_2 = \chi_3$,
  $\chi_2 = \chi_3 = \chi_4$, $\chi_4 = \chi_1 = \chi_3$,
  $\chi_2 = \chi_4$. If $T_1$ ($\chi_1 = \chi_2$), $T_2$
  ($\chi_2 = \chi_3$), $T_5$ ($\chi_2 = \chi_4$) all fail, then
  over $\{0,1\}$ we get $\chi_1 = \chi_3 = \chi_4 = 1 - \chi_2$,
  so $T_4$ ($\chi_4 = \chi_1 = \chi_3$) holds.
-/
theorem thm_k2_b2 : RadoNumberAtMost 2 2 4 := by
  intro χ hValid
  have h1 : χ 1 < 2 := hValid 1 (by norm_num) (by norm_num)
  have h2 : χ 2 < 2 := hValid 2 (by norm_num) (by norm_num)
  have h3 : χ 3 < 2 := hValid 3 (by norm_num) (by norm_num)
  have h4 : χ 4 < 2 := hValid 4 (by norm_num) (by norm_num)
  by_cases hT1 : χ 1 = χ 2
  · -- Triple (2,1,2): 2 + 2·1 = 2·2.
    exact ⟨2, 1, 2, by norm_num, by norm_num, by norm_num,
           ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hT1.symm, hT1⟩
  · by_cases hT2 : χ 2 = χ 3
    · -- Triple (2,2,3): 2 + 2·2 = 2·3.
      exact ⟨2, 2, 3, by norm_num, by norm_num, by norm_num,
             ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, rfl, hT2⟩
    · by_cases hT5 : χ 2 = χ 4
      · -- Triple (4,2,4): 4 + 2·2 = 2·4.
        exact ⟨4, 2, 4, by norm_num, by norm_num, by norm_num,
               ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
               hT5.symm, hT5⟩
      · -- ¬T1, ¬T2, ¬T5: over {0,1}, χ1 = χ3 = χ4 = 1 - χ2. Triple (4,1,3).
        exact ⟨4, 1, 3, by norm_num, by norm_num, by norm_num,
               ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
               by omega, by omega⟩

/-! ### Derived theorem — upper bound for $b \ge 3$. -/

/--
  Upper bound for $b \ge 3$: every valid 2-coloring of
  $\{1, …, b^2\}$ contains a monochromatic solution.
-/
theorem thm_k2_upper_ge_3 (b : ℕ) (hb : 3 ≤ b) :
    RadoNumberAtMost b 2 (b ^ 2) := by
  intro χ hValid
  have hb_pos : 0 < b := by linarith
  have hb_sq_pos : 0 < b ^ 2 := by positivity
  have hb_le_sq : b ≤ b ^ 2 := by nlinarith
  have h2b_le_sq : 2 * b ≤ b ^ 2 := by nlinarith
  have hbp1_le_sq : b + 1 ≤ b ^ 2 := by nlinarith
  -- b * (b - 1) + b = b^2
  have hbm1_plus_b : b * (b - 1) + b = b ^ 2 := by
    have h : b - 1 + 1 = b := Nat.sub_add_cancel (by linarith : 1 ≤ b)
    calc b * (b - 1) + b
        = b * ((b - 1) + 1) := by ring
      _ = b * b := by rw [h]
      _ = b ^ 2 := by ring
  have hbm1_in : b * (b - 1) ≤ b ^ 2 - 1 := by omega
  have hValid' : IsValidColoring (b ^ 2 - 1) 2 χ := fun m hm_lb hm_ub =>
    hValid m hm_lb (by omega)
  by_cases hAvoid : AvoidsMonoSolution b (b ^ 2 - 1) χ
  · -- Pos: apply compression lemma
    have hCompress := lem_compress2 b hb χ hValid' hAvoid
    set c0 : ℕ := χ b with hc0_def
    have hChi_b : χ b = c0 := rfl
    have hChi_2b : χ (b * 2) = c0 := hCompress 2 (by linarith) (by omega)
    have hbm1_pos : 1 ≤ b - 1 := by omega
    have hChi_b_bm1 : χ (b * (b - 1)) = c0 := hCompress (b - 1) hbm1_pos (le_refl _)
    have hChi_b_lt : χ b < 2 := hValid b hb_pos hb_le_sq
    have hc0_lt : c0 < 2 := hChi_b_lt
    by_cases hCase : χ (b ^ 2) = c0
    · -- Case A: triple (b^2, b, 2b)
      have h2b_comm : b * 2 ≤ b ^ 2 := by linarith
      refine ⟨b ^ 2, b, b * 2, le_refl _, hb_le_sq, h2b_comm, ?_, ?_, ?_⟩
      · refine ⟨hb_sq_pos, hb_pos, Nat.mul_pos hb_pos (by norm_num), ?_⟩
        ring
      · rw [hCase, hChi_b]
      · rw [hChi_b, hChi_2b]
    · -- Case B: χ(b^2) ≠ c0
      have hChi_b2_lt : χ (b ^ 2) < 2 := hValid (b ^ 2) hb_sq_pos (le_refl _)
      -- hEq_1 and hRT_1
      have hEq_1 : b * (b - 1) + b * 1 = b * b := by
        have h : b - 1 + 1 = b := Nat.sub_add_cancel (by linarith : 1 ≤ b)
        calc b * (b - 1) + b * 1
            = b * ((b - 1) + 1) := by ring
          _ = b * b := by rw [h]
      have hRT_1 : IsRadoTriple b (b * (b - 1)) 1 b := by
        refine ⟨Nat.mul_pos hb_pos (by omega), by norm_num, hb_pos, ?_⟩
        have : b * b = b ^ 2 := by ring
        linarith [hEq_1]
      -- Step 1: χ(1) ≠ c0
      have hChi_1_ne : χ 1 ≠ c0 := by
        intro hContra
        apply hAvoid
        refine ⟨b * (b - 1), 1, b, hbm1_in, ?_, ?_, hRT_1, ?_, ?_⟩
        · omega
        · linarith [Nat.sub_le (b ^ 2) 1]
        · rw [hChi_b_bm1, hContra]
        · rw [hContra, hChi_b]
      have hChi_1_lt : χ 1 < 2 := hValid 1 (by norm_num) (by linarith)
      have hChi_1_val : χ 1 = 1 - c0 := by omega
      -- hEq_2 and hRT_2
      have hEq_2 : b * (b - 1) + b * (b + 1) = b * (2 * b) := by
        have h : b - 1 + (b + 1) = 2 * b := by omega
        calc b * (b - 1) + b * (b + 1)
            = b * ((b - 1) + (b + 1)) := by ring
          _ = b * (2 * b) := by rw [h]
      have hRT_2 : IsRadoTriple b (b * (b - 1)) (b + 1) (2 * b) := by
        refine ⟨Nat.mul_pos hb_pos (by omega), by linarith, by linarith, ?_⟩
        linarith [hEq_2]
      -- Step 2: χ(b+1) ≠ c0
      have hbp1_le_bm1 : b + 1 ≤ b ^ 2 - 1 := by
        have : b + 2 ≤ b ^ 2 := by nlinarith
        omega
      have h2b_le_bm1 : 2 * b ≤ b ^ 2 - 1 := by
        have : 2 * b + 1 ≤ b ^ 2 := by nlinarith
        omega
      have hChi_bp1_ne : χ (b + 1) ≠ c0 := by
        intro hContra
        apply hAvoid
        refine ⟨b * (b - 1), b + 1, 2 * b, hbm1_in, hbp1_le_bm1, h2b_le_bm1, hRT_2, ?_, ?_⟩
        · rw [hChi_b_bm1, hContra]
        · rw [hContra]
          have h2b_eq : (2 * b : ℕ) = b * 2 := by ring
          rw [h2b_eq]
          exact hChi_2b.symm
      have hChi_bp1_lt : χ (b + 1) < 2 := hValid (b + 1) (by linarith) hbp1_le_sq
      have hChi_bp1_val : χ (b + 1) = 1 - c0 := by omega
      have hChi_b2_val : χ (b ^ 2) = 1 - c0 := by omega
      -- Triple (b^2, 1, b+1)
      refine ⟨b ^ 2, 1, b + 1, le_refl _, by linarith, hbp1_le_sq, ?_, ?_, ?_⟩
      · refine ⟨hb_sq_pos, by norm_num, by linarith, ?_⟩
        ring
      · rw [hChi_b2_val, hChi_1_val]
      · rw [hChi_1_val, hChi_bp1_val]
  · -- Neg: already a mono on smaller domain
    have hMono : HasMonoSolution b (b ^ 2 - 1) χ := by
      by_contra h
      exact hAvoid h
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    refine ⟨x, y, z, ?_, ?_, ?_, hRT, hxy, hyz⟩
    · exact le_trans hxn (Nat.sub_le _ _)
    · exact le_trans hyn (Nat.sub_le _ _)
    · exact le_trans hzn (Nat.sub_le _ _)

/-! ### Main theorem `thm:k2`. -/

/--
  **Theorem `thm:k2`.** For all $b \ge 2$, $R_2(b) = b^2$.
-/
theorem thm_k2 (b : ℕ) (hb : 2 ≤ b) :
    IsRadoNumber b 2 (b ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact thm_lower b 2 hb (by norm_num)
  · rcases Nat.lt_or_ge b 3 with hb_lt | hb_ge
    · have hb_eq : b = 2 := by omega
      subst hb_eq
      exact thm_k2_b2
    · exact thm_k2_upper_ge_3 b hb_ge

end RadoNumbers
