/-
  RadoNumbers/General/BasicResults.lean

  Basic structural results about LinearEquation partition regularity.

  These are TRIVIAL/EASY directions of Rado-type results, provable without
  deep theory. They form the warm-up for eventual full Rado theorem.
-/

import RadoNumbers.General.PartitionRegular
import RadoNumbers.General.BAdicEquation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RadoNumbers.General

/--
  **Trivial: every equation with a bounded positive solution is
  1-partition regular at that bound.**

  For k = 1, the only color is 0. Any positive solution to the equation
  is automatically monochromatic (all colors are 0).
-/
theorem isKPartitionRegularAt_one_of_hasPosSolution
    (eq : LinearEquation) (N : ℕ)
    (h : ∃ x : ℕ → ℕ, eq.IsPositiveSolution x ∧
      (∀ i, i < eq.numVars → x i ≤ N)) :
    IsKPartitionRegularAt eq 1 N := by
  obtain ⟨x, hpos, hbound⟩ := h
  intro χ hχk
  refine ⟨x, hbound, hpos, ?_⟩
  -- Show all χ(x i) are equal: since k = 1, they're all 0.
  intro i j hi hj
  have hxi_pos : 0 < x i := hpos.1 i hi
  have hxj_pos : 0 < x j := hpos.1 j hj
  have hxi_le : x i ≤ N := hbound i hi
  have hxj_le : x j ≤ N := hbound j hj
  have hxi_color : χ (x i) < 1 := hχk (x i) hxi_pos hxi_le
  have hxj_color : χ (x j) < 1 := hχk (x j) hxj_pos hxj_le
  omega

/--
  **Monotonicity of `IsKPartitionRegularAt` in N.**

  If equation eq is k-partition-regular at bound N, then it's also
  k-partition-regular at any larger bound N' ≥ N.

  Proof: a k-coloring of [1, N'] restricted to [1, N] is also a k-coloring;
  mono solution found in [1, N] is also a mono solution in [1, N'] since
  N ≤ N'.

  This is a basic structural property allowing us to define the
  Rado number as the MINIMAL N where partition regularity holds.
-/
theorem isKPartitionRegularAt_mono
    (eq : LinearEquation) (k N N' : ℕ) (hN : N ≤ N')
    (h : IsKPartitionRegularAt eq k N) :
    IsKPartitionRegularAt eq k N' := by
  intro χ hχk
  have hχk_restricted : IsKColoring N k χ := by
    intro i hi1 hiN
    exact hχk i hi1 (le_trans hiN hN)
  obtain ⟨x, hbound, hpos, hcolor⟩ := h χ hχk_restricted
  refine ⟨x, ?_, hpos, hcolor⟩
  intro i hi
  exact le_trans (hbound i hi) hN

/--
  **Bound elaboration**: if there exists N witnessing partition regularity,
  then all bounds ≥ N also witness it.

  Direct consequence of `isKPartitionRegularAt_mono`.
-/
theorem isKPartitionRegular_iff_eventually
    (eq : LinearEquation) (k : ℕ) :
    IsKPartitionRegular eq k ↔ ∃ N, ∀ N', N ≤ N' → IsKPartitionRegularAt eq k N' := by
  constructor
  · intro ⟨N, hN⟩
    exact ⟨N, fun N' hNN' => isKPartitionRegularAt_mono eq k N N' hNN' hN⟩
  · intro ⟨N, hN⟩
    exact ⟨N, hN N (le_refl N)⟩

/--
  **IsRadoNumber from bounds**: combining upper bound (partition-regular at N)
  and lower bound (not partition-regular at N - 1) gives `IsRadoNumber eq k N`.

  Proof uses monotonicity: ¬ partition-regular at N-1 propagates downward
  to all M ≤ N-1, i.e., M < N.

  This is the standard way to prove R_k(eq) = N exactly.
-/
theorem isRadoNumber_of_bounds
    (eq : LinearEquation) (k N : ℕ) (hN : 1 ≤ N)
    (hUpper : IsKPartitionRegularAt eq k N)
    (hLower : ¬ IsKPartitionRegularAt eq k (N - 1)) :
    IsRadoNumber eq k N := by
  refine ⟨hUpper, fun M hM hPR => ?_⟩
  apply hLower
  exact isKPartitionRegularAt_mono eq k M (N - 1) (by omega) hPR

/--
  **Partition regularity requires existence of a positive solution.**

  If `eq` is k-partition-regular (for any k ≥ 1), then it has at least one
  positive solution. Otherwise mono solutions wouldn't exist for any coloring.

  Proof: apply partition regularity to the trivial constant-0 coloring.
  Any mono solution (which exists by partition regularity) is in particular
  a positive solution.
-/
theorem isKPartitionRegular_hasPosSolution
    (eq : LinearEquation) (k : ℕ) (hk : 1 ≤ k)
    (h : IsKPartitionRegular eq k) :
    ∃ x : ℕ → ℕ, eq.IsPositiveSolution x := by
  obtain ⟨N, hN⟩ := h
  -- Apply hN to the trivial constant-0 coloring.
  let χ : ℕ → ℕ := fun _ => 0
  have hχk : IsKColoring N k χ := by
    intro i _ _
    exact hk
  obtain ⟨x, _, hpos, _⟩ := hN χ hχk
  exact ⟨x, hpos⟩

/--
  **Monotonicity of `IsKPartitionRegularAt` in k**.

  If equation `eq` is k'-partition-regular at bound N (i.e., every k'-coloring
  of [1, N] forces a mono solution), then for any smaller k ≤ k', it is also
  k-partition-regular at N.

  Reason: a k-coloring is also a k'-coloring (taking values in [0, k) ⊆ [0, k')).
  Apply hypothesis to the same coloring.

  Consequence: R_k(eq) ≤ R_{k'}(eq) for k ≤ k' (adding colors raises threshold).
-/
theorem isKPartitionRegularAt_mono_colors
    (eq : LinearEquation) (k k' N : ℕ) (hk : k ≤ k')
    (h : IsKPartitionRegularAt eq k' N) :
    IsKPartitionRegularAt eq k N := by
  intro χ hχk
  have hχk' : IsKColoring N k' χ := by
    intro i hi1 hiN
    exact lt_of_lt_of_le (hχk i hi1 hiN) hk
  exact h χ hχk'

/--
  **TRIVIAL LOWER BOUND R_k(b) ≥ b for b-adic equation**, derivable without
  any valuation theory (uses only the algebraic structure of x + b·y = b·z).

  Argument: any positive solution (x, y, z) to x + b·y = b·z satisfies
  x = b·(z - y) ≥ b (since z > y from positivity of x), so x ≥ b. Hence
  no positive solution exists in [1, b-1]^3, and the trivial coloring χ ≡ 0
  vacuously avoids mono solutions at level b - 1.

  Conclusion: for any b ≥ 2 and k ≥ 1, no k-coloring of [1, b-1] can be forced
  to have a mono solution — so R_k(bAdicEquation b) ≥ b.

  This complements the deeper valuation bound R_k(b) ≥ b^k (from `thm_lower`).
-/
theorem not_isKPartitionRegularAt_bAdicEquation_at_b_minus_one
    {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ¬ IsKPartitionRegularAt (bAdicEquation b) k (b - 1) := by
  intro hPR
  -- Use trivial coloring χ ≡ 0.
  let χ : ℕ → ℕ := fun _ => 0
  have hχk : IsKColoring (b - 1) k χ := fun _ _ _ => hk
  obtain ⟨f, hbound, hpos, _⟩ := hPR χ hχk
  -- hbound : ∀ i < numVars, f i ≤ b - 1.
  -- hpos.2 : eval f = 0, i.e., f 0 + b · f 1 = b · f 2 in ℤ.
  have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
  have hbnd0 : f 0 ≤ b - 1 := hbound 0 (by rw [hnv]; omega)
  have hbnd1 : f 1 ≤ b - 1 := hbound 1 (by rw [hnv]; omega)
  have hbnd2 : f 2 ≤ b - 1 := hbound 2 (by rw [hnv]; omega)
  have hf0_pos : 0 < f 0 := hpos.1 0 (by rw [hnv]; omega)
  have hf1_pos : 0 < f 1 := hpos.1 1 (by rw [hnv]; omega)
  have hf2_pos : 0 < f 2 := hpos.1 2 (by rw [hnv]; omega)
  -- eval f = 0 gives f 0 + b · f 1 = b · f 2 in ℤ.
  have heval := hpos.2
  have hZeq : (f 0 : ℤ) + (b : ℤ) * (f 1 : ℤ) = (b : ℤ) * (f 2 : ℤ) := by
    have h := heval
    unfold bAdicEquation LinearEquation.eval at h
    simp [List.zipIdx] at h
    omega
  -- Cast to ℕ: f 0 + b · f 1 = b · f 2.
  have hNeq : f 0 + b * f 1 = b * f 2 := by exact_mod_cast hZeq
  -- Show f 2 > f 1 (since f 0 > 0): hNeq says f 0 + b * f 1 = b * f 2.
  -- If f 2 ≤ f 1, then b * f 2 ≤ b * f 1, forcing f 0 ≤ 0, contradiction.
  have hbmul_le_iff : ∀ a c : ℕ, a ≤ c → b * a ≤ b * c :=
    fun a c h => Nat.mul_le_mul_left b h
  have hf21 : f 1 < f 2 := by
    by_contra hge
    have hge' : f 2 ≤ f 1 := Nat.le_of_not_lt hge
    have hbmul : b * f 2 ≤ b * f 1 := hbmul_le_iff (f 2) (f 1) hge'
    omega
  -- From f 2 ≥ f 1 + 1: b * f 2 ≥ b * (f 1 + 1) = b * f 1 + b.
  -- Combined with f 0 + b * f 1 = b * f 2: f 0 ≥ b. Contradicts f 0 ≤ b - 1.
  have hbmul_step : b * (f 1 + 1) ≤ b * f 2 :=
    hbmul_le_iff (f 1 + 1) (f 2) hf21
  have : b * (f 1 + 1) = b * f 1 + b := by ring
  omega

/--
  **Monotonicity of `IsKPartitionRegular` in k**: if eq is k'-partition-regular,
  it is also k-partition-regular for any k ≤ k'.

  Consequence: R_k(eq) ≤ R_{k'}(eq) for k ≤ k' (in particular, partition
  regularity at k = 1 follows from any positive partition regularity).
-/
theorem isKPartitionRegular_mono_colors
    (eq : LinearEquation) (k k' : ℕ) (hk : k ≤ k')
    (h : IsKPartitionRegular eq k') :
    IsKPartitionRegular eq k := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, isKPartitionRegularAt_mono_colors eq k k' N hk hN⟩

/--
  **Monotonicity of `HasMonoSolution` in N**: a mono solution at level N
  is also a mono solution at any level N' ≥ N (same witness works).

  Trivial structural lemma; useful for propagating mono solutions upward.
-/
theorem hasMonoSolution_mono
    (eq : LinearEquation) (N N' : ℕ) (χ : ℕ → ℕ) (hN : N ≤ N')
    (h : HasMonoSolution eq N χ) :
    HasMonoSolution eq N' χ := by
  obtain ⟨f, hbound, hpos, hcolor⟩ := h
  refine ⟨f, ?_, hpos, hcolor⟩
  intro i hi
  exact le_trans (hbound i hi) hN

/--
  **R_k(eq) ≤ R_{k+1}(eq)** explicitly: the Rado number is non-decreasing
  in the number of colors. Corollary of `isKPartitionRegularAt_mono_colors`.

  Statement: if eq has Rado number N_{k+1} for k+1 colors, then for k
  colors the Rado number N_k satisfies N_k ≤ N_{k+1}.

  In particular, the Rado threshold values form a non-decreasing sequence
  R_1(eq) ≤ R_2(eq) ≤ R_3(eq) ≤... whenever they exist.
-/
theorem isRadoNumber_le_succ_colors
    (eq : LinearEquation) (k N_k N_kk : ℕ)
    (h_k : IsRadoNumber eq k N_k)
    (h_kk : IsRadoNumber eq (k + 1) N_kk) :
    N_k ≤ N_kk := by
  by_contra hN_gt
  have hN_lt : N_kk < N_k := Nat.lt_of_not_le hN_gt
  have hMin_k : ¬ IsKPartitionRegularAt eq k N_kk := h_k.2 N_kk hN_lt
  have hPR_k : IsKPartitionRegularAt eq k N_kk :=
    isKPartitionRegularAt_mono_colors eq k (k + 1) N_kk (by omega) h_kk.1
  exact hMin_k hPR_k

/-! ### Multiples sub-coloring (foundational structural lemma).

  Key Mathlib-style lemma: for ANY LinearEquation eq, if χ is mono-free on
  [1, n], then the multiples sub-coloring χ_c(d) := χ(c·d) is mono-free
  on [1, n/c]. This is the structural backbone of the cascade machinery
  and of Pillar 3 reductions: it lets us recurse from level n to level
  n/c while preserving the mono-free property.

  Now stated at MAXIMAL GENERALITY (any LinearEquation, not just bAdicEquation)
  via the new `LinearEquation.eval_const_mul` linearity lemma.
-/

/--
  **Scaling preserves positive solution of bAdicEquation b** (specialization).
  Direct corollary of the general `LinearEquation.isPositiveSolution_const_mul`.
-/
theorem bAdicEquation_isPositiveSolution_scale
    {b : ℕ} (c : ℕ) (hc : 1 ≤ c) (f : ℕ → ℕ)
    (hf : (bAdicEquation b).IsPositiveSolution f) :
    (bAdicEquation b).IsPositiveSolution (fun i => c * f i) :=
  LinearEquation.isPositiveSolution_const_mul (bAdicEquation b) hc f hf

/--
  **Multiples sub-coloring is mono-free** for ANY LinearEquation eq.

  GENERAL version: works for arbitrary `LinearEquation eq` (not just
  `bAdicEquation b`). If χ is mono-free on [1, n] for eq, and c ≥ 1, then
  the c-multiples sub-coloring χ_c(d) := χ(c·d) is mono-free on [1, n/c]
  for the SAME eq.

  Proof: a mono solution of χ_c at level n/c lifts (via scaling by c) to
  a mono solution of χ at level c · (n/c) ≤ n, contradicting mono-freeness.
  Uses `LinearEquation.isPositiveSolution_const_mul` from eval linearity.

  KERNEL-PURE. Genuinely general (all homogeneous linear equations).
-/
theorem multiples_subcoloring_mono_free
    (eq : LinearEquation) {n : ℕ} (c : ℕ) (hc : 1 ≤ c) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution eq n χ) :
    ¬ HasMonoSolution eq (n / c) (fun d => χ (c * d)) := by
  intro ⟨f, hbound, hpos, hcolor⟩
  apply hNoMono
  refine ⟨fun i => c * f i, ?_, ?_, ?_⟩
  · -- c * f i ≤ c * (n/c) ≤ n.
    intro i hi
    have hfi : f i ≤ n / c := hbound i hi
    have hmul : c * f i ≤ c * (n / c) := Nat.mul_le_mul_left c hfi
    have hdiv : c * (n / c) ≤ n := Nat.mul_div_le n c
    exact le_trans hmul hdiv
  · -- IsPositiveSolution preserved by scaling (general eval linearity).
    exact LinearEquation.isPositiveSolution_const_mul eq hc f hpos
  · -- Colors all equal: χ(c * f i) = χ_c(f i) = χ_c(f j) = χ(c * f j).
    intro i j hi hj
    exact hcolor i j hi hj

/--
  **Specialization** to bAdicEquation b — kept for backward compatibility
  and citation convenience. Direct application of the general
  `multiples_subcoloring_mono_free`.
-/
theorem bAdicEquation_multiples_subcoloring_mono_free
    {b n : ℕ} (c : ℕ) (hc : 1 ≤ c) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ) :
    ¬ HasMonoSolution (bAdicEquation b) (n / c) (fun d => χ (c * d)) :=
  multiples_subcoloring_mono_free (bAdicEquation b) c hc χ hNoMono

/--
  **`IsKColoring` is preserved by multiples sub-coloring** (trivial structural
  lemma, complement to `bAdicEquation_multiples_subcoloring_mono_free`).

  If χ is k-coloring of [1, n] and c ≥ 1, then χ_c(d) := χ(c·d) is k-coloring
  of [1, n/c].
-/
theorem isKColoring_multiples_subcoloring
    {n k : ℕ} (c : ℕ) (hc : 1 ≤ c) (χ : ℕ → ℕ)
    (hχk : IsKColoring n k χ) :
    IsKColoring (n / c) k (fun d => χ (c * d)) := by
  intro d hd1 hdNc
  apply hχk
  · -- 1 ≤ c * d : both c and d are ≥ 1.
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by
      have hd_pos : 0 < d := hd1
      have hc_pos : 0 < c := hc
      have : 0 < c * d := Nat.mul_pos hc_pos hd_pos
      omega)
  · -- c * d ≤ c * (n / c) ≤ n.
    have hmul : c * d ≤ c * (n / c) := Nat.mul_le_mul_left c hdNc
    have hdiv : c * (n / c) ≤ n := Nat.mul_div_le n c
    exact le_trans hmul hdiv

/-! ### Self-loop structural constraint (toward Pillar 3 attack).

  The self-loop (b·m, (b-1)·m, b·m) is the canonical "diagonal" Rado triple
  for bAdicEquation b (with x = z). Avoidance gives χ((b-1)m) ≠ χ(b·m).

  This is the cleanest structural constraint usable in Pillar 3 attacks,
  forcing mono-free colorings to ALTERNATE colors at adjacent multiples.
-/

/--
  **Self-loop constraint for bAdicEquation b**: for any mono-free k-coloring χ
  of [1, n] for bAdicEquation b (b ≥ 2), and any m ≥ 1 with b·m ≤ n, we have
  χ((b-1)·m) ≠ χ(b·m).

  Proof: the triple (b·m, (b-1)·m, b·m) is a positive solution of bAdicEquation
  b (since b·m + b·(b-1)·m = b·b·m). Mono = χ(b·m) = χ((b-1)·m). Mono-freeness
  forces ≠.

  This gives an INFINITE FAMILY of color-inequality constraints from a single
  mono-free hypothesis, building toward Pillar 3 structural analysis.
-/
theorem bAdicEquation_self_loop_chi_diff
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (hbm : b * m ≤ n) :
    χ ((b - 1) * m) ≠ χ (b * m) := by
  intro hEq
  apply hNoMono
  -- Witness f : ℕ → ℕ with f 0 = b·m, f 1 = (b-1)·m, f 2 = b·m.
  refine ⟨fun i => if i = 0 then b * m else if i = 1 then (b - 1) * m else b * m, ?_, ?_, ?_⟩
  · -- All bounded by n.
    intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    have hb1m_le : (b - 1) * m ≤ b * m := by
      apply Nat.mul_le_mul_right; omega
    match i, hi with
    | 0, _ => simp; exact hbm
    | 1, _ => simp; omega
    | 2, _ => simp; exact hbm
  · refine ⟨?_, ?_⟩
    · -- All positive: b·m ≥ 2·1 = 2; (b-1)·m ≥ 1·1 = 1.
      intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      have hbm_pos : 0 < b * m := Nat.mul_pos (by omega) hm
      have hb1m_pos : 0 < (b - 1) * m := Nat.mul_pos (by omega) hm
      match i, hi with
      | 0, _ => show 0 < b * m; exact hbm_pos
      | 1, _ => show 0 < (b - 1) * m; exact hb1m_pos
      | 2, _ => show 0 < b * m; exact hbm_pos
    · -- eval = 0: b·m + b·(b-1)·m - b·(b·m) = 0.
      rw [eval_bAdicEquation]
      simp
      -- Need: b·m + b·(b-1)·m = b·(b·m), i.e., (b-1)·m + m = b·m / b·m = b·m.
      -- Cast to ℤ: (b·m : ℤ) + (b : ℤ)·((b-1)·m : ℤ) - (b : ℤ)·(b·m : ℤ) = 0.
      -- (b·m : ℤ) = b·m, (b-1)·m : ℕ = (b - 1)·m where b - 1 ≥ 1.
      -- LHS = (b : ℤ)·m + (b : ℤ)·(((b : ℤ) - 1)·m) - (b : ℤ)·((b : ℤ)·m)
      -- = (b : ℤ)·m·(1 + (b - 1) - b) = (b : ℤ)·m·0 = 0. ✓
      have hb1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
        push_cast
        have : 1 ≤ b := by omega
        omega
      rw [hb1]
      ring
  · -- Colors equal: f 0 = f 2 = b·m, f 1 = (b-1)·m. χ(b·m) = χ((b-1)·m) by hEq.
    intro i j hi hj
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi hj
    have hsym : χ (b * m) = χ ((b - 1) * m) := hEq.symm
    match i, hi, j, hj with
    | 0, _, 0, _ => simp
    | 0, _, 1, _ => simp; exact hsym
    | 0, _, 2, _ => simp
    | 1, _, 0, _ => simp; exact hEq
    | 1, _, 1, _ => simp
    | 1, _, 2, _ => simp; exact hEq
    | 2, _, 0, _ => simp
    | 2, _, 1, _ => simp; exact hsym
    | 2, _, 2, _ => simp

/-! ### Generalized canonical-triple structural constraint.

  The canonical-triple lemma `chi_constraint_canonical_triple_of_no_mono`
  (in Bridge.lean for compatibility with bAdicEquation specialization)
  also lives in pure General/ form here, allowing downstream Pillar 3
  attacks without circular imports.
-/

/--
  **Canonical-triple constraint (general form)**: for any mono-free k-coloring
  χ of [1, n] for bAdicEquation b (b ≥ 2), and any m ≥ 1 with b·m ≤ n and
  2·m ≤ n, the triple (b·m, m, 2·m) is positive Rado, so NOT all three
  colors equal.

  This is the GENERAL form (b·m, m, 2·m). The specific b=3 form is
  (3·m, m, 2·m) — a single constraint per m, complementing the self-loop
  constraint χ((b-1)·m) ≠ χ(b·m).

  KERNEL-PURE proof.
-/
theorem bAdicEquation_canonical_triple_constraint
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (hbm : b * m ≤ n) (h2m : 2 * m ≤ n) :
    ¬ (χ (b * m) = χ m ∧ χ m = χ (2 * m)) := by
  intro ⟨h_bm_m, h_m_2m⟩
  apply hNoMono
  refine ⟨fun i => if i = 0 then b * m else if i = 1 then m else 2 * m, ?_, ?_, ?_⟩
  · intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    match i, hi with
    | 0, _ => show b * m ≤ n; exact hbm
    | 1, _ => show m ≤ n; omega
    | 2, _ => show 2 * m ≤ n; exact h2m
  · refine ⟨?_, ?_⟩
    · intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      have hbm_pos : 0 < b * m := Nat.mul_pos (by omega) hm
      have h2m_pos : 0 < 2 * m := Nat.mul_pos (by omega) hm
      match i, hi with
      | 0, _ => show 0 < b * m; exact hbm_pos
      | 1, _ => show 0 < m; exact hm
      | 2, _ => show 0 < 2 * m; exact h2m_pos
    · rw [eval_bAdicEquation]
      simp
      ring
  · intro i j hi hj
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi hj
    have h_bm_2m : χ (b * m) = χ (2 * m) := h_bm_m.trans h_m_2m
    match i, hi, j, hj with
    | 0, _, 0, _ => simp
    | 0, _, 1, _ => simp; exact h_bm_m
    | 0, _, 2, _ => simp; exact h_bm_2m
    | 1, _, 0, _ => simp; exact h_bm_m.symm
    | 1, _, 1, _ => simp
    | 1, _, 2, _ => simp; exact h_m_2m
    | 2, _, 0, _ => simp; exact h_bm_2m.symm
    | 2, _, 1, _ => simp; exact h_m_2m.symm
    | 2, _, 2, _ => simp

/--
  **Conditional alternation**: if χ(b·m) = χ(m) (canonical triple's
  first-third equality), then χ(2·m) ≠ χ(m).

  Direct corollary of `bAdicEquation_canonical_triple_constraint`:
  NOT (chi(b·m) = chi(m) AND chi(m) = chi(2·m)) gives the conditional
  inequality.

  Use case: in a Pillar 3 argument, given chi(3m) = chi(m), forces
  chi(2m) ≠ chi(m), restricting chi(2m) to a smaller color set.
-/
theorem bAdicEquation_canonical_triple_conditional_alternation
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (hbm : b * m ≤ n) (h2m : 2 * m ≤ n)
    (hEq : χ (b * m) = χ m) :
    χ (2 * m) ≠ χ m := by
  intro h_m_2m
  have h := bAdicEquation_canonical_triple_constraint hb χ hNoMono hm hbm h2m
  exact h ⟨hEq, h_m_2m.symm⟩

/--
  **Multiples sub-coloring BUNDLED**: for ANY LinearEquation eq, mono-free
  k-coloring chi of [1, n], and any c ≥ 1, the c-multiples sub-coloring
  is BOTH a k-coloring of [1, n/c] AND mono-free for eq at [1, n/c].

  Bundle of `isKColoring_multiples_subcoloring` + `multiples_subcoloring_mono_free`.
  Single hypothesis form for cascade-step applications.
-/
theorem multiples_subcoloring_bundled
    (eq : LinearEquation) {n k : ℕ} (c : ℕ) (hc : 1 ≤ c) (χ : ℕ → ℕ)
    (hKcol : IsKColoring n k χ)
    (hNoMono : ¬ HasMonoSolution eq n χ) :
    IsKColoring (n / c) k (fun d => χ (c * d)) ∧
    ¬ HasMonoSolution eq (n / c) (fun d => χ (c * d)) :=
  ⟨isKColoring_multiples_subcoloring c hc χ hKcol,
   multiples_subcoloring_mono_free eq c hc χ hNoMono⟩

/-! ### Iterated multiples sub-coloring (Pillar 3 cascade structure).

  By iterating `multiples_subcoloring_mono_free`, mono-free chi at level n
  for bAdicEquation b yields mono-free sub-colorings at all scales
  n/b, n/b², n/b³,...

  This is the FOUNDATIONAL recursion underlying the cascade machinery.
-/

/--
  **Iterated multiples sub-coloring** for bAdicEquation b: the c·c-fold
  multiples sub-coloring chi_{c²}(d) := chi(c²·d) is mono-free on [1, n/c²].

  Direct corollary of applying `multiples_subcoloring_mono_free` TWICE
  (once at scale c, then again at scale c on the result).
-/
theorem multiples_subcoloring_mono_free_iter
    (eq : LinearEquation) {n : ℕ} (c : ℕ) (hc : 1 ≤ c) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution eq n χ) :
    ¬ HasMonoSolution eq (n / c / c) (fun d => χ (c * (c * d))) := by
  -- First application: chi_c(d) := chi(c·d) mono-free on [1, n/c].
  have h1 := multiples_subcoloring_mono_free eq c hc χ hNoMono
  -- Second application: chi_c'(d) := chi_c(c·d) = chi(c·(c·d)) mono-free on [1, n/c/c].
  exact multiples_subcoloring_mono_free eq c hc (fun d => χ (c * d)) h1

/--
  **Iterated b-fold multiples sub-coloring**: for mono-free chi at level
  b^k - 1 for bAdicEquation b, the b^j-fold sub-coloring is mono-free at
  level (b^k - 1) / b^j ≈ b^(k-j) for any 0 ≤ j ≤ k.

  This is the recursive descent structure underlying the cascade proof.
  Combined with the inductive hypothesis R_{k-1}(b) ≤ b^{k-1}, this gives
  the compression-style argument at each level.

  (Specialized to single iteration for clarity; the j-fold version follows
  by induction.)
-/
theorem bAdicEquation_iter_multiples_subcoloring
    {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ) :
    ¬ HasMonoSolution (bAdicEquation b) (n / b / b) (fun d => χ (b * (b * d))) :=
  multiples_subcoloring_mono_free_iter (bAdicEquation b) b (by omega) χ hNoMono

/-! ### Specialized b=3 constraint chains (for Pillar 3 attack).

  Direct application of the self-loop constraint at b = 3 yields the
  9-step color-inequality chain chi(2m) ≠ chi(3m) for m ∈ [1, 9],
  which is the foundational data for Pillar 3 analysis.
-/

/--
  **For mono-free 3-coloring of [1, 27] for bAdicEquation 3**:
  the self-loop gives χ(2·m) ≠ χ(3·m) for any m with 3·m ≤ 27, i.e.,
  m ∈ [1, 9]. Specializes `bAdicEquation_self_loop_chi_diff` to b = 3.
-/
theorem bAdicEquation_3_self_loop_chain
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {m : ℕ} (hm : 1 ≤ m) (h3m : 3 * m ≤ n) :
    χ (2 * m) ≠ χ (3 * m) := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono hm h3m
  -- h : χ ((3 - 1) * m) ≠ χ (3 * m). Simplify (3 - 1) = 2.
  have h32 : (3 - 1 : ℕ) = 2 := by decide
  rw [h32] at h
  exact h

/--
  **For mono-free 3-coloring of [1, 27] for bAdicEquation 3 with chi(1) = 0**:
  combining (3, 1, 2) canonical triple + chi(1) = 0 + self-loop chi(2) ≠ chi(3)
  forces a structural constraint.

  Specifically: chi(3) = 0 → chi(2) ∈ {1, 2} AND chi(2) ≠ chi(3) ✓ (trivially).
  But also from (3, 1, 2): NOT (chi(3) = chi(1) AND chi(1) = chi(2)), i.e.,
  NOT (chi(3) = 0 AND chi(2) = 0). Substituting chi(1) = 0: this just says
  NOT (chi(3) = 0 = chi(2)) — already implied by chi(2) ≠ chi(3) when
  chi(3) = 0.

  CLEAN CONCLUSION: under chi(1) = 0, no NEW constraint from (3, 1, 2)
  beyond the self-loop chi(2) ≠ chi(3). The canonical triple becomes
  equivalent to the self-loop in this base case.
-/
theorem bAdicEquation_3_base_chi_constraint
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3 : 3 ≤ n) :
    χ 2 ≠ χ 3 := by
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 1) (by omega) (by omega)
  simpa using h

/--
  **Canonical triple (3, 1, 2) forbidden mono**: for mono-free k-coloring chi
  of [1, n] for bAdicEquation 3 (n ≥ 3), NOT all of χ(1), χ(2), χ(3) are equal.

  This is the canonical (b·m, m, 2·m) constraint at b=3, m=1: (3, 1, 2)
  Rado triple. Crucial Pillar 3 building block.

  Specifically: chi(1) = chi(2) = chi(3) is impossible for mono-free chi.
  This eliminates one structural configuration immediately.
-/
theorem bAdicEquation_3_chi_1_2_3_not_all_equal
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3 : 3 ≤ n) :
    ¬ (χ 1 = χ 2 ∧ χ 2 = χ 3) := by
  -- Apply canonical_triple_constraint (b=3, m=1): NOT (χ(3·1) = χ(1) AND χ(1) = χ(2·1)).
  have h := bAdicEquation_canonical_triple_constraint (b := 3) (n := n) (by omega) χ
    hNoMono (m := 1) (by omega) (by omega) (by omega)
  -- h : ¬ (χ (3 * 1) = χ 1 ∧ χ 1 = χ (2 * 1)). Simplify: ¬ (χ 3 = χ 1 ∧ χ 1 = χ 2).
  intro ⟨h12, h23⟩
  apply h
  refine ⟨?_, ?_⟩
  · -- Need χ (3 * 1) = χ 1, i.e., χ 3 = χ 1. We have χ 1 = χ 2 = χ 3 so χ 3 = χ 1.
    show χ 3 = χ 1
    exact (h12.trans h23).symm
  · -- Need χ 1 = χ (2 * 1), i.e., χ 1 = χ 2. Have it.
    show χ 1 = χ 2
    exact h12

/--
  **Forced inequality**: for mono-free 3-coloring chi of [1, 27] for
  bAdicEquation 3 with chi(1) = 0 AND chi(2) = 0, we have chi(3) ≠ 0.

  Direct corollary of `bAdicEquation_3_chi_1_2_3_not_all_equal`:
  if chi(1) = chi(2) = 0, then χ(3) = 0 would give χ(1) = χ(2) = χ(3) = 0,
  forbidden by the (3, 1, 2) Rado triple.

  This is the first concrete chi-value constraint in the Pillar 3
  WLOG chi(1) = chi(2) = 0 sub-case analysis.
-/
theorem bAdicEquation_3_chi_3_ne_zero_when_chi_1_2_eq_zero
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3 : 3 ≤ n)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) :
    χ 3 ≠ 0 := by
  intro h3_zero
  have h := bAdicEquation_3_chi_1_2_3_not_all_equal χ hNoMono h3
  apply h
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
  · rw [h2, h3_zero]

/-! ### Second self-loop family (x = y form).

  Besides the (x = z) self-loop (b·m, (b-1)·m, b·m), there's the (x = y)
  self-loop (b·m, b·m, (b+1)·m). For bAdicEquation b: b·m + b·b·m = b·(b+1)·m ✓.

  This gives a DIFFERENT family of color-inequality constraints
  χ(b·m) ≠ χ((b+1)·m), orthogonal to the (x = z) self-loop.

  Both families together greatly restrict mono-free colorings.
-/

/--
  **Second self-loop constraint** for bAdicEquation b: for mono-free
  k-coloring χ of [1, n] for bAdicEquation b (b ≥ 2), and any m ≥ 1
  with (b+1)·m ≤ n, we have χ(b·m) ≠ χ((b+1)·m).

  Proof: the triple (b·m, b·m, (b+1)·m) satisfies b·m + b·b·m = b·(b+1)·m
  (positive Rado solution). Mono = χ(b·m) = χ((b+1)·m). Avoidance.

  For b = 3, m = 1: χ(3) ≠ χ(4) (= the missing constraint that, combined
  with χ(2) ≠ χ(3) and the canonical-triple constraints, characterizes
  the mono-free 3-coloring structure on small initial segments).
-/
theorem bAdicEquation_self_loop_xy_chi_diff
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (h_bp1m : (b + 1) * m ≤ n) :
    χ (b * m) ≠ χ ((b + 1) * m) := by
  intro hEq
  apply hNoMono
  -- Witness f : ℕ → ℕ with f 0 = b·m, f 1 = b·m, f 2 = (b+1)·m.
  refine ⟨fun i => if i = 0 then b * m else if i = 1 then b * m else (b + 1) * m, ?_, ?_, ?_⟩
  · -- All bounded by n. (b·m ≤ (b+1)·m ≤ n.)
    intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    have hbm_le : b * m ≤ (b + 1) * m := by
      apply Nat.mul_le_mul_right; omega
    match i, hi with
    | 0, _ => show b * m ≤ n; omega
    | 1, _ => show b * m ≤ n; omega
    | 2, _ => show (b + 1) * m ≤ n; exact h_bp1m
  · refine ⟨?_, ?_⟩
    · -- All positive.
      intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      have hbm_pos : 0 < b * m := Nat.mul_pos (by omega) hm
      have hbp1m_pos : 0 < (b + 1) * m := Nat.mul_pos (by omega) hm
      match i, hi with
      | 0, _ => show 0 < b * m; exact hbm_pos
      | 1, _ => show 0 < b * m; exact hbm_pos
      | 2, _ => show 0 < (b + 1) * m; exact hbp1m_pos
    · -- eval = 0: b·m + b·(b·m) - b·((b+1)·m) = b·m + b²·m - b·(b+1)·m
      -- = b·m·(1 + b - (b+1)) = b·m·0 = 0. ✓
      rw [eval_bAdicEquation]
      simp
      push_cast
      ring
  · -- Colors equal: chi(b·m) = chi((b+1)·m) by hEq (and chi(b·m) = chi(b·m)).
    intro i j hi hj
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi hj
    match i, hi, j, hj with
    | 0, _, 0, _ => simp
    | 0, _, 1, _ => simp
    | 0, _, 2, _ => simp; exact hEq
    | 1, _, 0, _ => simp
    | 1, _, 1, _ => simp
    | 1, _, 2, _ => simp; exact hEq
    | 2, _, 0, _ => simp; exact hEq.symm
    | 2, _, 1, _ => simp; exact hEq.symm
    | 2, _, 2, _ => simp

/--
  **For mono-free 3-coloring of [1, 27] for bAdicEquation 3**:
  the (x = y) self-loop gives χ(3·m) ≠ χ(4·m) for any m with 4·m ≤ n,
  i.e., m ∈ [1, n/4]. Specializes `bAdicEquation_self_loop_xy_chi_diff`
  to b = 3.
-/
theorem bAdicEquation_3_self_loop_xy_chain
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {m : ℕ} (hm : 1 ≤ m) (h4m : 4 * m ≤ n) :
    χ (3 * m) ≠ χ (4 * m) := by
  have h := bAdicEquation_self_loop_xy_chi_diff (b := 3) (by omega) χ hNoMono hm
    (by show (3 + 1) * m ≤ n; convert h4m using 1)
  -- h : χ (3 * m) ≠ χ ((3 + 1) * m). Need: χ (3 * m) ≠ χ (4 * m).
  have h31 : (3 + 1 : ℕ) = 4 := by decide
  rw [h31] at h
  exact h

/-! ### CompressionHyp 3 2 derived FROM SCRATCH (no project bridge).

  Demonstration that the General/ framework's structural lemmas are
  SUFFICIENT to prove the base-level compression hypothesis at b=3, k=2
  without relying on the project's analytic proof or any SAT axiom.

  This validates the structural approach: the same machinery, applied at
  higher k, would give CompressionHyp 3 3, etc. (Higher k requires
  ITERATIVE application of these lemmas — multi-month structural work.)
-/

/--
  **CompressionHyp 3 2 from structural lemmas** (Mathlib-style proof,
  no project bridge).

  For any mono-free 2-coloring χ of [1, 8] for bAdicEquation 3, we have
  χ(3) = χ(6) (so c₀ = 1 - χ(3) is omitted at both multiples-of-3).

  Proof chain (all kernel-pure from new structural lemmas):
  1. Self-loop (3, 2, 3) at m = 1: χ(2) ≠ χ(3). [self_loop_chi_diff]
  2. Self-loop (3, 3, 4) at m = 1: χ(3) ≠ χ(4). [self_loop_xy_chi_diff]
  3. With 2 colors: from (1) and (2), χ(2) = χ(4) = 1 - χ(3).
  4. Canonical triple (6, 2, 4): NOT (χ(6) = χ(2) AND χ(2) = χ(4)).
     Given χ(2) = χ(4), get χ(6) ≠ χ(2). [canonical_triple_constraint]
  5. With 2 colors: χ(6) ≠ χ(2) = 1 - χ(3) ⇒ χ(6) = χ(3). ✓

  This gives an in-General-framework derivation of the project's
  compression_hyp_k2 at b = 3, fully kernel-pure.

  KERNEL-PURE.
-/
theorem compressionHyp_3_2_from_scratch
    {n : ℕ} (h_n : 8 ≤ n) (χ : ℕ → ℕ)
    (hχk : IsKColoring n 2 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 3 = χ 6 := by
  -- Step 1: χ(2) ≠ χ(3) (self-loop (3, 2, 3)).
  have h23 : χ 2 ≠ χ 3 := bAdicEquation_3_base_chi_constraint χ hNoMono (by omega)
  -- Step 2: χ(3) ≠ χ(4) (self-loop (3, 3, 4)).
  have h34 : χ 3 ≠ χ 4 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 1) (by omega) (by omega)
    simpa using h
  -- Color values bounded by 2.
  have hχ2 : χ 2 < 2 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 2 := hχk 3 (by omega) (by omega)
  have hχ4 : χ 4 < 2 := hχk 4 (by omega) (by omega)
  have hχ6 : χ 6 < 2 := hχk 6 (by omega) (by omega)
  -- Step 3: with 2 colors, χ(2) ≠ χ(3) and χ(3) ≠ χ(4) ⇒ χ(2) = χ(4).
  have h24 : χ 2 = χ 4 := by
    interval_cases (χ 3) <;> omega
  -- Step 4: canonical triple (6, 2, 4) at m = 2.
  have hCanon := bAdicEquation_canonical_triple_constraint
    (b := 3) (n := n) (show (2 : ℕ) ≤ 3 by omega) χ hNoMono
    (m := 2) (by omega) (by show 3 * 2 ≤ n; omega) (by show 2 * 2 ≤ n; omega)
  have h6_eq : (3 : ℕ) * 2 = 6 := by decide
  have h4_eq : (2 : ℕ) * 2 = 4 := by decide
  rw [h6_eq, h4_eq] at hCanon
  have h62 : χ 6 ≠ χ 2 := fun hEq => hCanon ⟨hEq, h24⟩
  -- Step 5: With 2 colors {0, 1}, χ(2) ≠ χ(3) and χ(2) ≠ χ(6) ⇒ χ(3) = χ(6).
  -- Need to feed omega all the constraints. Use interval_cases on χ(2).
  interval_cases (χ 2) <;> omega

/-! ### GENERAL 2-parameter Rado triple constraint.

  Every positive Rado triple (x, y, z) for bAdicEquation b has the form
  (b·d, y, y+d) for some d, y ≥ 1 (since x = b·(z-y), set d = z-y).

  This is a 2-PARAMETER family generalizing both the canonical triple
  (d, y) = (d, d) giving (bd, d, 2d), and the (6, 1, 3) = (3·2, 1, 3)
  triple for d = 2, y = 1, etc.

  Mono-freeness gives NOT (χ(bd) = χ(y) AND χ(y) = χ(y+d)) for each
  valid (d, y) pair — a much richer constraint family.
-/

/--
  **General 2-parameter Rado triple constraint** for bAdicEquation b:
  for any d, y ≥ 1 with b·d ≤ n AND y + d ≤ n, the positive Rado triple
  (b·d, y, y + d) satisfies mono-freeness, so NOT all three colors equal.

  Subsumes:
  - canonical triple (y = d): (b·d, d, 2·d).
  - other triples like (6, 1, 3) = (3·2, 1, 3) for b = 3, d = 2, y = 1.

  Maximally general single-coordinate Rado constraint for bAdicEquation b.
-/
theorem bAdicEquation_general_rado_constraint
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {d y : ℕ} (hd : 1 ≤ d) (hy : 1 ≤ y) (hbd : b * d ≤ n) (hyd : y + d ≤ n) :
    ¬ (χ (b * d) = χ y ∧ χ y = χ (y + d)) := by
  intro ⟨h_bd_y, h_y_yd⟩
  apply hNoMono
  refine ⟨fun i => if i = 0 then b * d else if i = 1 then y else y + d, ?_, ?_, ?_⟩
  · intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    match i, hi with
    | 0, _ => show b * d ≤ n; exact hbd
    | 1, _ => show y ≤ n; omega
    | 2, _ => show y + d ≤ n; exact hyd
  · refine ⟨?_, ?_⟩
    · intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      have hbd_pos : 0 < b * d := Nat.mul_pos (by omega) hd
      match i, hi with
      | 0, _ => show 0 < b * d; exact hbd_pos
      | 1, _ => show 0 < y; exact hy
      | 2, _ => show 0 < y + d; omega
    · rw [eval_bAdicEquation]
      simp
      push_cast
      ring
  · intro i j hi hj
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi hj
    have h_bd_yd : χ (b * d) = χ (y + d) := h_bd_y.trans h_y_yd
    match i, hi, j, hj with
    | 0, _, 0, _ => simp
    | 0, _, 1, _ => simp; exact h_bd_y
    | 0, _, 2, _ => simp; exact h_bd_yd
    | 1, _, 0, _ => simp; exact h_bd_y.symm
    | 1, _, 1, _ => simp
    | 1, _, 2, _ => simp; exact h_y_yd
    | 2, _, 0, _ => simp; exact h_bd_yd.symm
    | 2, _, 1, _ => simp; exact h_y_yd.symm
    | 2, _, 2, _ => simp

/-! ### Color class definitions and basic counting infrastructure.

  For chi : ℕ → ℕ a k-coloring of [1, n], the COLOR CLASSES partition
  [1, n] into k subsets. Pigeonhole then gives that at least one class
  has size ≥ ⌈n/k⌉.

  This is the algebraic/combinatorial backbone for Schur-style counting
  arguments in Pillar 3 (= compression hypothesis analyses).
-/

/--
  **Color class** for color c in [1, n] under coloring χ.
  Returns the Finset of indices i ∈ [1, n] with χ(i) = c.
-/
def colorClass (n c : ℕ) (χ : ℕ → ℕ) : Finset ℕ :=
  (Finset.Ico 1 (n + 1)).filter (fun i => χ i = c)

/--
  **Color class is a sub-Finset of [1, n+1)** (trivial structural property).
-/
theorem colorClass_subset (n c : ℕ) (χ : ℕ → ℕ) :
    colorClass n c χ ⊆ Finset.Ico 1 (n + 1) := by
  unfold colorClass
  exact Finset.filter_subset _ _

/--
  **Membership in color class**: i ∈ colorClass n c χ iff 1 ≤ i ≤ n ∧ χ(i) = c.
-/
@[simp]
theorem mem_colorClass (n c i : ℕ) (χ : ℕ → ℕ) :
    i ∈ colorClass n c χ ↔ 1 ≤ i ∧ i ≤ n ∧ χ i = c := by
  unfold colorClass
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

/--
  **Color classes partition [1, n]**: for any k-coloring χ of [1, n],
  the sum of color class cardinalities equals n.

  ∑ c < k, |colorClass n c χ| = n
-/
theorem sum_colorClass_card (n k : ℕ) (χ : ℕ → ℕ) (hχ : IsKColoring n k χ) :
    (Finset.range k).sum (fun c => (colorClass n c χ).card) = n := by
  -- biUnion of color classes = Ico 1 (n+1).
  have hbiU : (Finset.range k).biUnion (fun c => colorClass n c χ) = Finset.Ico 1 (n + 1) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, mem_colorClass, Finset.mem_Ico]
    constructor
    · rintro ⟨c, _, h1, h2, _⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      have hin : i ≤ n := by omega
      refine ⟨χ i, hχ i h1 hin, h1, hin, rfl⟩
  -- Disjointness of color classes for different c.
  have hdisj : ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k, a ≠ b →
      Disjoint (colorClass n a χ) (colorClass n b χ) := by
    intro a _ b _ hab
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [mem_colorClass] at hx hy
    subst hxy
    exact hab (hx.2.2.symm.trans hy.2.2)
  -- Sum of cards = card of biUnion (by disjointness) = card of Ico = n.
  rw [← Finset.card_biUnion hdisj, hbiU, Nat.card_Ico]
  omega

/--
  **PIGEONHOLE for color classes** (basic form): for any k-coloring χ of [1, n],
  if k * (m - 1) < n then some color class has card ≥ m.

  Equivalent contrapositive: if all classes have card < m, then sum ≤ k*(m-1) < n,
  contradicting sum = n.
-/
theorem colorClass_pigeonhole (n k m : ℕ) (χ : ℕ → ℕ)
    (hχ : IsKColoring n k χ) (hkm : k * (m - 1) < n) :
    ∃ c ∈ Finset.range k, m ≤ (colorClass n c χ).card := by
  by_contra h
  push_neg at h
  have hsum := sum_colorClass_card n k χ hχ
  have hbound : (Finset.range k).sum (fun c => (colorClass n c χ).card) ≤
                (Finset.range k).sum (fun _ => m - 1) := by
    apply Finset.sum_le_sum
    intro c hc
    have := h c hc
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  rw [hsum] at hbound
  -- n ≤ k * (m - 1) < n. Contradiction.
  omega

/--
  **Ceiling form of color pigeonhole**: ∃ c, (colorClass n c χ).card ≥ ⌈n/k⌉.

  Standard form for Schur-style counting arguments.
  Requires k ≥ 1 (need at least one color class) and n ≥ 1.
-/
theorem colorClass_pigeonhole_ceil (n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (χ : ℕ → ℕ) (hχ : IsKColoring n k χ) :
    ∃ c ∈ Finset.range k, (n + k - 1) / k ≤ (colorClass n c χ).card := by
  apply colorClass_pigeonhole n k ((n + k - 1) / k) χ hχ
  -- Need: k * ((n + k - 1) / k - 1) < n.
  -- (n + k - 1)/k = ⌈n/k⌉. For n ≥ 1, ⌈n/k⌉ ≥ 1.
  -- k * (⌈n/k⌉ - 1) < n always (the standard ceiling property).
  -- Direct computation: ⌈n/k⌉ = (n+k-1)/k. k * ((n+k-1)/k - 1).
  -- Use Nat.div with division algorithm: (n+k-1) = k * ((n+k-1)/k) + r where 0 ≤ r < k.
  -- So k * ((n+k-1)/k) = n + k - 1 - r ≤ n + k - 1.
  -- k * ((n+k-1)/k - 1) = k * ((n+k-1)/k) - k = n + k - 1 - r - k = n - 1 - r < n (since r ≥ 0).
  -- Always strictly less than n.
  have hge1 : 1 ≤ (n + k - 1) / k := by
    apply (Nat.one_le_div_iff hk).mpr
    omega
  have hkdiv : k * ((n + k - 1) / k) ≤ n + k - 1 := by
    have := Nat.div_mul_le_self (n + k - 1) k
    linarith [Nat.mul_comm k ((n + k - 1) / k)]
  have hsubeq : k * ((n + k - 1) / k - 1) = k * ((n + k - 1) / k) - k := by
    have hge1' : (n + k - 1) / k ≥ 1 := hge1
    cases hN : (n + k - 1) / k with
    | zero => omega
    | succ m' => simp [Nat.mul_succ]
  rw [hsubeq]
  -- k * ((n+k-1)/k) - k ≤ n + k - 1 - k = n - 1 < n.
  omega

/-! ### Color permutation invariance (WLOG infrastructure).

  For any LinearEquation eq, the property "mono-free k-coloring" is
  invariant under PERMUTATION of color labels. This lets us assume
  WLOG specific color assignments (e.g., χ(1) = 0) without loss of
  generality.

  Key Mathlib-style lemma: `mono_free_pi_invariant`.
-/

/--
  **HasMonoSolution is invariant under color permutation**.

  Let π : ℕ → ℕ be a bijection (or any injection on the color range of χ).
  Then `HasMonoSolution eq n χ ↔ HasMonoSolution eq n (π ∘ χ)`.

  Direction (→): if χ has mono solution (x_i) with χ(x_i) all equal to c,
  then π ∘ χ has mono solution with (π ∘ χ)(x_i) = π(c) all equal.

  Direction (←): conversely, π ∘ χ has mono ⇒ χ has mono (since π is injective).
-/
theorem hasMonoSolution_comp_inj
    (eq : LinearEquation) (n : ℕ) (χ : ℕ → ℕ) (π : ℕ → ℕ)
    (hπ : Function.Injective π) :
    HasMonoSolution eq n (π ∘ χ) ↔ HasMonoSolution eq n χ := by
  constructor
  · rintro ⟨f, hbound, hpos, hcolor⟩
    refine ⟨f, hbound, hpos, ?_⟩
    intro i j hi hj
    have h_pi_eq : (π ∘ χ) (f i) = (π ∘ χ) (f j) := hcolor i j hi hj
    exact hπ h_pi_eq
  · rintro ⟨f, hbound, hpos, hcolor⟩
    refine ⟨f, hbound, hpos, ?_⟩
    intro i j hi hj
    show π (χ (f i)) = π (χ (f j))
    rw [hcolor i j hi hj]

/--
  **HasMonoSolution invariant under arbitrary bijection on colors**.

  More general formulation: if π : ℕ → ℕ is a bijection (≃), then χ has
  mono iff π ∘ χ has mono.

  Direct corollary of `hasMonoSolution_comp_inj` (using Equiv injectivity).
-/
theorem hasMonoSolution_comp_equiv
    (eq : LinearEquation) (n : ℕ) (χ : ℕ → ℕ) (π : ℕ ≃ ℕ) :
    HasMonoSolution eq n ((π : ℕ → ℕ) ∘ χ) ↔ HasMonoSolution eq n χ :=
  hasMonoSolution_comp_inj eq n χ π π.injective

/--
  **IsKColoring is preserved by permutation** (if π maps [0, k) to [0, k)).

  If χ is k-coloring of [1, n] and π : ℕ → ℕ satisfies π(c) < k whenever
  c < k, then π ∘ χ is also k-coloring of [1, n].
-/
theorem isKColoring_comp
    (n k : ℕ) (χ : ℕ → ℕ) (π : ℕ → ℕ)
    (hπ : ∀ c, c < k → π c < k)
    (hχ : IsKColoring n k χ) :
    IsKColoring n k (π ∘ χ) := by
  intro i hi1 hin
  exact hπ (χ i) (hχ i hi1 hin)

/--
  **Mono-free k-coloring permutation invariance**: combining
  `hasMonoSolution_comp_inj` with `isKColoring_comp`.

  If χ is mono-free k-coloring of [1, n] for eq AND π : ℕ → ℕ is an injection
  with π(c) < k whenever c < k, then π ∘ χ is also mono-free k-coloring of
  [1, n] for the SAME eq.

  Use case: WLOG chi(1) = 0 reductions. Given chi(1) = c₀, the swap-with-0
  permutation gives an equivalent mono-free coloring with chi(1) = 0.
-/
theorem mono_free_coloring_comp_inj
    (eq : LinearEquation) (n k : ℕ) (χ : ℕ → ℕ) (π : ℕ → ℕ)
    (hπinj : Function.Injective π)
    (hπcol : ∀ c, c < k → π c < k)
    (hKcol : IsKColoring n k χ)
    (hNoMono : ¬ HasMonoSolution eq n χ) :
    IsKColoring n k (π ∘ χ) ∧ ¬ HasMonoSolution eq n (π ∘ χ) := by
  refine ⟨isKColoring_comp n k χ π hπcol hKcol, ?_⟩
  intro hMono
  exact hNoMono ((hasMonoSolution_comp_inj eq n χ π hπinj).mp hMono)

/-! ### Cascade-step structural reduction (general LinearEquation).

  KEY MATHLIB INFRA: for any LinearEquation eq, the inductive hypothesis
  "R_{k-1}(eq) ≤ N_{k-1}" combined with multiples sub-coloring gives a
  CONSTRAINT on mono-free k-colorings at any level N.

  Specifically: chi mono-free k-coloring at N implies chi' (= c-multiples
  sub-coloring on [1, N/c]) is mono-free for eq. If chi' uses ≤ (k-1) colors,
  applying R_{k-1}(eq) bound at [1, N/c] could force mono. The COMPRESSION
  question is whether chi' is FORCED to use ≤ (k-1) colors — this is what
  CompressionHyp asks at each level.
-/

/--
  **Cascade step bridge** (general framework): combining multiples sub-coloring
  with inductive partition-regularity hypothesis.

  Statement: If multiples sub-coloring chi' is k'-partition-regular at level
  N/c (i.e., every k'-coloring of [1, N/c] forces mono), AND chi uses only k'
  colors at multiples (i.e., chi' is a k'-coloring), then chi at level N has
  a mono solution (lifted from chi' via scaling).

  This is the SINGLE-STEP cascade reduction in pure General/ form. Applied
  inductively, it gives the full cascade architecture: if R_{k-1} ≤ N_{k-1}
  AND each chi at level N_k has chi' as (k-1)-coloring at level N_k/c, then
  R_k ≤ N_k.

  KERNEL-PURE.
-/
theorem cascade_step_general
    (eq : LinearEquation) {N : ℕ} (c : ℕ) (hc : 1 ≤ c) (k' : ℕ) (χ : ℕ → ℕ)
    (hχ' : IsKColoring (N / c) k' (fun d => χ (c * d)))
    (hPR : IsKPartitionRegularAt eq k' (N / c)) :
    HasMonoSolution eq N χ := by
  -- Apply hPR to chi' to get mono at level N/c.
  obtain ⟨f, hbound, hpos, hcolor⟩ := hPR (fun d => χ (c * d)) hχ'
  -- Lift mono to level N via scaling f → c · f.
  refine ⟨fun i => c * f i, ?_, ?_, ?_⟩
  · intro i hi
    have hfi : f i ≤ N / c := hbound i hi
    have hmul : c * f i ≤ c * (N / c) := Nat.mul_le_mul_left c hfi
    have hdiv : c * (N / c) ≤ N := Nat.mul_div_le N c
    exact le_trans hmul hdiv
  · exact LinearEquation.isPositiveSolution_const_mul eq hc f hpos
  · intro i j hi hj
    exact hcolor i j hi hj

/--
  **Cascade step contrapositive**: if chi mono-free at N for eq, and chi'
  (= c-multiples) uses only k' colors, then ¬ IsKPartitionRegularAt eq k' (N/c).

  This is the STRUCTURAL OBSTRUCTION the cascade chases: showing that chi'
  uses ≤ (k-1) colors (compression) forces N/c < R_{k-1}(eq), i.e., a bound
  on N.
-/
theorem cascade_step_contrapositive
    (eq : LinearEquation) {N : ℕ} (c : ℕ) (hc : 1 ≤ c) (k' : ℕ) (χ : ℕ → ℕ)
    (hχ' : IsKColoring (N / c) k' (fun d => χ (c * d)))
    (hNoMono : ¬ HasMonoSolution eq N χ) :
    ¬ IsKPartitionRegularAt eq k' (N / c) := by
  intro hPR
  exact hNoMono (cascade_step_general eq c hc k' χ hχ' hPR)

/-! ### WLOG normalization via color swap (Pillar 3 setup).

  The SWAP π_swap a b is the transposition (a b) on ℕ.
  This is the canonical color permutation used in WLOG normalizations.

  Key application: WLOG chi(1) = 0 for any mono-free k-coloring.
-/

/--
  **Swap permutation**: defined via Mathlib's `Equiv.swap`, the transposition
  of a and b on ℕ (using DecidableEq).
-/
def swap_perm (a b : ℕ) (c : ℕ) : ℕ := Equiv.swap a b c

/--
  **swap_perm is injective** (as a bijection via Equiv.swap).
-/
theorem swap_perm_injective (a b : ℕ) :
    Function.Injective (swap_perm a b) :=
  (Equiv.swap a b).injective

/--
  **swap_perm preserves color range [0, k)** when both a, b ∈ [0, k).
-/
theorem swap_perm_lt (a b k : ℕ) (ha : a < k) (hb : b < k) :
    ∀ c, c < k → swap_perm a b c < k := by
  intro c hc
  unfold swap_perm
  -- Equiv.swap a b c = a if c = b, = b if c = a, = c otherwise.
  by_cases hca : c = a
  · rw [hca, Equiv.swap_apply_left]; exact hb
  · by_cases hcb : c = b
    · rw [hcb, Equiv.swap_apply_right]; exact ha
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]; exact hc

/--
  **swap_perm sends a to b**: swap_perm a b a = b.
-/
@[simp]
theorem swap_perm_left (a b : ℕ) : swap_perm a b a = b := by
  unfold swap_perm; rw [Equiv.swap_apply_left]

/--
  **WLOG chi(1) = 0** for mono-free k-coloring: given any mono-free
  k-coloring chi of [1, n] for eq, there exists a mono-free k-coloring
  chi' with chi'(1) = 0 (constructed via color swap permutation).

  This is the canonical "WLOG chi(1) = 0" reduction, available in fully
  general form (any LinearEquation, any k ≥ 1, n ≥ 1).
-/
theorem WLOG_chi_one_eq_zero
    (eq : LinearEquation) (n k : ℕ) (hk : 1 ≤ k) (χ : ℕ → ℕ) (hn : 1 ≤ n)
    (hKcol : IsKColoring n k χ)
    (hNoMono : ¬ HasMonoSolution eq n χ) :
    ∃ χ' : ℕ → ℕ,
      IsKColoring n k χ' ∧ ¬ HasMonoSolution eq n χ' ∧ χ' 1 = 0 := by
  have hchi1 : χ 1 < k := hKcol 1 (le_refl 1) hn
  have hzero_lt_k : (0 : ℕ) < k := hk
  refine ⟨swap_perm 0 (χ 1) ∘ χ, ?_, ?_, ?_⟩
  · exact isKColoring_comp n k χ (swap_perm 0 (χ 1))
      (swap_perm_lt 0 (χ 1) k hzero_lt_k hchi1) hKcol
  · intro hMono
    exact hNoMono ((hasMonoSolution_comp_inj eq n χ (swap_perm 0 (χ 1))
      (swap_perm_injective 0 (χ 1))).mp hMono)
  · -- (π ∘ chi) 1 = swap_perm 0 (chi 1) (chi 1) = 0.
    show swap_perm 0 (χ 1) (χ 1) = 0
    unfold swap_perm
    -- Equiv.swap 0 c c = 0.
    rw [Equiv.swap_apply_right]

/-! ### Second-level structural constraints (Pillar 3 chi' lemmas).

  Applying the structural toolkit to the multiples sub-coloring chi'(d) := χ(c·d)
  yields a SECOND TIER of constraints on χ itself.

  These chi(c·m) inter-relationships are precisely the structural content of
  the compression hypothesis at level k+1.
-/

/--
  **Second-level self-loop**: for mono-free k-coloring χ of [1, n] for bAdicEquation b,
  the multiples sub-coloring χ' inherits the self-loop constraints. Specifically:
  χ(b·(b-1)·m) ≠ χ(b·b·m), i.e., χ((b² - b)·m) ≠ χ(b²·m).

  For b = 3, m = 1: χ(6) ≠ χ(9). For b = 3, m = 2: χ(12) ≠ χ(18). Etc.

  Derived by applying `bAdicEquation_self_loop_chi_diff` to the multiples
  sub-coloring χ'(d) := χ(b·d).
-/
theorem bAdicEquation_second_level_self_loop
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (hbsm : b * b * m ≤ n) :
    χ ((b - 1) * (b * m)) ≠ χ (b * (b * m)) := by
  -- Get χ' mono-free at n/b via multiples sub-coloring.
  have hχ' := multiples_subcoloring_mono_free (bAdicEquation b) b (by omega) χ hNoMono
  -- Apply self-loop to χ' at (b, b·m_in_chi') — but need m_in_chi' such that b · m_in_chi' ≤ n/b.
  -- Set m_in_chi' := m. Then b · m_in_chi' = b·m ≤ n/b iff b²·m ≤ n.
  have h := bAdicEquation_self_loop_chi_diff (b := b) (n := n / b) hb
    (fun d => χ (b * d)) hχ' (m := m) hm
    (by
      -- Need b * m ≤ n / b. With b²·m ≤ n: b · m ≤ n / b.
      apply Nat.le_div_iff_mul_le (by omega : 0 < b) |>.mpr
      calc b * m * b = b * b * m := by ring
        _ ≤ n := hbsm)
  -- h : χ ((b - 1) * m) ≠ χ (b * m), where chi here is the sub-coloring chi'.
  -- chi'(x) = chi(b * x). So h says chi(b*((b-1)*m)) ≠ chi(b*(b*m)).
  -- Simplify chi(b·((b-1)·m)) = chi((b-1)·(b·m)) (mul comm/assoc).
  show χ ((b - 1) * (b * m)) ≠ χ (b * (b * m))
  have heq1 : (b - 1) * (b * m) = b * ((b - 1) * m) := by ring
  rw [heq1]
  exact h

end RadoNumbers.General

namespace RadoNumbers.General

/-! ### R_2(2) = 4 derived FROM SCRATCH in General/ (validation).

  Demonstrates that the General/ structural toolkit (eval linearity,
  multiples sub-coloring, self-loop constraints, canonical-triple constraint,
  WLOG chi(1) = 0) is sufficient to derive R_k(b) for small (b, k) instances
  without ANY project bridge.

  This is a SOUNDNESS check on the framework — the SAME toolkit, applied
  systematically at larger (b, k), would derive CompressionHyp 3 3 and
  ultimately R_3(3) = 27. The multi-month work consists of organizing the
  sub-case enumeration.
-/

/--
  **R_2(2) ≤ 4** derived structurally in General/ from new infrastructure
  (no project bridge).

  For ANY 2-coloring χ of [1, 4] for bAdicEquation 2, χ has a mono Rado
  solution. Equivalently: ¬ ∃ mono-free 2-coloring of [1, 4].

  Proof chain (using ONLY General/ structural lemmas):
  1. WLOG_chi_one_eq_zero → χ(1) = 0.
  2. Self-loop xz at (b=2, m=1): χ(1) ≠ χ(2) → χ(2) = 1.
  3. Self-loop xy at (b=2, m=1): χ(2) ≠ χ(3) → χ(3) = 0.
  4. General Rado (b=2, d=2, y=1) = (4, 1, 3): NOT (χ(4) = χ(1) AND χ(1) = χ(3)) →
     χ(4) ≠ 0 → χ(4) = 1.
  5. Self-loop xz at (b=2, m=2) = (4, 2, 4): χ(2) ≠ χ(4) → 1 ≠ 1. Contradiction.

  KERNEL-PURE.
-/
theorem isKPartitionRegularAt_bAdicEquation_2_2_4_from_scratch :
    IsKPartitionRegularAt (bAdicEquation 2) 2 4 := by
  intro χ hχk
  by_contra hNoMono
  -- WLOG chi(1) = 0.
  obtain ⟨χ', hχ'k, hχ'NoMono, hχ'1⟩ :=
    WLOG_chi_one_eq_zero (bAdicEquation 2) 4 2 (by omega) χ (by omega) hχk hNoMono
  have h12 : χ' 1 ≠ χ' 2 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 2) (n := 4) (by omega) χ' hχ'NoMono
      (m := 1) (by omega) (by omega)
    simpa using h
  have h23 : χ' 2 ≠ χ' 3 := by
    have h := bAdicEquation_self_loop_xy_chi_diff (b := 2) (n := 4) (by omega) χ' hχ'NoMono
      (m := 1) (by omega)
    simpa using h
  have hRado := bAdicEquation_general_rado_constraint (b := 2) (n := 4) (by omega) χ' hχ'NoMono
    (d := 2) (y := 1) (by omega) (by omega) (by omega) (by omega)
  have h24 : χ' 2 ≠ χ' 4 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 2) (n := 4) (by omega) χ' hχ'NoMono
      (m := 2) (by omega) (by omega)
    simpa using h
  have hχ'2 : χ' 2 < 2 := hχ'k 2 (by omega) (by omega)
  have hχ'3 : χ' 3 < 2 := hχ'k 3 (by omega) (by omega)
  have hχ'4 : χ' 4 < 2 := hχ'k 4 (by omega) (by omega)
  have h2eq1 : χ' 2 = 1 := by omega
  have h3eq0 : χ' 3 = 0 := by omega
  have h4ne0 : χ' 4 ≠ 0 := by
    intro h4_zero
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ' 4 = χ' 1
      rw [h4_zero, hχ'1]
    · show χ' 1 = χ' 3
      rw [hχ'1, h3eq0]
  have h4eq1 : χ' 4 = 1 := by omega
  apply h24
  rw [h2eq1, h4eq1]

/--
  **R_2(4) ≤ 16** derived structurally in General/ (no project bridge).

  Demonstrates the from-scratch pattern works at b = 4 too. Structure
  similar to R_2(3) but with chi(3..5) instead of chi(2..4) due to b = 4
  self-loop indices.

  Proof:
  - WLOG χ(1) = 0.
  - Self-loop xz m=1: χ(3) ≠ χ(4).
  - Self-loop xy m=1: χ(4) ≠ χ(5).
  - 2-color: χ(3) = χ(5).
  - General Rado (8, 1, 3) [d=2, y=1]: NOT (χ(8) = χ(1) AND χ(1) = χ(3)).
  - Self-loop xz m=2: χ(6) ≠ χ(8).
  - Case split on χ(4):
    * χ(4) = 0: χ(3) = χ(5) = 1, χ(8) = 0 forced (from triple (8,1,3) with chi(3)=1, chi(1)=0:
                NOT (chi(8)=0 AND chi(3)=0) vacuous since chi(3)≠0). So chi(8) free.
                Hmm need different chain. Let me restart.
-/
theorem isKPartitionRegularAt_bAdicEquation_4_2_16_from_scratch :
    IsKPartitionRegularAt (bAdicEquation 4) 2 16 := by
  intro χ hχk
  by_contra hNoMono
  -- WLOG chi(1) = 0.
  obtain ⟨χ', hχ'k, hχ'NoMono, hχ'1⟩ :=
    WLOG_chi_one_eq_zero (bAdicEquation 4) 16 2 (by omega) χ (by omega) hχk hNoMono
  -- Self-loop xz m=1: χ(3) ≠ χ(4).
  have h34 : χ' 3 ≠ χ' 4 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
      (m := 1) (by omega) (by omega)
    simpa using h
  -- Self-loop xy m=1: χ(4) ≠ χ(5).
  have h45 : χ' 4 ≠ χ' 5 := by
    have h := bAdicEquation_self_loop_xy_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
      (m := 1) (by omega)
    simpa using h
  -- Color bounds.
  have hχ'2 : χ' 2 < 2 := hχ'k 2 (by omega) (by omega)
  have hχ'3 : χ' 3 < 2 := hχ'k 3 (by omega) (by omega)
  have hχ'4 : χ' 4 < 2 := hχ'k 4 (by omega) (by omega)
  have hχ'5 : χ' 5 < 2 := hχ'k 5 (by omega) (by omega)
  have hχ'8 : χ' 8 < 2 := hχ'k 8 (by omega) (by omega)
  have hχ'12 : χ' 12 < 2 := hχ'k 12 (by omega) (by omega)
  -- 2-color: chi'(3) = chi'(5).
  have h35 : χ' 3 = χ' 5 := by omega
  -- Self-loop xz m=2: χ(6) ≠ χ(8). χ(6) NOT yet derived; let's track chi(8).
  -- Self-loop xy m=2: chi(8) ≠ chi(10). Both ≤ 16 ✓.
  have h810 : χ' 8 ≠ χ' 10 := by
    have h := bAdicEquation_self_loop_xy_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
      (m := 2) (by omega)
    simpa using h
  -- Self-loop xz m=3: chi(9) ≠ chi(12).
  have h912 : χ' 9 ≠ χ' 12 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
      (m := 3) (by omega) (by omega)
    simpa using h
  -- Self-loop xz m=4: chi(12) ≠ chi(16).
  have h1216 : χ' 12 ≠ χ' 16 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
      (m := 4) (by omega) (by omega)
    simpa using h
  have hχ'16 : χ' 16 < 2 := hχ'k 16 (by omega) (by omega)
  have hχ'9 : χ' 9 < 2 := hχ'k 9 (by omega) (by omega)
  -- 2-color: chi(9) ≠ chi(12) AND chi(12) ≠ chi(16) → chi(9) = chi(16).
  have h916 : χ' 9 = χ' 16 := by omega
  -- canonical (4, 1, 2): NOT (chi(4) = chi(1) AND chi(1) = chi(2)). chi(1) = 0.
  have hRado412 := bAdicEquation_canonical_triple_constraint (b := 4) (n := 16) (by omega) χ'
    hχ'NoMono (m := 1) (by omega) (by omega) (by omega)
  -- hRado412 : NOT (χ' (4 * 1) = χ' 1 ∧ χ' 1 = χ' (2 * 1)). Simplify.
  -- General Rado (16, 1, 5) [d=4, y=1]: NOT (chi(16) = chi(1) AND chi(1) = chi(5)).
  have hRado1615 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
    χ' hχ'NoMono (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
  -- hRado1615 : NOT (χ' (4 * 4) = χ' 1 ∧ χ' 1 = χ' (1 + 4)). I.e., NOT (chi(16) = chi(1) AND chi(1) = chi(5)).
  -- chi(1) = 0, chi(5) = chi(3) (from h35). So NOT (chi(16) = 0 AND chi(3) = 0).
  -- Case split on chi(4).
  by_cases h4eq0 : χ' 4 = 0
  · -- Case χ'(4) = 0. h34: χ'(3) ≠ 0 → χ'(3) = 1. h35: χ'(5) = 1.
    have h3eq1 : χ' 3 = 1 := by omega
    have h5eq1 : χ' 5 = 1 := by rw [← h35]; exact h3eq1
    -- From hRado412: NOT (chi(4) = chi(1) AND chi(1) = chi(2)). chi(4) = 0 = chi(1) ✓. So chi(2) ≠ chi(1) = 0. chi(2) = 1.
    have h2eq1 : χ' 2 = 1 := by
      by_contra h2_ne
      have h2_eq0 : χ' 2 = 0 := by omega
      apply hRado412
      refine ⟨?_, ?_⟩
      · show χ' (4 * 1) = χ' 1; rw [show (4 * 1 : ℕ) = 4 by decide, h4eq0, hχ'1]
      · show χ' 1 = χ' (2 * 1); rw [show (2 * 1 : ℕ) = 2 by decide, hχ'1, h2_eq0]
    -- Self-loop (8, 6, 8) at b=4, m=2: chi(6) ≠ chi(8).
    have h68 : χ' 6 ≠ χ' 8 := by
      have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
        (m := 2) (by omega) (by omega)
      simpa using h
    -- canonical (8, 2, 4) at b=4, m=2: NOT (chi(8) = chi(2) AND chi(2) = chi(4)).
    -- chi(2) = 1, chi(4) = 0: chi(2) ≠ chi(4), vacuous.
    -- Self-loop xy m=2: chi(8) ≠ chi(10). Already h810.
    -- General Rado (8, 1, 3): NOT (chi(8) = chi(1) AND chi(1) = chi(3)). chi(1) = 0, chi(3) = 1. chi(1) ≠ chi(3), vacuous.
    -- General Rado (8, 3, 5): NOT (chi(8) = chi(3) AND chi(3) = chi(5)). chi(3) = chi(5) = 1. So chi(8) ≠ 1. chi(8) = 0.
    have hRado835 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (d := 2) (y := 3) (by omega) (by omega) (by omega) (by omega)
    -- hRado835 : NOT (χ' (4 * 2) = χ' 3 ∧ χ' 3 = χ' (3 + 2)).
    -- Simplify 4*2=8, 3+2=5. NOT (chi(8) = chi(3) = 1 AND chi(3) = chi(5)).
    have h8ne1 : χ' 8 ≠ 1 := by
      intro h8_eq1
      apply hRado835
      refine ⟨?_, ?_⟩
      · show χ' (4 * 2) = χ' 3; rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq1, h3eq1]
      · show χ' 3 = χ' (3 + 2); rw [show (3 + 2 : ℕ) = 5 by decide, h3eq1, h5eq1]
    have h8eq0 : χ' 8 = 0 := by omega
    -- General Rado (12, 1, 4) at b=4, d=3, y=1: NOT (chi(12) = chi(1) AND chi(1) = chi(4)).
    -- chi(1) = chi(4) = 0. So chi(12) ≠ 0.
    have hRado1214 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    have h12ne0 : χ' 12 ≠ 0 := by
      intro h12_eq0
      apply hRado1214
      refine ⟨?_, ?_⟩
      · show χ' (4 * 3) = χ' 1; rw [show (4 * 3 : ℕ) = 12 by decide, h12_eq0, hχ'1]
      · show χ' 1 = χ' (1 + 3); rw [show (1 + 3 : ℕ) = 4 by decide, hχ'1, h4eq0]
    have h12eq1 : χ' 12 = 1 := by omega
    -- h912: chi(9) ≠ chi(12) = 1. chi(9) = 0.
    have h9eq0 : χ' 9 = 0 := by rw [h12eq1] at h912; omega
    -- h916: chi(9) = chi(16) = 0.
    have h16eq0 : χ' 16 = 0 := by rw [← h916]; exact h9eq0
    -- hRado1615: NOT (chi(16) = chi(1) AND chi(1) = chi(5)). chi(16) = 0 = chi(1) ✓. chi(5) = 1.
    -- chi(1) = 0 ≠ 1 = chi(5). Vacuous. Hmm no contradiction.
    -- Let me find another triple. (12, 4, 7) at b=4, d=3, y=4: NOT (chi(12) = chi(4) AND chi(4) = chi(7)).
    -- chi(12) = 1, chi(4) = 0: chi(12) ≠ chi(4), vacuous.
    -- (16, 1, 5) — already done.
    -- (16, 2, 6) at b=4, d=4, y=2: NOT (chi(16) = chi(2) AND chi(2) = chi(6)).
    -- chi(2) = 1, chi(16) = 0: chi(16) ≠ chi(2), vacuous.
    -- (16, 4, 8) at b=4, d=4, y=4: NOT (chi(16) = chi(4) AND chi(4) = chi(8)).
    -- chi(16) = 0, chi(4) = 0, chi(8) = 0. ALL ZERO. MONO!
    have hRado1648 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (d := 4) (y := 4) (by omega) (by omega) (by omega) (by omega)
    -- hRado1648 : NOT (chi(4 * 4) = chi(4) AND chi(4) = chi(4 + 4)). I.e., NOT (chi(16) = chi(4) AND chi(4) = chi(8)).
    apply hRado1648
    refine ⟨?_, ?_⟩
    · show χ' (4 * 4) = χ' 4; rw [show (4 * 4 : ℕ) = 16 by decide, h16eq0, h4eq0]
    · show χ' 4 = χ' (4 + 4); rw [show (4 + 4 : ℕ) = 8 by decide, h4eq0, h8eq0]
  · -- Case χ'(4) = 1.
    have h4eq1 : χ' 4 = 1 := by omega
    -- h34: chi(3) ≠ 1, so chi(3) = 0. chi(5) = chi(3) = 0.
    have h3eq0 : χ' 3 = 0 := by omega
    have h5eq0 : χ' 5 = 0 := by rw [← h35]; exact h3eq0
    -- canonical (4, 1, 2): NOT (chi(4) = chi(1) AND chi(1) = chi(2)). chi(4) = 1, chi(1) = 0. chi(4) ≠ chi(1), vacuous.
    -- chi(2) free.
    -- canonical (8, 2, 4): NOT (chi(8) = chi(2) AND chi(2) = chi(4)). chi(4) = 1.
    have hRado824 := bAdicEquation_canonical_triple_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (m := 2) (by omega) (by omega) (by omega)
    -- If chi(2) = 1 = chi(4): NOT (chi(8) = 1). chi(8) ≠ 1.
    -- If chi(2) = 0: chi(2) ≠ chi(4), vacuous.
    -- General Rado (8, 1, 3): NOT (chi(8) = chi(1) AND chi(1) = chi(3)). chi(1) = chi(3) = 0. So chi(8) ≠ 0.
    have hRado813 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (d := 2) (y := 1) (by omega) (by omega) (by omega) (by omega)
    have h8ne0 : χ' 8 ≠ 0 := by
      intro h8_eq0
      apply hRado813
      refine ⟨?_, ?_⟩
      · show χ' (4 * 2) = χ' 1; rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq0, hχ'1]
      · show χ' 1 = χ' (1 + 2); rw [show (1 + 2 : ℕ) = 3 by decide, hχ'1, h3eq0]
    have h8eq1 : χ' 8 = 1 := by omega
    -- Self-loop xz m=2: chi(6) ≠ chi(8) = 1. chi(6) = 0.
    have h68 : χ' 6 ≠ χ' 8 := by
      have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := 16) (by omega) χ' hχ'NoMono
        (m := 2) (by omega) (by omega)
      simpa using h
    have h6eq0 : χ' 6 = 0 := by rw [h8eq1] at h68; have hχ'6 : χ' 6 < 2 := hχ'k 6 (by omega) (by omega); omega
    -- General Rado (12, 1, 4): NOT (chi(12) = chi(1) AND chi(1) = chi(4)). chi(1) = 0, chi(4) = 1. Vacuous.
    -- General Rado (12, 2, 5): NOT (chi(12) = chi(2) AND chi(2) = chi(5)). chi(5) = 0. If chi(2) = 0, chi(12) ≠ 0.
    -- General Rado (12, 3, 6): NOT (chi(12) = chi(3) AND chi(3) = chi(6)). chi(3) = chi(6) = 0. chi(12) ≠ 0.
    have hRado1236 := bAdicEquation_general_rado_constraint (b := 4) (n := 16) (by omega)
      χ' hχ'NoMono (d := 3) (y := 3) (by omega) (by omega) (by omega) (by omega)
    have h12ne0 : χ' 12 ≠ 0 := by
      intro h12_eq0
      apply hRado1236
      refine ⟨?_, ?_⟩
      · show χ' (4 * 3) = χ' 3; rw [show (4 * 3 : ℕ) = 12 by decide, h12_eq0, h3eq0]
      · show χ' 3 = χ' (3 + 3); rw [show (3 + 3 : ℕ) = 6 by decide, h3eq0, h6eq0]
    have h12eq1 : χ' 12 = 1 := by omega
    -- General Rado (16, 4, 8) [d=4, y=4]: chi(16) = chi(4) AND chi(4) = chi(8) means chi(16) = 1 = chi(4) = 1 = chi(8). MONO if chi(16) = 1.
    -- chi(12) = 1, h1216 (self-loop xz m=4): chi(12) ≠ chi(16). chi(16) ≠ 1 = chi(12). chi(16) = 0.
    have h16eq0 : χ' 16 = 0 := by rw [h12eq1] at h1216; omega
    -- General Rado (16, 1, 5): NOT (chi(16) = chi(1) AND chi(1) = chi(5)). chi(16) = 0 = chi(1), chi(5) = 0 = chi(1). All zero. MONO!
    apply hRado1615
    refine ⟨?_, ?_⟩
    · show χ' (4 * 4) = χ' 1; rw [show (4 * 4 : ℕ) = 16 by decide, h16eq0, hχ'1]
    · show χ' 1 = χ' (1 + 4); rw [show (1 + 4 : ℕ) = 5 by decide, hχ'1, h5eq0]

theorem isKPartitionRegularAt_bAdicEquation_3_2_9_from_scratch :
    IsKPartitionRegularAt (bAdicEquation 3) 2 9 := by
  intro χ hχk
  by_contra hNoMono
  -- WLOG chi(1) = 0.
  obtain ⟨χ', hχ'k, hχ'NoMono, hχ'1⟩ :=
    WLOG_chi_one_eq_zero (bAdicEquation 3) 9 2 (by omega) χ (by omega) hχk hNoMono
  -- Structural constraints.
  have h23 : χ' 2 ≠ χ' 3 := by
    have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := 9) (by omega) χ' hχ'NoMono
      (m := 1) (by omega) (by omega)
    simpa using h
  have h34 : χ' 3 ≠ χ' 4 := by
    have h := bAdicEquation_self_loop_xy_chi_diff (b := 3) (n := 9) (by omega) χ' hχ'NoMono
      (m := 1) (by omega)
    simpa using h
  -- Color bounds.
  have hχ'2 : χ' 2 < 2 := hχ'k 2 (by omega) (by omega)
  have hχ'3 : χ' 3 < 2 := hχ'k 3 (by omega) (by omega)
  have hχ'4 : χ' 4 < 2 := hχ'k 4 (by omega) (by omega)
  have hχ'6 : χ' 6 < 2 := hχ'k 6 (by omega) (by omega)
  have hχ'9 : χ' 9 < 2 := hχ'k 9 (by omega) (by omega)
  -- With 2 colors, h23 + h34 → chi'(2) = chi'(4).
  have h24 : χ' 2 = χ' 4 := by omega
  -- General Rado (6, 2, 4) [b=3, d=2, y=2]: NOT (χ'(6) = χ'(2) AND χ'(2) = χ'(4)).
  have hRado624 := bAdicEquation_general_rado_constraint (b := 3) (n := 9) (by omega)
    χ' hχ'NoMono (d := 2) (y := 2) (by omega) (by omega) (by omega) (by omega)
  -- With χ'(2) = χ'(4): NOT χ'(6) = χ'(2). So χ'(6) ≠ χ'(2).
  have h62 : χ' 6 ≠ χ' 2 := by
    intro h6_eq_2
    apply hRado624
    refine ⟨?_, ?_⟩
    · show χ' (3 * 2) = χ' 2; rw [show (3 * 2 : ℕ) = 6 by decide]; exact h6_eq_2
    · show χ' 2 = χ' (2 + 2); rw [show (2 + 2 : ℕ) = 4 by decide]; exact h24
  -- Case split on χ'(3). Use by_cases on chi'(3) = 0 to keep hypothesis named.
  by_cases h3eq0 : χ' 3 = 0
  · -- Case χ'(3) = 0.
    have h2eq1 : χ' 2 = 1 := by omega
    have h4eq1 : χ' 4 = 1 := by rw [← h24]; exact h2eq1
    have h6eq0 : χ' 6 = 0 := by rw [h2eq1] at h62; omega
    have hRado613 := bAdicEquation_general_rado_constraint (b := 3) (n := 9) (by omega)
      χ' hχ'NoMono (d := 2) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado613
    refine ⟨?_, ?_⟩
    · show χ' (3 * 2) = χ' 1; rw [show (3 * 2 : ℕ) = 6 by decide, h6eq0, hχ'1]
    · show χ' 1 = χ' (1 + 2); rw [show (1 + 2 : ℕ) = 3 by decide, hχ'1, h3eq0]
  · -- Case χ'(3) = 1 (since chi'(3) < 2 and ≠ 0).
    have h3eq1 : χ' 3 = 1 := by omega
    have h2eq0 : χ' 2 = 0 := by omega
    have h4eq0 : χ' 4 = 0 := by rw [← h24]; exact h2eq0
    have h6eq1 : χ' 6 = 1 := by rw [h2eq0] at h62; omega
    have h69 : χ' 6 ≠ χ' 9 := by
      have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := 9) (by omega) χ' hχ'NoMono
        (m := 3) (by omega) (by omega)
      simpa using h
    have h9eq0 : χ' 9 = 0 := by rw [h6eq1] at h69; omega
    have hRado914 := bAdicEquation_general_rado_constraint (b := 3) (n := 9) (by omega)
      χ' hχ'NoMono (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado914
    refine ⟨?_, ?_⟩
    · show χ' (3 * 3) = χ' 1; rw [show (3 * 3 : ℕ) = 9 by decide, h9eq0, hχ'1]
    · show χ' 1 = χ' (1 + 3); rw [show (1 + 3 : ℕ) = 4 by decide, hχ'1, h4eq0]

/-! ### Multiples-of-3 structural constraints (toward CompressionHyp 3 3).

  Key structural facts about mono-free 3-coloring chi for bAdicEquation 3
  at the multiples-of-3 level. These are the BUILDING BLOCKS for the
  systematic CompressionHyp 3 3 enumeration.
-/

/--
  **First three multiples-of-3 are not all same color**: for mono-free
  k-coloring χ of [1, n] for bAdicEquation 3 (n ≥ 9), NOT all of
  χ(3), χ(6), χ(9) are equal.

  Proof: the Rado triple (9, 3, 6) gives 9 + 3·3 = 18 = 3·6 ✓.
  Mono-freeness forbids χ(9) = χ(3) = χ(6).

  Significance: directly bounds the "all 3 same color at first 3 multiples"
  case in any sub-case enumeration of CompressionHyp 3 3.
-/
theorem bAdicEquation_3_not_all_same_at_3_6_9
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    ¬ (χ 3 = χ 6 ∧ χ 6 = χ 9) := by
  intro ⟨h36, h69⟩
  -- (9, 3, 6) general Rado triple [b=3, d=3, y=3]: NOT (χ(9) = χ(3) ∧ χ(3) = χ(6)).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 3) (by omega) (by omega) (by omega) (by omega)
  -- hRado : NOT (χ (3 * 3) = χ 3 AND χ 3 = χ (3 + 3)). Simplify.
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 3
    rw [show (3 * 3 : ℕ) = 9 by decide]
    -- χ 9 = χ 3 from χ 3 = χ 6 = χ 9 (transitively).
    exact (h36.trans h69).symm
  · show χ 3 = χ (3 + 3)
    rw [show (3 + 3 : ℕ) = 6 by decide]
    exact h36

/--
  **Mono-free chi can't have first-three multiples ALL equal to chi(1)**.

  Strict-strengthening of `bAdicEquation_3_not_all_same_at_3_6_9` plus
  WLOG chi(1) constraint: NOT (chi(3) = chi(1) AND chi(6) = chi(1) AND
  chi(9) = chi(1)).

  Useful for Pillar 3 sub-case elimination: if chi(1) is fixed (e.g., to 0
  by WLOG_chi_one_eq_zero), at least one of chi(3), chi(6), chi(9) is ≠ 0.
-/
theorem bAdicEquation_3_not_all_chi_1_at_3_6_9
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    ¬ (χ 3 = χ 1 ∧ χ 6 = χ 1 ∧ χ 9 = χ 1) := by
  intro ⟨h31, h61, h91⟩
  apply bAdicEquation_3_not_all_same_at_3_6_9 χ h9 hNoMono
  refine ⟨?_, ?_⟩
  · rw [h31, h61]
  · rw [h61, h91]

/--
  **(18, 9, 15) Rado-triple constraint**: for mono-free chi for bAdicEquation 3
  on [1, n] (n ≥ 18), NOT (χ(18) = χ(9) ∧ χ(9) = χ(15)).

  Direct from general_rado_constraint with (b, d, y) = (3, 3, 9): triple
  (9, 9, 18) wait — let me recompute. (b·d, y, y+d) = (3·3, 9, 9+3) = (9, 9, 12).

  Actually I want (18, 9, 15). For (b·d, y, y+d) = (18, 9, 15): b·d = 18, d = 6.
  y = 9, y+d = 15. ✓

  So d = 6, y = 9. Constraint NOT (χ(18) = χ(9) ∧ χ(9) = χ(15)).

  Significance: links chi(9), chi(15), chi(18) — second-level multiples-of-3
  constraints needed for CompressionHyp 3 3.
-/
theorem bAdicEquation_3_not_all_same_at_9_15_18
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    ¬ (χ 18 = χ 9 ∧ χ 9 = χ 15) := by
  intro ⟨h189, h915⟩
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 9
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h189
  · show χ 9 = χ (9 + 6)
    rw [show (9 + 6 : ℕ) = 15 by decide]
    exact h915

/--
  **Parametric family**: NOT (χ(9j) = χ(3j) ∧ χ(3j) = χ(6j)) for any j ≥ 1
  with 9·j ≤ n.

  Generalizes bAdicEquation_3_not_all_same_at_3_6_9 (j = 1) to arbitrary
  scaled triple (3j, 6j, 9j). Direct application of general_rado_constraint
  with (b·d, y, y+d) = (9j, 3j, 6j), i.e., b = 3, d = 3j, y = 3j.
-/
theorem bAdicEquation_3_not_all_same_at_3j_6j_9j
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {j : ℕ} (hj : 1 ≤ j) (hnj : 9 * j ≤ n) :
    ¬ (χ (3 * j) = χ (6 * j) ∧ χ (6 * j) = χ (9 * j)) := by
  intro ⟨h36, h69⟩
  -- Apply general_rado_constraint with b = 3, d = 3j, y = 3j.
  -- Triple (3·(3j), 3j, 3j + 3j) = (9j, 3j, 6j). Constraint: NOT (χ(9j) = χ(3j) ∧ χ(3j) = χ(6j)).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3 * j) (y := 3 * j) (by omega) (by omega)
    (by show 3 * (3 * j) ≤ n; rw [show (3 * (3 * j) : ℕ) = 9 * j by ring]; exact hnj)
    (by show 3 * j + 3 * j ≤ n; rw [show (3 * j + 3 * j : ℕ) = 6 * j by ring];
        calc 6 * j ≤ 9 * j := by nlinarith
          _ ≤ n := hnj)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * (3 * j)) = χ (3 * j)
    rw [show (3 * (3 * j) : ℕ) = 9 * j by ring]
    exact (h36.trans h69).symm
  · show χ (3 * j) = χ (3 * j + 3 * j)
    rw [show (3 * j + 3 * j : ℕ) = 6 * j by ring]
    exact h36

/--
  **Chi(6) determination via Chi(2) = Chi(4)**: for mono-free chi for
  bAdicEquation 3 on [1, n] (n ≥ 6), IF χ(2) = χ(4), THEN χ(6) ≠ χ(2).

  Direct from canonical-triple constraint (b=3, m=2): triple (6, 2, 4).
  Conditional forcing of chi(6) value.

  Useful in sub-case enumeration: many WLOG normalizations end up with
  χ(2) = χ(4), and this constraint then pins down chi(6).
-/
theorem bAdicEquation_3_chi_6_ne_when_chi_2_4_eq
    {n : ℕ} (χ : ℕ → ℕ) (h6 : 6 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24 : χ 2 = χ 4) :
    χ 6 ≠ χ 2 := by
  intro h6_eq_2
  -- canonical (6, 2, 4) at b=3, m=2: NOT (χ(6) = χ(2) ∧ χ(2) = χ(4)).
  have hRado := bAdicEquation_canonical_triple_constraint (b := 3) (n := n)
    (by omega) χ hNoMono (m := 2) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 2) = χ 2
    rw [show (3 * 2 : ℕ) = 6 by decide]; exact h6_eq_2
  · show χ 2 = χ (2 * 2)
    rw [show (2 * 2 : ℕ) = 4 by decide]; exact h24

/--
  **Chi(12) determination via Chi(4) = Chi(8)**: for mono-free chi for
  bAdicEquation 3 on [1, n] (n ≥ 12), IF χ(4) = χ(8), THEN χ(12) ≠ χ(4).

  Direct from canonical-triple constraint (b=3, m=4): triple (12, 4, 8).
  Second-level generalization of chi_6_ne_when_chi_2_4_eq.
-/
theorem bAdicEquation_3_chi_12_ne_when_chi_4_8_eq
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48 : χ 4 = χ 8) :
    χ 12 ≠ χ 4 := by
  intro h12_eq_4
  have hRado := bAdicEquation_canonical_triple_constraint (b := 3) (n := n)
    (by omega) χ hNoMono (m := 4) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 4
    rw [show (3 * 4 : ℕ) = 12 by decide]; exact h12_eq_4
  · show χ 4 = χ (2 * 4)
    rw [show (2 * 4 : ℕ) = 8 by decide]; exact h48

/--
  **General Chi(bm) determination via Chi(m) = Chi(2m)**: for mono-free chi
  for bAdicEquation b on [1, n] (b ≥ 2), any m ≥ 1 with b·m, 2·m ≤ n:
  IF χ(m) = χ(2·m), THEN χ(b·m) ≠ χ(m).

  GENERAL form of chi_6/12_ne lemmas — works for ANY b, m.

  Direct from canonical-triple constraint.
-/
theorem bAdicEquation_chi_bm_ne_when_chi_m_2m_eq
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 1 ≤ m) (hbm : b * m ≤ n) (h2m : 2 * m ≤ n)
    (heq : χ m = χ (2 * m)) :
    χ (b * m) ≠ χ m := by
  intro h_bm_eq_m
  have hRado := bAdicEquation_canonical_triple_constraint hb χ hNoMono hm hbm h2m
  apply hRado
  exact ⟨h_bm_eq_m, heq⟩

/-! ### General Rado constraint convenient FORMS for sub-case work. -/

/--
  **Form 1**: given χ(b·d) = χ(y), derive χ(y+d) ≠ χ(y).

  Direct from general_rado_constraint with the (b·d, y, y+d) Rado triple
  contrapositive on the first conjunct.
-/
theorem bAdicEquation_chi_yd_ne_when_chi_bd_y_eq
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {d y : ℕ} (hd : 1 ≤ d) (hy : 1 ≤ y) (hbd : b * d ≤ n) (hyd : y + d ≤ n)
    (heq : χ (b * d) = χ y) :
    χ (y + d) ≠ χ y := by
  intro h_yd_eq_y
  have hRado := bAdicEquation_general_rado_constraint hb χ hNoMono hd hy hbd hyd
  apply hRado
  exact ⟨heq, h_yd_eq_y.symm⟩

/--
  **Form 2**: given χ(y) = χ(y+d), derive χ(b·d) ≠ χ(y).

  Direct from general_rado_constraint with the (b·d, y, y+d) Rado triple
  contrapositive on the second conjunct.
-/
theorem bAdicEquation_chi_bd_ne_when_chi_y_yd_eq
    {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {d y : ℕ} (hd : 1 ≤ d) (hy : 1 ≤ y) (hbd : b * d ≤ n) (hyd : y + d ≤ n)
    (heq : χ y = χ (y + d)) :
    χ (b * d) ≠ χ y := by
  intro h_bd_eq_y
  have hRado := bAdicEquation_general_rado_constraint hb χ hNoMono hd hy hbd hyd
  apply hRado
  exact ⟨h_bd_eq_y, heq⟩

/-! ### Pillar 3 WLOG normalization (3 sub-cases).

  Given the WLOG_chi_one_eq_zero (chi(1) = 0) + self-loop (chi(2) ≠ chi(3)),
  the chi(2), chi(3) configuration partitions into 3 normalized sub-cases:
  (0, 0, 1), (0, 1, 0), (0, 1, 2). Each requires its own structural proof
  for Pillar 3 closure.
-/

/--
  **First-3 values trichotomy** for mono-free 3-coloring with chi(1) = 0:
  exactly one of three configurations holds for (chi(1), chi(2), chi(3))
  modulo color swap symmetry on {1, 2}.

  This is the WLOG SUB-CASE STRUCTURE for any Pillar 3 attack.

  Given chi(1) = 0 and chi(2) ≠ chi(3), we have:
  - Sub-case A: chi(2) = 0 (so chi(3) ≠ 0).
  - Sub-case B1: chi(2) ≠ 0 AND chi(3) = 0.
  - Sub-case B2: chi(2) ≠ 0 AND chi(3) ≠ 0 (so chi(3) is the third color).

  By color swap on {1, 2}, sub-case A with chi(3) = 2 ≡ chi(3) = 1.
  Similar for B1, B2.
-/
theorem mono_free_3_coloring_chi_1_zero_sub_cases
    {n : ℕ} (χ : ℕ → ℕ) (hn : 3 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hχ1 : χ 1 = 0)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 2 = 0 ∧ χ 3 ≠ 0) ∨ -- sub-case A: chi(2) = 0
    (χ 2 ≠ 0 ∧ χ 3 = 0) ∨ -- sub-case B1: chi(3) = 0
    (χ 2 ≠ 0 ∧ χ 3 ≠ 0 ∧ χ 2 ≠ χ 3) := by -- sub-case B2: both non-zero, distinct
  -- chi(2) ≠ chi(3) from self-loop.
  have h23 : χ 2 ≠ χ 3 := bAdicEquation_3_base_chi_constraint χ hNoMono hn
  -- chi(2), chi(3) < 3 from k-coloring.
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  -- Case split on chi(2).
  by_cases h2_zero : χ 2 = 0
  · -- Sub-case A: chi(2) = 0. Then chi(3) ≠ 0 (since chi(2) ≠ chi(3)).
    left
    refine ⟨h2_zero, ?_⟩
    rw [← h2_zero]; exact h23.symm
  · -- chi(2) ≠ 0. Sub-case on chi(3).
    by_cases h3_zero : χ 3 = 0
    · -- Sub-case B1.
      right; left
      exact ⟨h2_zero, h3_zero⟩
    · -- Sub-case B2.
      right; right
      exact ⟨h2_zero, h3_zero, h23⟩

/--
  **Multi-value structural forcing**: for mono-free 3-coloring chi of [1, n]
  (n ≥ 9) for bAdicEquation 3 with chi(1) = chi(2) = chi(4) = 0:
  chi(6) ≠ 0 AND chi(9) ≠ 0 AND chi(6) ≠ chi(9).

  Hence {chi(6), chi(9)} ⊆ {1, 2} with both distinct. By 3-coloring with
  k = 3, {chi(6), chi(9)} = {1, 2} (cover both non-zero colors).

  This is a SUBSTANTIVE STRUCTURAL FACT for the Pillar 3 sub-case
  enumeration: in sub-case A.1 (chi(4) = 0), chi(6) and chi(9) are
  completely determined modulo color swap.

  Proof chain:
  1. chi(6) ≠ chi(2) = 0 (from chi_6_ne_when_chi_2_4_eq with chi(2) = chi(4)).
  2. chi(9) ≠ 0 from (9, 1, 4) Rado: chi(1) = chi(4) = 0 forces chi(9) ≠ 0.
  3. chi(6) ≠ chi(9) from self-loop (9, 6, 9): xz form at m = 3.
-/
theorem bAdicEquation_3_chi_6_9_forced_when_chi_1_2_4_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0) :
    χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 6 ≠ χ 9 := by
  refine ⟨?_, ?_, ?_⟩
  · -- chi(6) ≠ 0: from chi_6_ne_when_chi_2_4_eq with chi(2) = chi(4) = 0.
    have h24 : χ 2 = χ 4 := by rw [h2, h4]
    have h62 : χ 6 ≠ χ 2 := bAdicEquation_3_chi_6_ne_when_chi_2_4_eq χ (by omega) hNoMono h24
    rw [h2] at h62; exact h62
  · -- chi(9) ≠ 0: from (9, 1, 4) Rado [b=3, d=3, y=1].
    -- NOT (chi(9) = chi(1) AND chi(1) = chi(4)). chi(1) = chi(4) = 0.
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    intro h9_eq_0
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 1
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_0, h1]
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h1, h4]
  · -- chi(6) ≠ chi(9): self-loop (9, 6, 9) x=z form at m = 3.
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 3) (by omega) (by omega)
    -- h : χ (2 * 3) ≠ χ (3 * 3). I.e., χ 6 ≠ χ 9.
    simpa using h

/--
  **Sub-case A.1.a deeper forcing**: under chi(1) = chi(2) = chi(4) = 0 AND
  chi(6) = 1 (WLOG within sub-case), chi(9) = 2 AND chi(5) ≠ 1 AND chi(7) ≠ 1.

  These follow from:
  - chi(9) = 2: chi(9) ≠ 0 (above) AND chi(9) ≠ chi(6) = 1 (above) → chi(9) = 2.
  - chi(5) ≠ 1: (6, 3, 5) Rado constraint with chi(6) = chi(3) (= 1 in this case).
    Actually need chi(3) = 1 too.
  - chi(7) ≠ 1: (3, 6, 7) Rado constraint with chi(3) = chi(6) (= 1 in this case).

  Specifically under chi(3) = chi(6) = 1: chi(5), chi(7) ∈ {0, 2}.
-/
theorem bAdicEquation_3_chi_5_7_forced_when_chi_3_6_eq_1
    {n : ℕ} (χ : ℕ → ℕ) (h7 : 7 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (hχ3 : χ 3 = 1) (hχ6 : χ 6 = 1) :
    χ 5 ≠ 1 ∧ χ 7 ≠ 1 := by
  refine ⟨?_, ?_⟩
  · -- chi(5) ≠ 1: from (6, 3, 5) Rado [b=3, d=2, y=3].
    -- NOT (chi(6) = chi(3) AND chi(3) = chi(5)). With chi(3) = chi(6) = 1:
    -- NOT (1 = 1 AND 1 = chi(5)). So chi(5) ≠ 1.
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 3) (by omega) (by omega) (by omega) (by omega)
    intro h5_eq_1
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 3
      rw [show (3 * 2 : ℕ) = 6 by decide, hχ6, hχ3]
    · show χ 3 = χ (3 + 2)
      rw [show (3 + 2 : ℕ) = 5 by decide, hχ3, h5_eq_1]
  · -- chi(7) ≠ 1: from (3, 6, 7) Rado [b=3, d=1, y=6].
    -- NOT (chi(3) = chi(6) AND chi(6) = chi(7)). With chi(3) = chi(6) = 1:
    -- NOT (1 = 1 AND 1 = chi(7)). So chi(7) ≠ 1.
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 6) (by omega) (by omega) (by omega) (by omega)
    intro h7_eq_1
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 6
      rw [show (3 * 1 : ℕ) = 3 by decide, hχ3, hχ6]
    · show χ 6 = χ (6 + 1)
      rw [show (6 + 1 : ℕ) = 7 by decide, hχ6, h7_eq_1]

/--
  **Forced multiples-of-3 inequality via (3d, y, y+d) Rado triples**: for
  mono-free chi for bAdicEquation 3 on [1, n] and any d, y ≥ 1 with
  3·d ≤ n AND y + d ≤ n, IF χ(y) = χ(y+d) THEN χ(3·d) ≠ χ(y).

  Specialization of bAdicEquation_chi_bd_ne_when_chi_y_yd_eq to b = 3.
  Useful for forcing multiples-of-3 chi values via pair equalities.

  Examples:
  - d = 4, y = 1: χ(1) = χ(5) → χ(12) ≠ χ(1).
  - d = 6, y = 1: χ(1) = χ(7) → χ(18) ≠ χ(1).
  - d = 5, y = 1: χ(1) = χ(6) → χ(15) ≠ χ(1).
-/
theorem bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {d y : ℕ} (hd : 1 ≤ d) (hy : 1 ≤ y) (h3d : 3 * d ≤ n) (hyd : y + d ≤ n)
    (heq : χ y = χ (y + d)) :
    χ (3 * d) ≠ χ y :=
  bAdicEquation_chi_bd_ne_when_chi_y_yd_eq (b := 3) (n := n) (by omega) χ hNoMono
    hd hy h3d hyd heq

/--
  **chi(12) ≠ 0** when chi(1) = chi(5) = 0 (specialization of Form 2 at d=4, y=1).
-/
theorem bAdicEquation_3_chi_12_ne_zero_when_chi_1_5_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h5 : χ 5 = 0) :
    χ 12 ≠ 0 := by
  have h15 : χ 1 = χ (1 + 4) := by
    rw [show (1 + 4 : ℕ) = 5 by decide, h1, h5]
  have h := bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq χ hNoMono
    (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega) h15
  -- h : χ (3 * 4) ≠ χ 1. Simplify 3*4 = 12 and chi(1) = 0.
  rw [show (3 * 4 : ℕ) = 12 by decide, h1] at h
  exact h

/--
  **chi(15) ≠ 0** when chi(1) = chi(6) = 0 (specialization at d=5, y=1).
-/
theorem bAdicEquation_3_chi_15_ne_zero_when_chi_1_6_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h6 : χ 6 = 0) :
    χ 15 ≠ 0 := by
  have h16 : χ 1 = χ (1 + 5) := by
    rw [show (1 + 5 : ℕ) = 6 by decide, h1, h6]
  have h := bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq χ hNoMono
    (d := 5) (y := 1) (by omega) (by omega) (by omega) (by omega) h16
  rw [show (3 * 5 : ℕ) = 15 by decide, h1] at h
  exact h

/--
  **chi(18) ≠ 0** when chi(1) = chi(7) = 0 (specialization at d=6, y=1).
-/
theorem bAdicEquation_3_chi_18_ne_zero_when_chi_1_7_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h7 : χ 7 = 0) :
    χ 18 ≠ 0 := by
  have h17 : χ 1 = χ (1 + 6) := by
    rw [show (1 + 6 : ℕ) = 7 by decide, h1, h7]
  have h := bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq χ hNoMono
    (d := 6) (y := 1) (by omega) (by omega) (by omega) (by omega) h17
  rw [show (3 * 6 : ℕ) = 18 by decide, h1] at h
  exact h

/--
  **GENERAL PRINCIPLE**: for mono-free 3-coloring chi of [1, n] for
  bAdicEquation 3 with χ(1) = 0, for ANY y ∈ [2, n] with χ(y) = 0 AND
  3·(y-1) ≤ n, χ(3·(y-1)) ≠ 0.

  This is the UNIVERSAL chi-forcing pattern that the 12/15/18 lemmas
  specialize. Any second "zero-color" point y forces the multiple
  3·(y-1) to be non-zero.

  Use case: ANY hypothesis like "χ(y) = 0 for y = 5, 6,..., 9" yields
  "χ(12), χ(15), χ(18), χ(21), χ(24) all ≠ 0", which is significant
  progress toward CompressionHyp 3 3 omits-color-0 case.

  KERNEL-PURE.
-/
theorem bAdicEquation_3_chi_3_y_minus_1_ne_zero_when_chi_y_eq_zero
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0)
    {y : ℕ} (hy : 2 ≤ y) (hyn : y ≤ n) (h3y1 : 3 * (y - 1) ≤ n)
    (h_chi_y : χ y = 0) :
    χ (3 * (y - 1)) ≠ 0 := by
  -- Use Form 2: χ(1) = χ(1 + (y - 1)) = χ(y), then χ(3·(y-1)) ≠ χ(1) = 0.
  have hyd : (1 + (y - 1) : ℕ) = y := by omega
  have h1y : χ 1 = χ (1 + (y - 1)) := by
    rw [hyd, h1, h_chi_y]
  have h := bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq χ hNoMono
    (d := y - 1) (y := 1) (by omega) (by omega) (by omega) (by omega) h1y
  -- h : χ (3 * (y - 1)) ≠ χ 1. χ 1 = 0.
  rw [h1] at h
  exact h

/--
  **MOST GENERAL chi-forcing principle**: for mono-free 3-coloring chi of
  [1, n] for bAdicEquation 3, for ANY two indices y < y' in [1, n] with
  χ(y) = χ(y') AND 3·(y' - y) ≤ n, χ(3·(y' - y)) ≠ χ(y).

  This is the SHARPEST atomic forcing pattern: any pair of same-color points
  forces a third multiple-of-3 to be different color.

  Specializations (with c = χ(y) = χ(y')):
  - y = 1, y' = 2, c = 0: χ(3) ≠ 0.
  - y = 1, y' = 5, c = 0: χ(12) ≠ 0.
  - y = 2, y' = 7, c = 0: χ(15) ≠ 0.
  - y = 5, y' = 13, c = 0: χ(24) ≠ 0.
  - etc.

  KERNEL-PURE.
-/
theorem bAdicEquation_3_chi_3_diff_ne_when_chi_y_y'_eq
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {y y' : ℕ} (hyy' : y < y') (hy : 1 ≤ y) (hy'n : y' ≤ n)
    (h3diff : 3 * (y' - y) ≤ n)
    (h_chi_eq : χ y = χ y') :
    χ (3 * (y' - y)) ≠ χ y := by
  -- General Rado triple (3·(y'-y), y, y + (y'-y)) = (3·(y'-y), y, y'). Constraint:
  -- NOT (χ(3·(y'-y)) = χ(y) AND χ(y) = χ(y')).
  have hyd : (y + (y' - y) : ℕ) = y' := by omega
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := y' - y) (y := y) (by omega) hy (by omega)
    (by rw [hyd]; exact hy'n)
  intro h_3diff_eq_y
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * (y' - y)) = χ y; exact h_3diff_eq_y
  · show χ y = χ (y + (y' - y))
    rw [hyd]; exact h_chi_eq

/--
  **Corollary**: same as above but specialized to χ(y) = χ(y') = 0
  (the most common use case in Pillar 3 attacks).
-/
theorem bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {y y' : ℕ} (hyy' : y < y') (hy : 1 ≤ y) (hy'n : y' ≤ n)
    (h3diff : 3 * (y' - y) ≤ n)
    (h_chi_y : χ y = 0) (h_chi_y' : χ y' = 0) :
    χ (3 * (y' - y)) ≠ 0 := by
  have h_eq : χ y = χ y' := by rw [h_chi_y, h_chi_y']
  have h := bAdicEquation_3_chi_3_diff_ne_when_chi_y_y'_eq χ hNoMono hyy' hy hy'n h3diff h_eq
  rw [h_chi_y] at h
  exact h

/--
  **SUB-CASE A.1 partial closure**: for mono-free chi for bAdicEquation 3 on
  [1, n] (n ≥ 21) with chi at the SIX non-multiples-of-3 indices {1, 2, 4, 5, 7, 8}
  all = 0:
    χ(3), χ(6), χ(9), χ(12), χ(15), χ(18), χ(21) are ALL ≠ 0.

  Proof: 7 applications of bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero
  at suitable (y, y') pairs:
    - χ(3) via (1, 2): y' - y = 1.
    - χ(6) via (2, 4): y' - y = 2.
    - χ(9) via (1, 4): y' - y = 3.
    - χ(12) via (1, 5): y' - y = 4.
    - χ(15) via (2, 7): y' - y = 5.
    - χ(18) via (1, 7): y' - y = 6.
    - χ(21) via (1, 8): y' - y = 7.

  REMAINING for full Pillar 3 sub-case A.1 closure: χ(24) requires pair with
  diff 8, no such pair exists in {1, 2, 4, 5, 7, 8} (max diff is 7). So
  chi(24) requires additional structural constraints beyond this hypothesis
  set (e.g., assuming more chi values at higher indices = 0).

  This DEMONSTRATES the most general forcing principle's POWER and SCOPE.
  KERNEL-PURE.
-/
theorem bAdicEquation_3_partial_pillar3_A1
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0)
    (h5 : χ 5 = 0) (h7 : χ 7 = 0) (h8 : χ 8 = 0) :
    χ 3 ≠ 0 ∧ χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 12 ≠ 0 ∧ χ 15 ≠ 0 ∧ χ 18 ≠ 0 ∧ χ 21 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- chi(3) via (1, 2): y' - y = 1, 3·1 = 3.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 1) (y' := 2) (by omega) (by omega) (by omega) (by omega) h1 h2
    simpa using h
  · -- chi(6) via (2, 4): y' - y = 2, 3·2 = 6.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 2) (y' := 4) (by omega) (by omega) (by omega) (by omega) h2 h4
    simpa using h
  · -- chi(9) via (1, 4): y' - y = 3, 3·3 = 9.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 1) (y' := 4) (by omega) (by omega) (by omega) (by omega) h1 h4
    simpa using h
  · -- chi(12) via (1, 5): y' - y = 4, 3·4 = 12.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 1) (y' := 5) (by omega) (by omega) (by omega) (by omega) h1 h5
    simpa using h
  · -- chi(15) via (2, 7): y' - y = 5, 3·5 = 15.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 2) (y' := 7) (by omega) (by omega) (by omega) (by omega) h2 h7
    simpa using h
  · -- chi(18) via (1, 7): y' - y = 6, 3·6 = 18.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 1) (y' := 7) (by omega) (by omega) (by omega) (by omega) h1 h7
    simpa using h
  · -- chi(21) via (1, 8): y' - y = 7, 3·7 = 21.
    have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
      (y := 1) (y' := 8) (by omega) (by omega) (by omega) (by omega) h1 h8
    simpa using h

/--
  **FULL SUB-CASE A.1 + chi(10) = 0 closure**: extends partial closure with
  chi(10) = 0 hypothesis to force chi(24) ≠ 0. All 8 multiples-of-3 in [3, 24]
  forced ≠ 0.

  This gives CompressionHyp 3 3 with c₀ = 0 in this specific sub-sub-case
  (sub-case A.1 augmented with chi(10) = 0).

  KERNEL-PURE.
-/
theorem bAdicEquation_3_full_pillar3_A1_with_chi_10_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0)
    (h5 : χ 5 = 0) (h7 : χ 7 = 0) (h8 : χ 8 = 0) (h10 : χ 10 = 0) :
    χ 3 ≠ 0 ∧ χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 12 ≠ 0 ∧
    χ 15 ≠ 0 ∧ χ 18 ≠ 0 ∧ χ 21 ≠ 0 ∧ χ 24 ≠ 0 := by
  -- First 7 from partial closure.
  obtain ⟨h3, h6, h9, h12, h15, h18, h21⟩ :=
    bAdicEquation_3_partial_pillar3_A1 (n := n) χ (by omega) hNoMono h1 h2 h4 h5 h7 h8
  refine ⟨h3, h6, h9, h12, h15, h18, h21, ?_⟩
  -- chi(24) ≠ 0 via pair (2, 10): y' - y = 8, 3·8 = 24.
  have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
    (y := 2) (y' := 10) (by omega) (by omega) (by omega) (by omega) h2 h10
  simpa using h

/--
  **FULL SUB-CASE A.1 + chi(13) = 0 closure**: alternative augmentation
  via pair (5, 13) with diff 8 forces chi(24) ≠ 0.

  Same content as _with_chi_10_eq_zero but with different witness chi value.
  Demonstrates the SYMMETRIC structure of the chi-forcing principle.
-/
theorem bAdicEquation_3_full_pillar3_A1_with_chi_13_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0)
    (h5 : χ 5 = 0) (h7 : χ 7 = 0) (h8 : χ 8 = 0) (h13 : χ 13 = 0) :
    χ 3 ≠ 0 ∧ χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 12 ≠ 0 ∧
    χ 15 ≠ 0 ∧ χ 18 ≠ 0 ∧ χ 21 ≠ 0 ∧ χ 24 ≠ 0 := by
  obtain ⟨h3, h6, h9, h12, h15, h18, h21⟩ :=
    bAdicEquation_3_partial_pillar3_A1 (n := n) χ (by omega) hNoMono h1 h2 h4 h5 h7 h8
  refine ⟨h3, h6, h9, h12, h15, h18, h21, ?_⟩
  -- chi(24) ≠ 0 via pair (5, 13): y' - y = 8, 3·8 = 24.
  have h := bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero (n := n) χ hNoMono
    (y := 5) (y' := 13) (by omega) (by omega) (by omega) (by omega) h5 h13
  simpa using h

/--
  **FULL SUB-CASE A.1 + chi(16) = 0 via self-loop closure**: third
  augmentation using self-loop at m = 8 instead of forcing principle.

  Self-loop xz (24, 16, 24): χ(16) ≠ χ(24). Combined with χ(16) = 0 gives
  χ(24) ≠ 0.

  Demonstrates that DIFFERENT structural tools (self-loop vs pair-forcing)
  yield the same conclusion through different routes.
-/
theorem bAdicEquation_3_full_pillar3_A1_with_chi_16_eq_zero
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0)
    (h5 : χ 5 = 0) (h7 : χ 7 = 0) (h8 : χ 8 = 0) (h16 : χ 16 = 0) :
    χ 3 ≠ 0 ∧ χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 12 ≠ 0 ∧
    χ 15 ≠ 0 ∧ χ 18 ≠ 0 ∧ χ 21 ≠ 0 ∧ χ 24 ≠ 0 := by
  obtain ⟨h3, h6, h9, h12, h15, h18, h21⟩ :=
    bAdicEquation_3_partial_pillar3_A1 (n := n) χ (by omega) hNoMono h1 h2 h4 h5 h7 h8
  refine ⟨h3, h6, h9, h12, h15, h18, h21, ?_⟩
  -- chi(24) ≠ 0 via self-loop xz at m = 8: chi(16) ≠ chi(24). chi(16) = 0.
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 8) (by omega) (by omega)
  -- h : chi(2 * 8) ≠ chi(3 * 8), i.e., chi 16 ≠ chi 24.
  have h' : χ 16 ≠ χ 24 := by
    have := h
    rw [show (2 * 8 : ℕ) = 16 by decide, show (3 * 8 : ℕ) = 24 by decide] at this
    exact this
  -- chi(16) = 0, so chi(24) ≠ 0.
  intro h24_eq_0
  apply h'
  rw [h16, h24_eq_0]

/--
  **UNIFIED sub-case A.1 closure**: ANY of three augmentations (chi(10) = 0,
  chi(13) = 0, OR chi(16) = 0) yields full 8-fold closure with c₀ = 0.

  Disjunctive hypothesis form for organized sub-case enumeration.
-/
theorem bAdicEquation_3_full_pillar3_A1_unified
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h1 : χ 1 = 0) (h2 : χ 2 = 0) (h4 : χ 4 = 0)
    (h5 : χ 5 = 0) (h7 : χ 7 = 0) (h8 : χ 8 = 0)
    (hAug : χ 10 = 0 ∨ χ 13 = 0 ∨ χ 16 = 0) :
    χ 3 ≠ 0 ∧ χ 6 ≠ 0 ∧ χ 9 ≠ 0 ∧ χ 12 ≠ 0 ∧
    χ 15 ≠ 0 ∧ χ 18 ≠ 0 ∧ χ 21 ≠ 0 ∧ χ 24 ≠ 0 := by
  rcases hAug with h10 | h13 | h16
  · exact bAdicEquation_3_full_pillar3_A1_with_chi_10_eq_zero (n := n) χ h24 hNoMono
      h1 h2 h4 h5 h7 h8 h10
  · exact bAdicEquation_3_full_pillar3_A1_with_chi_13_eq_zero (n := n) χ h24 hNoMono
      h1 h2 h4 h5 h7 h8 h13
  · exact bAdicEquation_3_full_pillar3_A1_with_chi_16_eq_zero (n := n) χ h24 hNoMono
      h1 h2 h4 h5 h7 h8 h16

/--
  **Self-loop (18, 18, 24)** Rado triple: for mono-free chi for bAdicEquation 3
  with 24 ≤ n, χ(18) ≠ χ(24).

  Direct from self-loop xy at m = 6: (b·m, b·m, (b+1)·m) = (18, 18, 24).
-/
theorem bAdicEquation_3_chi_18_ne_chi_24
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 18 ≠ χ 24 := by
  have h := bAdicEquation_self_loop_xy_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 6) (by omega) (by omega)
  -- h : χ (3 * 6) ≠ χ ((3 + 1) * 6). Convert literals.
  show χ (3 * 6) ≠ χ ((3 + 1) * 6)
  exact h

/--
  **Self-loop (24, 16, 24)** Rado triple: chi(16) ≠ chi(24).

  Self-loop xz at m = 8: (b·m, (b-1)·m, b·m) = (24, 16, 24).
-/
theorem bAdicEquation_3_chi_16_ne_chi_24
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 16 ≠ χ 24 := by
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 8) (by omega) (by omega)
  -- h : χ (2 * 8) ≠ χ (3 * 8). Convert literals.
  show χ (2 * 8) ≠ χ (3 * 8)
  exact h

/--
  **CRITICAL sub-sub-case**: under sub-case A.1 hypotheses and chi(16), chi(18) ∈ {1, 2}
  with chi(16) ≠ chi(18), chi(24) is forced to be the third color (= 0).

  Proof: chi(24) ≠ chi(16) AND chi(24) ≠ chi(18), so chi(24) ∉ {chi(16), chi(18)}.
  Given chi(16), chi(18) ∈ {1, 2} distinct, {chi(16), chi(18)} = {1, 2}.
  With chi(24) < 3 (3-coloring), chi(24) ∈ {0, 1, 2}\{1, 2} = {0}.

  This identifies a CRITICAL CONFIGURATION where chi(24) = 0 is FORCED.
  In this configuration, chi at multiples-of-3 spans all 3 colors:
    χ(3..21) ∈ {1, 2} (forced) ∪ χ(24) = 0.

  Since this would VIOLATE CompressionHyp 3 3 (no color omitted at multiples),
  this entire configuration must be IMPOSSIBLE for mono-free chi.

  TODO (multi-week): derive contradiction by finding mono Rado triple in this
  configuration. Requires deeper structural analysis of chi values at
  unspecified indices.
-/
theorem bAdicEquation_3_chi_24_eq_zero_when_chi_16_18_distinct_nonzero
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_pos : χ 16 ≠ 0) (h18_pos : χ 18 ≠ 0) (h16_18_ne : χ 16 ≠ χ 18) :
    χ 24 = 0 := by
  -- chi(24) ≠ chi(16) and chi(24) ≠ chi(18).
  have h_24_16 : χ 24 ≠ χ 16 :=
    (bAdicEquation_3_chi_16_ne_chi_24 χ h24 hNoMono).symm
  have h_24_18 : χ 24 ≠ χ 18 :=
    (bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono).symm
  -- chi values bounded: chi(16), chi(18), chi(24) < 3.
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  -- chi(16), chi(18) ∈ {1, 2} (non-zero), distinct → {chi(16), chi(18)} = {1, 2}.
  -- chi(24) ∉ {chi(16), chi(18)} = {1, 2} → chi(24) = 0.
  omega


/-! ### Threshold equivalence FROM SCRATCH (kernel-pure capstone).

  With the kernel-pure lower bound (valuationColoring mono-freeness in
  BAdicEquation.lean), R_k(b) = b^k for any (b, k) reduces to proving ONLY
  the upper bound IsKPartitionRegularAt at b^k. The lower bound is automatic.
-/

/--
  **R_k(b) = b^k iff IsKPartitionRegularAt at b^k** (kernel-pure threshold
  equivalence FROM SCRATCH).

  Given the kernel-pure lower bound (proven via valuation coloring), the
  full IsRadoNumber statement for (b, k, b^k) is equivalent to just the
  upper bound IsKPartitionRegularAt at b^k.

  This is the CANONICAL REDUCTION for any kernel-pure threshold result:
  - To prove R_k(b) = b^k: it SUFFICES to prove IsKPartitionRegularAt at b^k.
  - The lower bound R_k(b) ≥ b^k is automatic from valuation coloring.

  COMPARE with `isRadoNumber_radoEq_3_27_iff_pillar3` (specific to b=3, k=3,
  uses project bridge for lower bound). This general version uses ONLY
  General/ kernel-pure infrastructure.

  KERNEL-PURE end-to-end.
-/
theorem isRadoNumber_iff_isKPartitionRegularAt_from_scratch
    (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
    IsRadoNumber (bAdicEquation b) k (b ^ k) ↔
    IsKPartitionRegularAt (bAdicEquation b) k (b ^ k) := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro hUpper
    refine ⟨hUpper, ?_⟩
    intro M hM hPR
    have hLower := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one_from_scratch b k hb hk
    apply hLower
    exact isKPartitionRegularAt_mono _ _ M (b ^ k - 1) (by omega) hPR

/-! ### §49. CompressionHyp 3 3 STRUCTURAL TOOLKIT — multiples-of-3 chain.

  Targets the open piece: for any mono-free 3-coloring χ of [1, 26] for
  bAdicEquation 3, the chi values at multiples of 3 in [3, 24] omit some
  color (= CompressionHyp 3 3).

  These lemmas extract the chi-distinctness relations at multiples of 3
  from existing self-loop machinery.
-/

/--
  **chi(6) ≠ chi(9)** for mono-free 3-coloring of bAdicEquation 3 with n ≥ 9.
  Specialization of self-loop xz at m=3.
-/
theorem bAdicEquation_3_chi_6_ne_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 6 ≠ χ 9 := by
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 3) (by omega) (by omega)
  show χ (2 * 3) ≠ χ (3 * 3)
  exact h

/--
  **chi(9) ≠ chi(12)** for mono-free 3-coloring of bAdicEquation 3 with n ≥ 12.
  Specialization of self-loop xy at m=3.
-/
theorem bAdicEquation_3_chi_9_ne_chi_12
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 9 ≠ χ 12 := by
  have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 3) (by omega) (by omega)
  show χ (3 * 3) ≠ χ (4 * 3)
  exact h

/--
  **chi(12) ≠ chi(18)** for mono-free 3-coloring of bAdicEquation 3 with n ≥ 18.
  Specialization of self-loop xz at m=6.
-/
theorem bAdicEquation_3_chi_12_ne_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 12 ≠ χ 18 := by
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 6) (by omega) (by omega)
  show χ (2 * 6) ≠ χ (3 * 6)
  exact h

/--
  **chi(12) ≠ chi(16)** for mono-free 3-coloring of bAdicEquation 3 with n ≥ 16.
  Specialization of self-loop xy at m=4.
-/
theorem bAdicEquation_3_chi_12_ne_chi_16
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 12 ≠ χ 16 := by
  have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 4) (by omega) (by omega)
  show χ (3 * 4) ≠ χ (4 * 4)
  exact h

/--
  **5-chain distinctness at multiples of 3**: for mono-free 3-coloring χ of
  [1, n] with n ≥ 24 for bAdicEquation 3, the values
    χ(6), χ(9), χ(12), χ(18), χ(24)
  form a chain where ADJACENT VALUES ARE DISTINCT:
    χ(6) ≠ χ(9), χ(9) ≠ χ(12), χ(12) ≠ χ(18), χ(18) ≠ χ(24).

  Bundled from the 4 self-loop specializations. Critical for the
  CompressionHyp 3 3 structural attack.
-/
theorem bAdicEquation_3_five_chain_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 6 ≠ χ 9 ∧ χ 9 ≠ χ 12 ∧ χ 12 ≠ χ 18 ∧ χ 18 ≠ χ 24 :=
  ⟨bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono,
   bAdicEquation_3_chi_9_ne_chi_12 χ (by omega) hNoMono,
   bAdicEquation_3_chi_12_ne_chi_18 χ (by omega) hNoMono,
   bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono⟩

/--
  **chi at {6, 9, 12} all distinct ⇒ surjection onto {0, 1, 2}** (3-coloring
  forces full surjection on 3-chain when all adjacent are distinct).

  For any 3-coloring χ with χ(6), χ(9), χ(12) < 3 and pairwise distinct,
  {χ(6), χ(9), χ(12)} = {0, 1, 2} (as a set).

  This is a finite arithmetic fact (chi < 3 + 3 distinct = surjective).
-/
theorem bAdicEquation_3_chi_6_9_12_surjective_when_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12) :
    ∀ c : ℕ, c < 3 → c = χ 6 ∨ c = χ 9 ∨ c = χ 12 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  intro c hc
  omega

/-! ### §50. CompressionHyp 3 3 — case (chi(6), chi(9), chi(12)) all distinct.

  In this case, chi at {6, 9, 12} surjects onto {0, 1, 2}, so all colors
  appear at multiples of 3. We need to derive contradiction.

  Key structural facts:
  - chi(18) ≠ chi(12) (self-loop xz m=6) → chi(18) ∈ {chi(6), chi(9)}
  - chi(16) ≠ chi(12) (self-loop xy m=4) → chi(16) ∈ {chi(6), chi(9)}
  - chi(24) ≠ chi(16), chi(24) ≠ chi(18) (self-loops) → constraints on chi(24)
-/

/--
  **chi(18) ∈ {chi(6), chi(9)} when chi(6), chi(9), chi(12) are distinct 3-coloring values**.

  Direct from chi(18) ≠ chi(12) plus chi(18) < 3 plus the surjectivity lemma.
-/
theorem bAdicEquation_3_chi_18_in_6_9_when_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12) :
    χ 18 = χ 6 ∨ χ 18 = χ 9 := by
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have h12_ne_18 := bAdicEquation_3_chi_12_ne_chi_18 χ (by omega) hNoMono
  have h_surj := bAdicEquation_3_chi_6_9_12_surjective_when_distinct (n := n) χ (by omega) hχk
    h6_ne_9 h6_ne_12 h9_ne_12
  have h_case := h_surj (χ 18) hχ18
  rcases h_case with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h12_ne_18.symm

/--
  **chi(16) ∈ {chi(6), chi(9)} when chi(6), chi(9), chi(12) are distinct 3-coloring values**.

  Direct from chi(16) ≠ chi(12) plus chi(16) < 3.
-/
theorem bAdicEquation_3_chi_16_in_6_9_when_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12) :
    χ 16 = χ 6 ∨ χ 16 = χ 9 := by
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have h12_ne_16 := bAdicEquation_3_chi_12_ne_chi_16 χ (by omega) hNoMono
  have h_surj := bAdicEquation_3_chi_6_9_12_surjective_when_distinct (n := n) χ (by omega) hχk
    h6_ne_9 h6_ne_12 h9_ne_12
  have h_case := h_surj (χ 16) hχ16
  rcases h_case with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h12_ne_16.symm

/-! ### §51. CompressionHyp 3 3 — EASY sub-case closure.

  When chi(6), chi(9), chi(12) all distinct AND chi(16) = chi(6) AND
  chi(18) = chi(6), the (6, 16, 18) Rado triple is monochromatic (since
  chi(6) = chi(16) = chi(18)), contradicting mono-freeness.

  This closes ONE of the four sub-cases of the "(6,9,12) distinct" branch.
-/

/--
  **(6, 16, 18) general Rado triple constraint**: for mono-free chi for
  bAdicEquation 3 with n ≥ 18, NOT (chi(6) = chi(16) ∧ chi(16) = chi(18)).

  Specialization of general Rado constraint at b=3, d=2, y=16: NOT (chi(6) =
  chi(16) AND chi(16) = chi(18)).
-/
theorem bAdicEquation_3_rado_6_16_18
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    ¬ (χ 6 = χ 16 ∧ χ 16 = χ 18) := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 16) (by omega) (by omega) (by omega) (by omega)
  intro ⟨h1, h2⟩
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 2) = χ 16
    rw [show (3 * 2 : ℕ) = 6 by decide]; exact h1
  · show χ 16 = χ (16 + 2)
    rw [show (16 + 2 : ℕ) = 18 by decide]; exact h2

/--
  **Sub-case CLOSURE**: when chi(6), chi(9), chi(12) all distinct and
  chi(16) = chi(18) = chi(6), we get a contradiction via the (6, 16, 18)
  mono triple.

  This is the FIRST of the 4 sub-cases of "(6,9,12) distinct" successfully
  closed kernel-pure.
-/
theorem bAdicEquation_3_no_chi_16_18_both_eq_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_6 : χ 16 = χ 6) (h18_eq_6 : χ 18 = χ 6) :
    False := by
  apply bAdicEquation_3_rado_6_16_18 (n := n) χ (by omega) hNoMono
  refine ⟨?_, ?_⟩
  · exact h16_eq_6.symm
  · rw [h16_eq_6, h18_eq_6]

/--
  **Sub-case REDUCTION** (chi(16) = chi(18) sub-case): when chi(6), chi(9),
  chi(12) all distinct AND chi(16) = chi(18), they BOTH must equal chi(9)
  (NOT chi(6), which would give immediate mono via (6, 16, 18) triple).

  Reduces the "(6,9,12) distinct + chi(16) = chi(18)" sub-case to
  "chi(16) = chi(18) = chi(9)", which is the genuinely-open sub-case 4.
-/
theorem bAdicEquation_3_chi_16_18_eq_chi_9_when_16_eq_18
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_18 : χ 16 = χ 18) :
    χ 16 = χ 9 ∧ χ 18 = χ 9 := by
  have h16_in := bAdicEquation_3_chi_16_in_6_9_when_distinct (n := n) χ h24 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  rcases h16_in with h | h
  · -- chi(16) = chi(6). Then chi(18) = chi(16) = chi(6). Both = chi(6).
    -- Apply no_chi_16_18_both_eq_6 for contradiction.
    exfalso
    exact bAdicEquation_3_no_chi_16_18_both_eq_6 (n := n) χ h24 hNoMono h
      (h16_eq_18.symm.trans h)
  · -- chi(16) = chi(9). Then chi(18) = chi(16) = chi(9).
    exact ⟨h, h16_eq_18.symm.trans h⟩

/--
  **Sub-case REDUCTION** (chi(16) ≠ chi(18) sub-case): when chi(6), chi(9),
  chi(12) all distinct, chi(16) ≠ chi(18) implies chi(24) = chi(12).

  Proof: chi(16), chi(18) ∈ {chi(6), chi(9)} (by previous lemmas). If
  chi(16) ≠ chi(18), then {chi(16), chi(18)} = {chi(6), chi(9)} (as a
  2-set). chi(24) ≠ chi(16) AND chi(24) ≠ chi(18) (self-loop xz m=8 and
  xy m=6). So chi(24) ∉ {chi(6), chi(9)}. Combined with chi(24) < 3,
  this forces chi(24) = chi(12).
-/
theorem bAdicEquation_3_chi_24_eq_chi_12_when_16_18_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_ne_18 : χ 16 ≠ χ 18) :
    χ 24 = χ 12 := by
  have h16_in := bAdicEquation_3_chi_16_in_6_9_when_distinct (n := n) χ h24 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  have h18_in := bAdicEquation_3_chi_18_in_6_9_when_distinct (n := n) χ h24 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ h24 hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  -- chi(24) ≠ chi(6) (from one of h16_in, h18_in matching chi(6)).
  -- chi(24) ≠ chi(9) (similarly).
  -- So chi(24) = chi(12) by elimination.
  have h24_ne_6 : χ 24 ≠ χ 6 := by
    intro h24_eq_6
    rcases h16_in with h16eq | h16eq
    · -- chi(16) = chi(6) = chi(24). Contradicts chi(16) ≠ chi(24).
      apply h16_ne_24
      rw [h16eq, ← h24_eq_6]
    · -- chi(16) = chi(9). Then chi(18) = chi(6) (since chi(16) ≠ chi(18) and
      -- {chi(16),chi(18)} ⊆ {chi(6),chi(9)}).
      have h18eq6 : χ 18 = χ 6 := by
        rcases h18_in with h | h
        · exact h
        · exfalso; apply h16_ne_18; rw [h16eq, h]
      apply h18_ne_24
      rw [h18eq6, ← h24_eq_6]
  have h24_ne_9 : χ 24 ≠ χ 9 := by
    intro h24_eq_9
    rcases h16_in with h16eq | h16eq
    · -- chi(16) = chi(6). Then chi(18) = chi(9) (from chi(16) ≠ chi(18)).
      have h18eq9 : χ 18 = χ 9 := by
        rcases h18_in with h | h
        · exfalso; apply h16_ne_18; rw [h16eq, h]
        · exact h
      apply h18_ne_24
      rw [h18eq9, ← h24_eq_9]
    · -- chi(16) = chi(9) = chi(24). Contradicts chi(16) ≠ chi(24).
      apply h16_ne_24
      rw [h16eq, ← h24_eq_9]
  -- chi(24) < 3 AND chi(24) ≠ chi(6), chi(9), so chi(24) = chi(12).
  -- chi(6), chi(9), chi(12) all distinct + chi(24) < 3 + chi(24) ∉ {chi(6),chi(9)}
  -- implies chi(24) = chi(12).
  omega

/-! ### §52. CompressionHyp 3 3 — sub-case 4 forced constraints.

  When chi(16) = chi(18) = chi(9) AND (chi(6), chi(9), chi(12)) all distinct
  (the "stuck" sub-case 4), several chi values at OTHER positions are
  FORCED away from chi(9) by general Rado triples.

  Specifically: chi(10), chi(19), chi(21), chi(22) all ≠ chi(9).
-/

/--
  **chi(10) ≠ chi(9) when chi(16) = chi(9) AND chi(18) = chi(9)**.

  Direct from general Rado (18, 10, 16) at b=3, d=6, y=10: NOT (chi(18) =
  chi(10) AND chi(10) = chi(16)). Since chi(18) = chi(9) = chi(16), this
  forces chi(10) ≠ chi(9).
-/
theorem bAdicEquation_3_chi_10_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9) :
    χ 10 ≠ χ 9 := by
  intro h10_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 10) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 10
    rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h10_eq_9]
  · show χ 10 = χ (10 + 6)
    rw [show (10 + 6 : ℕ) = 16 by decide, h16_eq_9, ← h10_eq_9]

/--
  **chi(19) ≠ chi(9) when chi(16) = chi(9)**.

  Direct from general Rado (9, 16, 19) at b=3, d=3, y=16: NOT (chi(9) =
  chi(16) AND chi(16) = chi(19)). Since chi(9) = chi(16), this forces
  chi(19) ≠ chi(16) = chi(9).
-/
theorem bAdicEquation_3_chi_19_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 19 ≠ χ 9 := by
  intro h19_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 16
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h16_eq_9.symm
  · show χ 16 = χ (16 + 3)
    rw [show (16 + 3 : ℕ) = 19 by decide, h16_eq_9, ← h19_eq_9]

/--
  **chi(21) ≠ chi(9) when chi(18) = chi(9)**.

  Direct from general Rado (9, 18, 21) at b=3, d=3, y=18: NOT (chi(9) =
  chi(18) AND chi(18) = chi(21)). Since chi(9) = chi(18), this forces
  chi(21) ≠ chi(18) = chi(9).
-/
theorem bAdicEquation_3_chi_21_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h18_eq_9 : χ 18 = χ 9) :
    χ 21 ≠ χ 9 := by
  intro h21_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 18
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h18_eq_9.symm
  · show χ 18 = χ (18 + 3)
    rw [show (18 + 3 : ℕ) = 21 by decide, h18_eq_9, ← h21_eq_9]

/--
  **chi(22) ≠ chi(9) when chi(16) = chi(18) = chi(9)**.

  Direct from general Rado (18, 16, 22) at b=3, d=6, y=16: NOT (chi(18) =
  chi(16) AND chi(16) = chi(22)). Since chi(18) = chi(16) = chi(9), this
  forces chi(22) ≠ chi(16) = chi(9).
-/
theorem bAdicEquation_3_chi_22_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h22 : 22 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9) :
    χ 22 ≠ χ 9 := by
  intro h22_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 16
    rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h16_eq_9]
  · show χ 16 = χ (16 + 6)
    rw [show (16 + 6 : ℕ) = 22 by decide, h16_eq_9, ← h22_eq_9]

/--
  **chi(13) ≠ chi(9) when chi(16) = chi(9)**.

  Direct from general Rado (9, 13, 16) at b=3, d=3, y=13: NOT (chi(9) =
  chi(13) AND chi(13) = chi(16)). Since chi(9) = chi(16), this forces
  chi(13) ≠ chi(9).
-/
theorem bAdicEquation_3_chi_13_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 13 ≠ χ 9 := by
  intro h13_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 13
    rw [show (3 * 3 : ℕ) = 9 by decide, ← h13_eq_9]
  · show χ 13 = χ (13 + 3)
    rw [show (13 + 3 : ℕ) = 16 by decide, h16_eq_9, ← h13_eq_9]

/--
  **chi(15) ≠ chi(9) when chi(18) = chi(9)**.

  Direct from general Rado (18, 9, 15) at b=3, d=6, y=9: NOT (chi(18) =
  chi(9) AND chi(9) = chi(15)). Since chi(18) = chi(9), this forces
  chi(15) ≠ chi(9).
-/
theorem bAdicEquation_3_chi_15_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h18_eq_9 : χ 18 = χ 9) :
    χ 15 ≠ χ 9 := by
  intro h15_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 9
    rw [show (3 * 6 : ℕ) = 18 by decide]; exact h18_eq_9
  · show χ 9 = χ (9 + 6)
    rw [show (9 + 6 : ℕ) = 15 by decide]; exact h15_eq_9.symm

/--
  **BUNDLED sub-case 4 constraints**: when chi(16) = chi(18) = chi(9) AND
  the (6,9,12)-distinct hypothesis, the chi values at positions
    {10, 13, 15, 19, 21, 22}
  are all ≠ chi(9).

  This is the COMPLETE set of forced "chi at non-multiples-of-3 in [10, 22]
  ≠ chi(9)" constraints derivable directly from sub-case 4 hypothesis.
-/
theorem bAdicEquation_3_sub4_forced_ne_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h22 : 22 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9) :
    χ 10 ≠ χ 9 ∧ χ 13 ≠ χ 9 ∧ χ 15 ≠ χ 9 ∧
    χ 19 ≠ χ 9 ∧ χ 21 ≠ χ 9 ∧ χ 22 ≠ χ 9 :=
  ⟨bAdicEquation_3_chi_10_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9 h18_eq_9,
   bAdicEquation_3_chi_13_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9,
   bAdicEquation_3_chi_15_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h18_eq_9,
   bAdicEquation_3_chi_19_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9,
   bAdicEquation_3_chi_21_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h18_eq_9,
   bAdicEquation_3_chi_22_ne_chi_9_in_sub4 (n := n) χ h22 hNoMono h16_eq_9 h18_eq_9⟩

/--
  **chi(8) = chi(9) under sub-case 4 + (6,9,12) distinct**.

  Logic: chi(8) ≠ chi(6) (self-loop xy m=2). chi(8) ≠ chi(12) (self-loop xz m=4).
  chi(8) < 3 + (6,9,12) distinct + chi(8) ∉ {chi(6), chi(12)} ⇒ chi(8) = chi(9).

  Holds in ALL of sub-case 4 (no dependence on Case A/B split).
-/
theorem bAdicEquation_3_chi_8_eq_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12) :
    χ 8 = χ 9 := by
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(8) ≠ chi(6): from self-loop xy m=2.
  have h6_ne_8 : χ 6 ≠ χ 8 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 2) (by omega) (by omega)
    show χ (3 * 2) ≠ χ (4 * 2); exact h
  -- chi(8) ≠ chi(12): from self-loop xz m=4.
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  omega

/--
  **chi(11) ≠ chi(9) under sub-case 4 + chi(8) = chi(9)**.

  Direct from (9, 8, 11) Rado triple: NOT (chi(9) = chi(8) AND chi(8) =
  chi(11)). Since chi(8) = chi(9), this forces chi(11) ≠ chi(8) = chi(9).
-/
theorem bAdicEquation_3_chi_11_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h11 : 11 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h8_eq_9 : χ 8 = χ 9) :
    χ 11 ≠ χ 9 := by
  intro h11_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 8
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h8_eq_9.symm
  · show χ 8 = χ (8 + 3)
    rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_9, ← h11_eq_9]

/--
  **chi(5) ≠ chi(9) under sub-case 4 + chi(8) = chi(9)**.

  Direct from (9, 5, 8) Rado triple: NOT (chi(9) = chi(5) AND chi(5) =
  chi(8)). Since chi(8) = chi(9), this forces chi(5) ≠ chi(8) = chi(9).
-/
theorem bAdicEquation_3_chi_5_ne_chi_9_in_sub4
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h8_eq_9 : χ 8 = χ 9) :
    χ 5 ≠ χ 9 := by
  intro h5_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 5
    rw [show (3 * 3 : ℕ) = 9 by decide, ← h5_eq_9]
  · show χ 5 = χ (5 + 3)
    rw [show (5 + 3 : ℕ) = 8 by decide, h8_eq_9, ← h5_eq_9]

/--
  **chi(4) = chi(9) under (6,9,12) distinct + chi(24) = chi(12)**.

  REUSABLE foundational lemma for sub-cases 2, 3, and 4b. Independent of
  chi(16)/chi(18) configuration.

  Logic: chi(4) ≠ chi(6) (self-loop xz m=2). chi(4) ≠ chi(12) (from
  (24, 4, 12) Rado triple with chi(24) = chi(12), avoid (12, 4, 12) mono
  pattern). chi(4) < 3 ⇒ chi(4) = chi(9).
-/
theorem bAdicEquation_3_chi_4_eq_9_when_chi_24_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h24_eq_12 : χ 24 = χ 12) :
    χ 4 = χ 9 := by
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(4) ≠ chi(6): from self-loop xz m=2.
  have h4_ne_6 : χ 4 ≠ χ 6 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 2) (by omega) (by omega)
    show χ (2 * 2) ≠ χ (3 * 2); exact h
  -- chi(4) ≠ chi(12): from (24, 4, 12) Rado triple at d=8, y=4.
  have h4_ne_12 : χ 4 ≠ χ 12 := by
    intro h4_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 4
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide, ← h4_eq_12]
  omega

/--
  **chi(15) ≠ chi(9) under chi(4) = chi(9)** (reusable).

  Direct from (15, 4, 9) Rado triple at d=5, y=4: NOT (chi(15) = chi(4)
  AND chi(4) = chi(9)). Since chi(4) = chi(9), this forces chi(15) ≠
  chi(4) = chi(9).
-/
theorem bAdicEquation_3_chi_15_ne_chi_9_when_chi_4_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h4_eq_9 : χ 4 = χ 9) :
    χ 15 ≠ χ 9 := by
  intro h15_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 4) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 4
    rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_9, ← h4_eq_9]
  · show χ 4 = χ (4 + 5)
    rw [show (4 + 5 : ℕ) = 9 by decide]; exact h4_eq_9

/--
  **chi(20) = chi(9) under chi(18) = chi(6) + chi(24) = chi(12) + (6,9,12)
  distinct**. REUSABLE foundational lemma for sub-case 3.

  Logic:
  - chi(20) ≠ chi(6): from (6, 18, 20) Rado triple at d=2, y=18 (chi(18) = chi(6)).
  - chi(20) ≠ chi(12): from (12, 20, 24) Rado triple at d=4, y=20 (chi(24) = chi(12)).
  - chi(20) < 3 ⇒ chi(20) = chi(9).
-/
theorem bAdicEquation_3_chi_20_eq_9_when_chi_18_eq_6_chi_24_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h18_eq_6 : χ 18 = χ 6) (h24_eq_12 : χ 24 = χ 12) :
    χ 20 = χ 9 := by
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(20) ≠ chi(6): from (6, 18, 20) Rado triple.
  have h20_ne_6 : χ 20 ≠ χ 6 := by
    intro h20_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 18
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h18_eq_6.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_6, ← h20_eq_6]
  -- chi(20) ≠ chi(12): from (12, 20, 24) Rado triple.
  have h20_ne_12 : χ 20 ≠ χ 12 := by
    intro h20_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 20
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h20_eq_12]
    · show χ 20 = χ (20 + 4)
      rw [show (20 + 4 : ℕ) = 24 by decide, h24_eq_12, ← h20_eq_12]
  omega

/--
  **chi(13) ≠ chi(9) when chi(16) = chi(9)** (REUSABLE for sub-case 2, 3, 4).

  Direct from (9, 13, 16) Rado triple at d=3, y=13: NOT (chi(9) = chi(13)
  AND chi(13) = chi(16)). Since chi(16) = chi(9), this forces chi(13) ≠
  chi(16) = chi(9).
-/
theorem bAdicEquation_3_chi_13_ne_chi_9_when_chi_16_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 13 ≠ χ 9 := by
  intro h13_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 13
    rw [show (3 * 3 : ℕ) = 9 by decide, ← h13_eq_9]
  · show χ 13 = χ (13 + 3)
    rw [show (13 + 3 : ℕ) = 16 by decide, h16_eq_9, ← h13_eq_9]

/--
  **chi(19) ≠ chi(9) when chi(16) = chi(9)** (REUSABLE).

  Direct from (9, 16, 19) Rado triple at d=3, y=16: NOT (chi(9) = chi(16)
  AND chi(16) = chi(19)). Since chi(16) = chi(9), this forces chi(19) ≠
  chi(16) = chi(9).
-/
theorem bAdicEquation_3_chi_19_ne_chi_9_when_chi_16_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 19 ≠ χ 9 := by
  intro h19_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 16
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h16_eq_9.symm
  · show χ 16 = χ (16 + 3)
    rw [show (16 + 3 : ℕ) = 19 by decide, h16_eq_9, ← h19_eq_9]

/-! ### §53. CompressionHyp 3 3 — sub-case 4 + Case B closure (toward).

  Case B = chi(10) = chi(12) AND chi(15) = chi(6) (one of the 2 alternatives
  from chi(10) ≠ chi(15) AND chi(10), chi(15) ∈ {chi(6), chi(12)}).

  Strategy: derive chain
    chi(13) = chi(12) → chi(17) = chi(9) → chi(14) = chi(6) →
    chi(21) = chi(12) → chi(19) = chi(12) → chi(20) = chi(9 or 12)
  Then in sub-sub-case 4b (chi(24) = chi(12)), chi(20) = chi(9) → (9, 17, 20)
  mono triple. In sub-sub-case 4a (chi(24) = chi(6)), chi(20) = chi(12)
  forces deeper analysis.
-/

/--
  **Step 1**: chi(13) = chi(12) under sub-case 4 + Case B.

  Logic: chi(13) ∈ {chi(6), chi(12)} (sub-case 4). If chi(13) = chi(6),
  then (3*2, 13, 15) = (6, 13, 15) is mono since chi(6) = chi(13) = chi(15)
  = chi(6).
-/
theorem bAdicEquation_3_chi_13_eq_12_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h15_eq_6 : χ 15 = χ 6) :
    χ 13 = χ 12 := by
  have h13_ne_9 : χ 13 ≠ χ 9 :=
    bAdicEquation_3_chi_13_ne_chi_9_in_sub4 (n := n) χ h16 hNoMono h16_eq_9
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(13) ∈ {chi(6), chi(12)} (since chi(13) < 3 and ≠ chi(9)).
  -- If chi(13) = chi(6), then (6, 13, 15) gives mono.
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    -- (6, 13, 15) Rado triple via general Rado (b=3, d=2, y=13).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 13
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h13_eq_6.symm
    · show χ 13 = χ (13 + 2)
      rw [show (13 + 2 : ℕ) = 15 by decide, h15_eq_6, ← h13_eq_6]
  -- chi(13) < 3 + chi(13) ≠ chi(6), chi(9), and chi(6), chi(9), chi(12) distinct.
  omega

/--
  **Step 2**: chi(17) = chi(9) under sub-case 4 + Case B + Step 1.

  Logic: chi(17) ∈ {0, 1, 2}. (12, 13, 17) Rado triple says
  NOT (chi(12) = chi(13) = chi(17)). chi(13) = chi(12) (Step 1), so
  chi(17) ≠ chi(12). (6, 15, 17) Rado triple says NOT (chi(6) = chi(15) =
  chi(17)). chi(15) = chi(6), so chi(17) ≠ chi(6). Hence chi(17) = chi(9).
-/
theorem bAdicEquation_3_chi_17_eq_9_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h17 : 17 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h15_eq_6 : χ 15 = χ 6) (h13_eq_12 : χ 13 = χ 12) :
    χ 17 = χ 9 := by
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(17) ≠ chi(12): from (12, 13, 17) Rado triple.
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 13
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h13_eq_12.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h17_eq_12, ← h13_eq_12]
  -- chi(17) ≠ chi(6): from (6, 15, 17) Rado triple.
  have h17_ne_6 : χ 17 ≠ χ 6 := by
    intro h17_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 15
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h15_eq_6.symm
    · show χ 15 = χ (15 + 2)
      rw [show (15 + 2 : ℕ) = 17 by decide, h17_eq_6, ← h15_eq_6]
  -- chi(17) < 3, ≠ chi(6), ≠ chi(12), and (chi(6),chi(9),chi(12)) distinct.
  omega

/--
  **Step 3**: chi(14) = chi(6) under sub-case 4 + Case B.

  Logic: chi(14) ≠ chi(9) from (9, 14, 17) since chi(17) = chi(9). Then
  chi(14) ∈ {chi(6), chi(12)}. chi(14) ≠ chi(12) from (12, 10, 14) since
  chi(10) = chi(12). Hence chi(14) = chi(6).
-/
theorem bAdicEquation_3_chi_14_eq_6_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h17 : 17 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h10_eq_12 : χ 10 = χ 12) (h17_eq_9 : χ 17 = χ 9) :
    χ 14 = χ 6 := by
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(14) ≠ chi(9): from (9, 14, 17) Rado triple (chi(17) = chi(9)).
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 14
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h14_eq_9]
    · show χ 14 = χ (14 + 3)
      rw [show (14 + 3 : ℕ) = 17 by decide, h17_eq_9, ← h14_eq_9]
  -- chi(14) ≠ chi(12): from (12, 10, 14) Rado triple (chi(10) = chi(12)).
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 10
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h10_eq_12.symm
    · show χ 10 = χ (10 + 4)
      rw [show (10 + 4 : ℕ) = 14 by decide, h14_eq_12, ← h10_eq_12]
  -- chi(14) < 3, ≠ chi(9), ≠ chi(12), and (chi(6),chi(9),chi(12)) distinct.
  omega

/--
  **Step 4**: chi(21) = chi(12) under sub-case 4 + Case B + Step 3.

  Logic: chi(21) ≠ chi(9) (from sub-case 4). chi(21) ≠ chi(14) (self-loop
  xz m=7). chi(14) = chi(6) (Step 3) so chi(21) ≠ chi(6). Hence chi(21) =
  chi(12).
-/
theorem bAdicEquation_3_chi_21_eq_12_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h18_eq_9 : χ 18 = χ 9) (h14_eq_6 : χ 14 = χ 6) :
    χ 21 = χ 12 := by
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h21_ne_9 : χ 21 ≠ χ 9 :=
    bAdicEquation_3_chi_21_ne_chi_9_in_sub4 (n := n) χ h21 hNoMono h18_eq_9
  -- chi(14) ≠ chi(21) from self-loop xz m=7.
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  -- chi(21) ≠ chi(6) (since chi(14) = chi(6) and chi(14) ≠ chi(21)).
  have h21_ne_6 : χ 21 ≠ χ 6 := by intro h; apply h14_ne_21; rw [h14_eq_6, ← h]
  omega

/--
  **Step 5**: chi(19) = chi(12) under sub-case 4 + Case B + Step 3.

  Logic: chi(19) ≠ chi(9) (sub-case 4). (15, 14, 19) Rado: NOT (chi(15) =
  chi(14) AND chi(14) = chi(19)). chi(15) = chi(6) = chi(14), so chi(19) ≠
  chi(14) = chi(6). Hence chi(19) = chi(12).
-/
theorem bAdicEquation_3_chi_19_eq_12_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h15_eq_6 : χ 15 = χ 6) (h14_eq_6 : χ 14 = χ 6) :
    χ 19 = χ 12 := by
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h19_ne_9 : χ 19 ≠ χ 9 :=
    bAdicEquation_3_chi_19_ne_chi_9_in_sub4 (n := n) χ h19 hNoMono h16_eq_9
  -- chi(19) ≠ chi(6): from (15, 14, 19) Rado triple (3d=15, d=5, y=14).
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 14
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_6, ← h14_eq_6]
    · show χ 14 = χ (14 + 5)
      rw [show (14 + 5 : ℕ) = 19 by decide, h19_eq_6, ← h14_eq_6]
  omega

/--
  **CLOSURE for sub-sub-case 4b under Case B**: when chi(16) = chi(18) =
  chi(9), chi(10) = chi(12), chi(15) = chi(6), chi(24) = chi(12), we have
  chi(17) = chi(9) (Step 2). Self-loop chain gives chi(15) ≠ chi(20), so
  chi(20) ≠ chi(6). chi(20) ≠ chi(12) (else (12, 20, 24) mono since chi(24) =
  chi(12)). So chi(20) = chi(9). Then (9, 17, 20) is mono. Contradiction.
-/
theorem bAdicEquation_3_sub4_caseB_4b_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h10_eq_12 : χ 10 = χ 12) (h15_eq_6 : χ 15 = χ 6)
    (h24_eq_12 : χ 24 = χ 12) :
    False := by
  -- Step 1: chi(13) = chi(12).
  have h13_eq_12 := bAdicEquation_3_chi_13_eq_12_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h15_eq_6
  -- Step 2: chi(17) = chi(9).
  have h17_eq_9 := bAdicEquation_3_chi_17_eq_9_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h15_eq_6 h13_eq_12
  -- chi(20) < 3 + ≠ chi(6), chi(12), chi(9) — wait need to compute.
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(20) ≠ chi(6): from self-loop xy m=5 (chi(15) ≠ chi(20)).
  have h15_ne_20 : χ 15 ≠ χ 20 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (3 * 5) ≠ χ (4 * 5); exact h
  have h20_ne_6 : χ 20 ≠ χ 6 := by intro h; apply h15_ne_20; rw [h15_eq_6, ← h]
  -- chi(20) ≠ chi(12): from (12, 20, 24) Rado triple (chi(24) = chi(12)).
  have h20_ne_12 : χ 20 ≠ χ 12 := by
    intro h20_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 20
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h20_eq_12]
    · show χ 20 = χ (20 + 4)
      rw [show (20 + 4 : ℕ) = 24 by decide, h24_eq_12, ← h20_eq_12]
  -- So chi(20) = chi(9).
  have h20_eq_9 : χ 20 = χ 9 := by omega
  -- (9, 17, 20) Rado triple: chi(9) = chi(17) = chi(20). All = chi(9). MONO.
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 17
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h17_eq_9.symm
  · show χ 17 = χ (17 + 3)
    rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_9, h20_eq_9]

/-! ### §54. CompressionHyp 3 3 — sub-case 4a + Case B closure.

  In sub-sub-case 4a (chi(24) = chi(6)) + Case B (chi(10) = chi(12),
  chi(15) = chi(6)), the closure proceeds via:
    Step 1-5: chi(13) = chi(12), chi(17) = chi(9), chi(14) = chi(6),
              chi(19) = chi(12), chi(21) = chi(12) (same as 4b).
    Step 6: chi(23) = chi(6) [via chi(23) ≠ chi(12), chi(23) ≠ chi(9)].
    Closure: (24, 15, 23) mono triple — chi(24) = chi(15) = chi(23) = chi(6).
-/

/--
  **Step 6** (4a-specific): chi(23) = chi(6) under sub-case 4 + Case B + Step 5.

  Logic: chi(23) ≠ chi(12) from (12, 19, 23) Rado triple since chi(19) = chi(12).
  chi(23) ≠ chi(9) from (18, 17, 23) Rado triple since chi(17) = chi(18) = chi(9).
  Hence chi(23) = chi(6).
-/
theorem bAdicEquation_3_chi_23_eq_6_in_sub4_caseB
    {n : ℕ} (χ : ℕ → ℕ) (h23 : 23 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h17_eq_9 : χ 17 = χ 9) (h18_eq_9 : χ 18 = χ 9) (h19_eq_12 : χ 19 = χ 12) :
    χ 23 = χ 6 := by
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(23) ≠ chi(12): from (12, 19, 23) Rado triple.
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 19
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h19_eq_12.symm
    · show χ 19 = χ (19 + 4)
      rw [show (19 + 4 : ℕ) = 23 by decide, h23_eq_12, ← h19_eq_12]
  -- chi(23) ≠ chi(9): from (18, 17, 23) Rado triple.
  have h23_ne_9 : χ 23 ≠ χ 9 := by
    intro h23_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 17
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 6)
      rw [show (17 + 6 : ℕ) = 23 by decide, h17_eq_9, ← h23_eq_9]
  omega

/--
  **CLOSURE for sub-sub-case 4a under Case B**: when chi(16) = chi(18) =
  chi(9), chi(10) = chi(12), chi(15) = chi(6), chi(24) = chi(6), we derive
  the contradiction via the (24, 15, 23) mono triple.

  All three chi values are forced to chi(6):
  - chi(24) = chi(6) (4a hypothesis)
  - chi(15) = chi(6) (Case B hypothesis)
  - chi(23) = chi(6) (Step 6, derived above)

  Hence (24, 15, 23) is monochromatic, contradicting mono-freeness.
-/
theorem bAdicEquation_3_sub4_caseB_4a_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h10_eq_12 : χ 10 = χ 12) (h15_eq_6 : χ 15 = χ 6)
    (h24_eq_6 : χ 24 = χ 6) :
    False := by
  -- Step 1: chi(13) = chi(12).
  have h13_eq_12 := bAdicEquation_3_chi_13_eq_12_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h15_eq_6
  -- Step 2: chi(17) = chi(9).
  have h17_eq_9 := bAdicEquation_3_chi_17_eq_9_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h15_eq_6 h13_eq_12
  -- Step 3: chi(14) = chi(6).
  have h14_eq_6 := bAdicEquation_3_chi_14_eq_6_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h10_eq_12 h17_eq_9
  -- Step 5: chi(19) = chi(12).
  have h19_eq_12 := bAdicEquation_3_chi_19_eq_12_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h15_eq_6 h14_eq_6
  -- Step 6: chi(23) = chi(6).
  have h23_eq_6 := bAdicEquation_3_chi_23_eq_6_in_sub4_caseB (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h17_eq_9 h18_eq_9 h19_eq_12
  -- Closure: (24, 15, 23) all = chi(6) is mono via general Rado d=8, y=15.
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 15) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 15
    rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_6, ← h15_eq_6]
  · show χ 15 = χ (15 + 8)
    rw [show (15 + 8 : ℕ) = 23 by decide, h15_eq_6, ← h23_eq_6]

/--
  **FULL CLOSURE of sub-case 4 under Case B**: when chi(16) = chi(18) = chi(9)
  AND chi(10) = chi(12), chi(15) = chi(6), the chi values force a mono triple
  in BOTH sub-sub-cases:
    - 4a (chi(24) = chi(6)): mono via (24, 15, 23).
    - 4b (chi(24) = chi(12)): mono via (9, 17, 20) or (12, 20, 24).

  Combines the two sub-sub-case closures into a single contradiction lemma.
-/
theorem bAdicEquation_3_sub4_caseB_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h10_eq_12 : χ 10 = χ 12) (h15_eq_6 : χ 15 = χ 6) :
    False := by
  -- chi(24) ∈ {chi(6), chi(12)} (from sub-case 4 constraints):
  -- chi(24) ≠ chi(18) = chi(9) (self-loop xy m=6).
  -- chi(24) < 3.
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have h24_ne_9 : χ 24 ≠ χ 9 := by intro h; apply h18_ne_24; rw [h18_eq_9, ← h]
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(24) is one of chi(6), chi(12).
  have h24_eq_or : χ 24 = χ 6 ∨ χ 24 = χ 12 := by omega
  rcases h24_eq_or with h24_eq_6 | h24_eq_12
  · -- Sub-sub-case 4a.
    exact bAdicEquation_3_sub4_caseB_4a_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h10_eq_12 h15_eq_6 h24_eq_6
  · -- Sub-sub-case 4b.
    exact bAdicEquation_3_sub4_caseB_4b_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h10_eq_12 h15_eq_6 h24_eq_12

/-! ### §55. CompressionHyp 3 3 — sub-case 4 + Case A closures.

  Case A = chi(10) = chi(6) AND chi(15) = chi(12). The OTHER assignment from
  chi(10) ≠ chi(15) AND chi(10), chi(15) ∈ {chi(6), chi(12)}.

  In Case A, chi(17) ≠ chi(12) (from (15, 12, 17) Rado triple). So chi(17)
  splits into two sub-sub-cases:
    A-I: chi(17) = chi(6)
    A-II: chi(17) = chi(9)

  Each sub-sub-case combines with chi(24) ∈ {chi(6), chi(12)} (4a/4b) to
  give 4 sub-sub-sub-cases (A-I × 4a, A-I × 4b, A-II × 4a, A-II × 4b).
-/

/--
  **A-I closure (independent of 4a/4b)**: when chi(15) = chi(12), chi(17) =
  chi(6) AND chi(16) = chi(9), chi(19) has no valid value in {0, 1, 2}:
  - chi(19) ≠ chi(9): sub-case 4 forced (from (9, 16, 19) since chi(16) = chi(9)).
  - chi(19) ≠ chi(6): from (6, 17, 19) Rado triple since chi(17) = chi(6).
  - chi(19) ≠ chi(12): from (12, 15, 19) Rado triple since chi(15) = chi(12).

  Closes BOTH 4a + A-I and 4b + A-I in one shot.
-/
theorem bAdicEquation_3_chi_19_impossible_in_sub4_caseA_AI
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9)
    (h15_eq_12 : χ 15 = χ 12)
    (h17_eq_6 : χ 17 = χ 6) :
    False := by
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(19) ≠ chi(9): from sub4 lemma.
  have h19_ne_9 : χ 19 ≠ χ 9 :=
    bAdicEquation_3_chi_19_ne_chi_9_in_sub4 (n := n) χ h19 hNoMono h16_eq_9
  -- chi(19) ≠ chi(6): from (6, 17, 19) Rado triple.
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 17
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h17_eq_6.symm
    · show χ 17 = χ (17 + 2)
      rw [show (17 + 2 : ℕ) = 19 by decide, h17_eq_6, ← h19_eq_6]
  -- chi(19) ≠ chi(12): from (12, 15, 19) Rado triple.
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 15
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h15_eq_12.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h19_eq_12, ← h15_eq_12]
  -- chi(19) < 3 + ≠ chi(6), chi(9), chi(12) ⇒ no valid value.
  omega

/--
  **A-II + 4a closure**: when chi(15) = chi(12), chi(17) = chi(9), chi(24) =
  chi(6), the chain
    chi(8) = chi(9) → chi(14) = chi(12) → chi(21) = chi(6) → chi(19) impossible
  derives contradiction.

  Chain details:
  - chi(8) = chi(9): foundational sub-case 4 lemma.
  - chi(14) ≠ chi(9): from (18, 8, 14) Rado triple.
  - chi(14) ≠ chi(6): from (24, 6, 14) Rado triple (4a).
  - chi(14) = chi(12) (only remaining).
  - chi(21) ≠ chi(14) = chi(12): self-loop xz m=7.
  - chi(21) ≠ chi(9): sub-case 4.
  - chi(21) = chi(6).
  - chi(19) ≠ chi(9): sub-case 4.
  - chi(19) ≠ chi(12): (12, 15, 19) Rado.
  - chi(19) ≠ chi(6): (6, 19, 21) Rado, chi(21) = chi(6).
  - All 3 forbidden ⇒ chi(19) impossible.
-/
theorem bAdicEquation_3_sub4_caseA_AII_4a_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h15_eq_12 : χ 15 = χ 12) (h17_eq_9 : χ 17 = χ 9) (h24_eq_6 : χ 24 = χ 6) :
    False := by
  -- chi(8) = chi(9).
  have h8_eq_9 := bAdicEquation_3_chi_8_eq_9_in_sub4 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  -- chi(14) ≠ chi(9): from (18, 8, 14) Rado triple.
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 8
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h8_eq_9]
    · show χ 8 = χ (8 + 6)
      rw [show (8 + 6 : ℕ) = 14 by decide, h8_eq_9, ← h14_eq_9]
  -- chi(14) ≠ chi(6): from (24, 6, 14) Rado triple in 4a.
  have h14_ne_6 : χ 14 ≠ χ 6 := by
    intro h14_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 6
      rw [show (3 * 8 : ℕ) = 24 by decide]; exact h24_eq_6
    · show χ 6 = χ (6 + 8)
      rw [show (6 + 8 : ℕ) = 14 by decide]; exact h14_eq_6.symm
  -- chi(14) = chi(12).
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h14_eq_12 : χ 14 = χ 12 := by omega
  -- chi(21) ≠ chi(14) = chi(12) via self-loop xz m=7.
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  have h21_ne_12 : χ 21 ≠ χ 12 := by intro h; apply h14_ne_21; rw [h14_eq_12, ← h]
  -- chi(21) ≠ chi(9) sub4.
  have h21_ne_9 : χ 21 ≠ χ 9 :=
    bAdicEquation_3_chi_21_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h18_eq_9
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have h21_eq_6 : χ 21 = χ 6 := by omega
  -- chi(19) impossibility.
  have h19_ne_9 : χ 19 ≠ χ 9 :=
    bAdicEquation_3_chi_19_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 15
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h15_eq_12.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h19_eq_12, ← h15_eq_12]
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 19
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h19_eq_6]
    · show χ 19 = χ (19 + 2)
      rw [show (19 + 2 : ℕ) = 21 by decide, h19_eq_6, h21_eq_6]
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  omega

/--
  **A-II + 4b closure**: when chi(15) = chi(12), chi(17) = chi(9), chi(24) =
  chi(12), the chain
    chi(19) = chi(6) → chi(21) = chi(12) → chi(13) = chi(6) → chi(11) = chi(12)
  ends in (12, 11, 15) mono triple since chi(11) = chi(12) = chi(15).
-/
theorem bAdicEquation_3_sub4_caseA_AII_4b_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h15_eq_12 : χ 15 = χ 12) (h17_eq_9 : χ 17 = χ 9) (h24_eq_12 : χ 24 = χ 12) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(19) = chi(6).
  have h19_ne_9 : χ 19 ≠ χ 9 :=
    bAdicEquation_3_chi_19_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 15
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h15_eq_12.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h19_eq_12, ← h15_eq_12]
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have h19_eq_6 : χ 19 = χ 6 := by omega
  -- chi(21) = chi(12).
  have h21_ne_9 : χ 21 ≠ χ 9 :=
    bAdicEquation_3_chi_21_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h18_eq_9
  have h21_ne_6 : χ 21 ≠ χ 6 := by
    intro h21_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 19
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h19_eq_6]
    · show χ 19 = χ (19 + 2)
      rw [show (19 + 2 : ℕ) = 21 by decide, h19_eq_6, ← h21_eq_6]
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have h21_eq_12 : χ 21 = χ 12 := by omega
  -- chi(13) = chi(6).
  have h13_ne_9 : χ 13 ≠ χ 9 :=
    bAdicEquation_3_chi_13_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 13
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h13_eq_12]
    · show χ 13 = χ (13 + 8)
      rw [show (13 + 8 : ℕ) = 21 by decide, h21_eq_12, ← h13_eq_12]
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have h13_eq_6 : χ 13 = χ 6 := by omega
  -- chi(11) = chi(12).
  have h8_eq_9 := bAdicEquation_3_chi_8_eq_9_in_sub4 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  have h11_ne_9 : χ 11 ≠ χ 9 :=
    bAdicEquation_3_chi_11_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 11
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h11_eq_6]
    · show χ 11 = χ (11 + 2)
      rw [show (11 + 2 : ℕ) = 13 by decide, h13_eq_6, ← h11_eq_6]
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have h11_eq_12 : χ 11 = χ 12 := by omega
  -- Closure: (12, 11, 15) mono via chi(11) = chi(15) = chi(12).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 11
    rw [show (3 * 4 : ℕ) = 12 by decide, ← h11_eq_12]
  · show χ 11 = χ (11 + 4)
    rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_12, ← h15_eq_12]

/--
  **FULL CLOSURE of sub-case 4 + Case A + A-II**: combines 4a + A-II and
  4b + A-II via chi(24) case split.
-/
theorem bAdicEquation_3_sub4_caseA_AII_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h15_eq_12 : χ 15 = χ 12) (h17_eq_9 : χ 17 = χ 9) :
    False := by
  -- chi(24) ∈ {chi(6), chi(12)}.
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have h24_ne_9 : χ 24 ≠ χ 9 := by intro h; apply h18_ne_24; rw [h18_eq_9, ← h]
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h24_or : χ 24 = χ 6 ∨ χ 24 = χ 12 := by omega
  rcases h24_or with h24_eq_6 | h24_eq_12
  · exact bAdicEquation_3_sub4_caseA_AII_4a_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h15_eq_12 h17_eq_9 h24_eq_6
  · exact bAdicEquation_3_sub4_caseA_AII_4b_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h15_eq_12 h17_eq_9 h24_eq_12

/--
  **FULL CLOSURE of Case A** under sub-case 4: combines A-I and A-II via
  chi(17) ∈ {chi(6), chi(9)} split.

  chi(17) ≠ chi(12) is FORCED by (15, 12, 17) Rado triple (chi(15) = chi(12)).
  So chi(17) ∈ {chi(6), chi(9)}.
  - chi(17) = chi(6): A-I closes via chi(19) impossibility.
  - chi(17) = chi(9): A-II closes via (4a: chi(19) impossible, 4b: (12,11,15) mono).
-/
theorem bAdicEquation_3_sub4_caseA_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9)
    (h10_eq_6 : χ 10 = χ 6) (h15_eq_12 : χ 15 = χ 12) :
    False := by
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(17) ≠ chi(12) from (15, 12, 17) Rado triple.
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 12
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  -- chi(17) ∈ {chi(6), chi(9)}.
  have h17_or : χ 17 = χ 6 ∨ χ 17 = χ 9 := by omega
  rcases h17_or with h17_eq_6 | h17_eq_9
  · -- A-I closure.
    exact bAdicEquation_3_chi_19_impossible_in_sub4_caseA_AI (n := n) χ (by omega) hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h15_eq_12 h17_eq_6
  · -- A-II closure.
    exact bAdicEquation_3_sub4_caseA_AII_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h15_eq_12 h17_eq_9

/-! ### §56. CompressionHyp 3 3 — sub-case 4 FULL CLOSURE.

  Combines Case A and Case B via chi(10)/chi(15) split.
  chi(10), chi(15) ∈ {chi(6), chi(12)} (from sub4 chi(10), chi(15) ≠ chi(9)
  + chi(10), chi(15) < 3 + (6,9,12) distinct).
  chi(10) ≠ chi(15) (self-loop xz m=5).
  So {chi(10), chi(15)} = {chi(6), chi(12)} as a set, giving two assignments:
  - Case A: chi(10) = chi(6), chi(15) = chi(12).
  - Case B: chi(10) = chi(12), chi(15) = chi(6).
-/

/--
  **MASTER THEOREM (sub-case 4 FULL CLOSURE)**: NO mono-free 3-coloring χ of
  [1, n] (n ≥ 24) for bAdicEquation 3 has chi(16) = chi(18) = chi(9) when
  chi(6), chi(9), chi(12) are all distinct.

  Bundles Case A and Case B closures into a single theorem. Eliminates
  sub-case 4 of the "(6,9,12) all distinct" branch in the CompressionHyp 3 3
  attack.

  KERNEL-PURE (only [propext, Classical.choice, Quot.sound]).
-/
theorem bAdicEquation_3_sub4_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_9 : χ 18 = χ 9) :
    False := by
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h10_ne_9 : χ 10 ≠ χ 9 :=
    bAdicEquation_3_chi_10_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9 h18_eq_9
  have h15_ne_9 : χ 15 ≠ χ 9 :=
    bAdicEquation_3_chi_15_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h18_eq_9
  -- chi(10) ≠ chi(15) from self-loop xz m=5.
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  -- chi(10), chi(15) ∈ {chi(6), chi(12)}, distinct.
  -- Case split.
  have h_assign : (χ 10 = χ 6 ∧ χ 15 = χ 12) ∨ (χ 10 = χ 12 ∧ χ 15 = χ 6) := by omega
  rcases h_assign with ⟨h10_eq_6, h15_eq_12⟩ | ⟨h10_eq_12, h15_eq_6⟩
  · -- Case A.
    exact bAdicEquation_3_sub4_caseA_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h10_eq_6 h15_eq_12
  · -- Case B.
    exact bAdicEquation_3_sub4_caseB_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9 h10_eq_12 h15_eq_6

/-! ### §57. CompressionHyp 3 3 — sub-case 3 FULL CLOSURE.

  Sub-case 3 = (chi(16) = chi(9), chi(18) = chi(6)) + chi(24) = chi(12)
  (chi(16) ≠ chi(18) sub-case forced chi(24) = chi(12) via R+201).

  Closes via chi(15) split:
  - 3-α (chi(15) = chi(6)): chi(17) impossible (all 3 values forced
    mono via (6,15,17), (9,17,20), (12,13,17) triples).
  - 3-β (chi(15) = chi(12)): chi(23) impossible (all 3 values forced
    mono via (24,15,23), (9,20,23), (18,17,23) triples).
-/

/--
  **Sub-case 3-α closure**: chi(17) is impossible when chi(15) = chi(6) AND
  chi(11) = chi(12) AND chi(13) = chi(12) AND chi(20) = chi(9).

  - chi(17) = chi(6): mono via (6, 15, 17) since chi(15) = chi(6).
  - chi(17) = chi(9): mono via (9, 17, 20) since chi(20) = chi(9).
  - chi(17) = chi(12): mono via (12, 13, 17) since chi(13) = chi(12).
-/
theorem bAdicEquation_3_sub3_alpha_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_6 : χ 18 = χ 6) (h24_eq_12 : χ 24 = χ 12)
    (h15_eq_6 : χ 15 = χ 6) :
    False := by
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(20) = chi(9) (foundational).
  have h20_eq_9 := bAdicEquation_3_chi_20_eq_9_when_chi_18_eq_6_chi_24_eq_12 (n := n) χ h24
    hχk hNoMono h6_ne_9 h6_ne_12 h9_ne_12 h18_eq_6 h24_eq_12
  -- chi(8) = chi(9) (foundational).
  have h8_eq_9 := bAdicEquation_3_chi_8_eq_9_in_sub4 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  -- chi(11) ≠ chi(9) (foundational).
  have h11_ne_9 :=
    bAdicEquation_3_chi_11_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  -- chi(13) ≠ chi(9) (from chi(16) = chi(9)).
  have h13_ne_9 :=
    bAdicEquation_3_chi_13_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono h16_eq_9
  -- chi(11) ≠ chi(6) (from (15, 6, 11) Rado triple, chi(15) = chi(6)).
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 6
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_6
    · show χ 6 = χ (6 + 5)
      rw [show (6 + 5 : ℕ) = 11 by decide]; exact h11_eq_6.symm
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have h11_eq_12 : χ 11 = χ 12 := by omega
  -- chi(13) ≠ chi(6) (from (15, 13, 18) Rado triple, chi(15) = chi(18) = chi(6)).
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 13
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_6, ← h13_eq_6]
    · show χ 13 = χ (13 + 5)
      rw [show (13 + 5 : ℕ) = 18 by decide, h18_eq_6, ← h13_eq_6]
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have h13_eq_12 : χ 13 = χ 12 := by omega
  -- chi(17) ≠ chi(6): from (6, 15, 17) Rado triple, chi(15) = chi(6).
  have h17_ne_6 : χ 17 ≠ χ 6 := by
    intro h17_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 15
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h15_eq_6.symm
    · show χ 15 = χ (15 + 2)
      rw [show (15 + 2 : ℕ) = 17 by decide, h17_eq_6, ← h15_eq_6]
  -- chi(17) ≠ chi(9): from (9, 17, 20) Rado triple, chi(20) = chi(9).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 17
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h17_eq_9]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h20_eq_9, ← h17_eq_9]
  -- chi(17) ≠ chi(12): from (12, 13, 17) Rado triple, chi(13) = chi(12).
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 13
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h13_eq_12.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h17_eq_12, ← h13_eq_12]
  -- chi(17) < 3 + ≠ chi(6), chi(9), chi(12) ⇒ impossible.
  omega

/--
  **Sub-case 3-β closure**: chi(23) is impossible when chi(15) = chi(12).

  Chain: chi(17) forced to chi(6) by:
  - chi(17) ≠ chi(12): (15, 12, 17) Rado with chi(15) = chi(12).
  - chi(17) ≠ chi(9): (9, 17, 20) Rado with chi(20) = chi(9).
  - chi(17) = chi(6).

  Then chi(23) impossible:
  - chi(23) ≠ chi(12): (24, 15, 23) Rado with chi(15) = chi(24) = chi(12).
  - chi(23) ≠ chi(9): (9, 20, 23) Rado with chi(20) = chi(9).
  - chi(23) ≠ chi(6): (18, 17, 23) Rado with chi(18) = chi(17) = chi(6).
-/
theorem bAdicEquation_3_sub3_beta_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_6 : χ 18 = χ 6) (h24_eq_12 : χ 24 = χ 12)
    (h15_eq_12 : χ 15 = χ 12) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(20) = chi(9) (foundational).
  have h20_eq_9 := bAdicEquation_3_chi_20_eq_9_when_chi_18_eq_6_chi_24_eq_12 (n := n) χ h24
    hχk hNoMono h6_ne_9 h6_ne_12 h9_ne_12 h18_eq_6 h24_eq_12
  -- chi(17) ≠ chi(12): from (15, 12, 17) Rado triple.
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 12
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  -- chi(17) ≠ chi(9): from (9, 17, 20) Rado triple.
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 17
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h17_eq_9]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h20_eq_9, ← h17_eq_9]
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have h17_eq_6 : χ 17 = χ 6 := by omega
  -- chi(23) ≠ chi(12): from (24, 15, 23) Rado triple.
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 15
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h15_eq_12]
    · show χ 15 = χ (15 + 8)
      rw [show (15 + 8 : ℕ) = 23 by decide, h15_eq_12, ← h23_eq_12]
  -- chi(23) ≠ chi(9): from (9, 20, 23) Rado triple.
  have h23_ne_9 : χ 23 ≠ χ 9 := by
    intro h23_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 20
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h20_eq_9]
    · show χ 20 = χ (20 + 3)
      rw [show (20 + 3 : ℕ) = 23 by decide, h20_eq_9, ← h23_eq_9]
  -- chi(23) ≠ chi(6): from (18, 17, 23) Rado triple.
  have h23_ne_6 : χ 23 ≠ χ 6 := by
    intro h23_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 17
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_6, ← h17_eq_6]
    · show χ 17 = χ (17 + 6)
      rw [show (17 + 6 : ℕ) = 23 by decide, h17_eq_6, ← h23_eq_6]
  -- chi(23) < 3 + ≠ chi(6), chi(9), chi(12) ⇒ impossible.
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  omega

/--
  **FULL CLOSURE of sub-case 3** = (chi(16) = chi(9), chi(18) = chi(6)) +
  chi(24) = chi(12). Splits chi(15) ∈ {chi(6), chi(12)} via 3-α/3-β.
-/
theorem bAdicEquation_3_sub3_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_9 : χ 16 = χ 9) (h18_eq_6 : χ 18 = χ 6) (h24_eq_12 : χ 24 = χ 12) :
    False := by
  -- chi(15) ∈ {chi(6), chi(12)}: from chi(15) ≠ chi(9) + chi(15) < 3.
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h4_eq_9 := bAdicEquation_3_chi_4_eq_9_when_chi_24_eq_12 (n := n) χ h24 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h24_eq_12
  have h15_ne_9 :=
    bAdicEquation_3_chi_15_ne_chi_9_when_chi_4_eq_9 (n := n) χ (by omega) hNoMono h4_eq_9
  have h15_or : χ 15 = χ 6 ∨ χ 15 = χ 12 := by omega
  rcases h15_or with h15_eq_6 | h15_eq_12
  · exact bAdicEquation_3_sub3_alpha_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_6 h24_eq_12 h15_eq_6
  · exact bAdicEquation_3_sub3_beta_contradiction (n := n) χ h24 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_6 h24_eq_12 h15_eq_12

/-! ### §58. CompressionHyp 3 3 — sub-case 2 FULL CLOSURE.

  Sub-case 2 = (chi(16) = chi(6), chi(18) = chi(9)) + chi(24) = chi(12).

  Splits chi(15) into 2-α and 2-β:
  - 2-α (chi(15) = chi(6)): closes via chi(1) impossibility after a 20-step
    derivation chain (chi(10), chi(11), chi(7), chi(5), chi(2), chi(3) all
    forced, then chi(1) ∈ {chi(6), chi(9), chi(12)} all blocked).
-/

/--
  **Sub-case 2-α closure**: chi(15) = chi(6) sub-case ⇒ derive chi(10) =
  chi(12), chi(11) = chi(12), chi(7) = chi(6), chi(5) = chi(12), chi(2) =
  chi(9), chi(3) = chi(6). Then chi(1) impossible:
  - chi(1) = chi(6): mono via (6, 1, 3) with chi(3) = chi(6).
  - chi(1) = chi(9): mono via (9, 1, 4) with chi(4) = chi(9).
  - chi(1) = chi(12): mono via (12, 1, 5) with chi(5) = chi(12).
-/
theorem bAdicEquation_3_sub2_alpha_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_6 : χ 16 = χ 6) (h18_eq_9 : χ 18 = χ 9) (h24_eq_12 : χ 24 = χ 12)
    (h15_eq_6 : χ 15 = χ 6) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(4) = chi(9) (foundational).
  have h4_eq_9 := bAdicEquation_3_chi_4_eq_9_when_chi_24_eq_12 (n := n) χ h24 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h24_eq_12
  -- chi(8) = chi(9) (foundational).
  have h8_eq_9 := bAdicEquation_3_chi_8_eq_9_in_sub4 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  -- chi(10) ≠ chi(9): from (18, 4, 10) Rado with chi(18) = chi(4) = chi(9).
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 4
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h4_eq_9]
    · show χ 4 = χ (4 + 6)
      rw [show (4 + 6 : ℕ) = 10 by decide, h10_eq_9, ← h4_eq_9]
  -- chi(10) ≠ chi(6): self-loop xz m=5 (chi(10) ≠ chi(15) = chi(6)).
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  have h10_ne_6 : χ 10 ≠ χ 6 := by intro h; apply h10_ne_15; rw [h, ← h15_eq_6]
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have h10_eq_12 : χ 10 = χ 12 := by omega
  -- chi(11) ≠ chi(9) (foundational).
  have h11_ne_9 :=
    bAdicEquation_3_chi_11_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  -- chi(11) ≠ chi(6): from (15, 6, 11) Rado with chi(15) = chi(6).
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 6
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_6
    · show χ 6 = χ (6 + 5)
      rw [show (6 + 5 : ℕ) = 11 by decide]; exact h11_eq_6.symm
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have h11_eq_12 : χ 11 = χ 12 := by omega
  -- chi(7) ≠ chi(9): from (9, 4, 7) Rado with chi(4) = chi(9).
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 4
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h4_eq_9]
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h7_eq_9, ← h4_eq_9]
  -- chi(7) ≠ chi(12): from (12, 7, 11) Rado with chi(11) = chi(12).
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 7
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h7_eq_12]
    · show χ 7 = χ (7 + 4)
      rw [show (7 + 4 : ℕ) = 11 by decide, h11_eq_12, ← h7_eq_12]
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have h7_eq_6 : χ 7 = χ 6 := by omega
  -- chi(5) ≠ chi(9): from (9, 5, 8) Rado with chi(8) = chi(9).
  have h5_ne_9 :=
    bAdicEquation_3_chi_5_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  -- chi(5) ≠ chi(6): from (6, 5, 7) Rado with chi(7) = chi(6).
  have h5_ne_6 : χ 5 ≠ χ 6 := by
    intro h5_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 5
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h5_eq_6]
    · show χ 5 = χ (5 + 2)
      rw [show (5 + 2 : ℕ) = 7 by decide, h7_eq_6, ← h5_eq_6]
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have h5_eq_12 : χ 5 = χ 12 := by omega
  -- chi(2) ≠ chi(6): from (15, 2, 7) Rado with chi(15) = chi(7) = chi(6).
  have h2_ne_6 : χ 2 ≠ χ 6 := by
    intro h2_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 2
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_6, ← h2_eq_6]
    · show χ 2 = χ (2 + 5)
      rw [show (2 + 5 : ℕ) = 7 by decide, h7_eq_6, ← h2_eq_6]
  -- chi(2) ≠ chi(12): from (24, 2, 10) Rado with chi(24) = chi(10) = chi(12).
  have h2_ne_12 : χ 2 ≠ χ 12 := by
    intro h2_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 2
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h2_eq_12]
    · show χ 2 = χ (2 + 8)
      rw [show (2 + 8 : ℕ) = 10 by decide, h10_eq_12, ← h2_eq_12]
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have h2_eq_9 : χ 2 = χ 9 := by omega
  -- chi(3) ≠ chi(9): from chi(3) ≠ chi(2) (self-loop xz m=1), chi(2) = chi(9).
  have h2_ne_3 : χ 2 ≠ χ 3 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 1) (by omega) (by omega)
    show χ (2 * 1) ≠ χ (3 * 1); exact h
  have h3_ne_9 : χ 3 ≠ χ 9 := by intro h; apply h2_ne_3; rw [h2_eq_9, h]
  -- chi(3) ≠ chi(12): from (24, 3, 11) Rado with chi(24) = chi(11) = chi(12).
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 3
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h3_eq_12]
    · show χ 3 = χ (3 + 8)
      rw [show (3 + 8 : ℕ) = 11 by decide, h11_eq_12, ← h3_eq_12]
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have h3_eq_6 : χ 3 = χ 6 := by omega
  -- chi(1) impossibility.
  -- chi(1) ≠ chi(6): from (6, 1, 3) Rado with chi(3) = chi(6).
  have h1_ne_6 : χ 1 ≠ χ 6 := by
    intro h1_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 1
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h1_eq_6]
    · show χ 1 = χ (1 + 2)
      rw [show (1 + 2 : ℕ) = 3 by decide, h3_eq_6, ← h1_eq_6]
  -- chi(1) ≠ chi(9): from (9, 1, 4) Rado with chi(4) = chi(9).
  have h1_ne_9 : χ 1 ≠ χ 9 := by
    intro h1_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 1
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h1_eq_9]
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_9, ← h1_eq_9]
  -- chi(1) ≠ chi(12): from (12, 1, 5) Rado with chi(5) = chi(12).
  have h1_ne_12 : χ 1 ≠ χ 12 := by
    intro h1_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 1
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h1_eq_12]
    · show χ 1 = χ (1 + 4)
      rw [show (1 + 4 : ℕ) = 5 by decide, h5_eq_12, ← h1_eq_12]
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  omega

/--
  **Sub-case 2-β-i closure**: chi(15) = chi(12), chi(20) = chi(6) ⇒
  extended chain to (3, 24, 25) mono.
  Assumes chi(7), chi(5), chi(10), chi(11), chi(13), chi(19), chi(17)
  derivation already complete (shared with 2-β-ii).
-/
theorem bAdicEquation_3_sub2_beta_i_extended_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h18_eq_9 : χ 18 = χ 9) (h24_eq_12 : χ 24 = χ 12)
    (h15_eq_12 : χ 15 = χ 12) (h17_eq_9 : χ 17 = χ 9) (h19_eq_6 : χ 19 = χ 6)
    (h20_eq_6 : χ 20 = χ 6) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(23) = chi(6).
  have h23_ne_9 : χ 23 ≠ χ 9 := by
    intro h23_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 17
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 6)
      rw [show (17 + 6 : ℕ) = 23 by decide, h17_eq_9, ← h23_eq_9]
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 15
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h15_eq_12]
    · show χ 15 = χ (15 + 8)
      rw [show (15 + 8 : ℕ) = 23 by decide, h15_eq_12, ← h23_eq_12]
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  have h23_eq_6 : χ 23 = χ 6 := by omega
  -- chi(21) = chi(12).
  have h21_ne_6 : χ 21 ≠ χ 6 := by
    intro h21_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 21
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h21_eq_6]
    · show χ 21 = χ (21 + 2)
      rw [show (21 + 2 : ℕ) = 23 by decide, h23_eq_6, ← h21_eq_6]
  have h21_ne_9 : χ 21 ≠ χ 9 := by
    intro h21_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 18
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h18_eq_9.symm
    · show χ 18 = χ (18 + 3)
      rw [show (18 + 3 : ℕ) = 21 by decide, h18_eq_9, ← h21_eq_9]
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have h21_eq_12 : χ 21 = χ 12 := by omega
  -- chi(3) = chi(12).
  have h3_ne_9 : χ 3 ≠ χ 9 := by
    intro h3_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 17
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 1)
      rw [show (17 + 1 : ℕ) = 18 by decide, h17_eq_9, ← h18_eq_9]
  have h3_ne_6 : χ 3 ≠ χ 6 := by
    intro h3_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 19
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h19_eq_6]
    · show χ 19 = χ (19 + 1)
      rw [show (19 + 1 : ℕ) = 20 by decide, h19_eq_6, h20_eq_6]
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have h3_eq_12 : χ 3 = χ 12 := by omega
  -- chi(22) = chi(9).
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 21
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_12, ← h21_eq_12]
    · show χ 21 = χ (21 + 1)
      rw [show (21 + 1 : ℕ) = 22 by decide, h21_eq_12, ← h22_eq_12]
  have h22_ne_6 : χ 22 ≠ χ 6 := by
    intro h22_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 20
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h20_eq_6.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_6, ← h22_eq_6]
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have h22_eq_9 : χ 22 = χ 9 := by omega
  -- chi(25) = chi(12).
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 22
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h22_eq_9]
    · show χ 22 = χ (22 + 3)
      rw [show (22 + 3 : ℕ) = 25 by decide, h22_eq_9, ← h25_eq_9]
  have h25_ne_6 : χ 25 ≠ χ 6 := by
    intro h25_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 23
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h23_eq_6]
    · show χ 23 = χ (23 + 2)
      rw [show (23 + 2 : ℕ) = 25 by decide, h23_eq_6, ← h25_eq_6]
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have h25_eq_12 : χ 25 = χ 12 := by omega
  -- MONO via (3, 24, 25).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 24) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 24
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_12, h24_eq_12]
  · show χ 24 = χ (24 + 1)
    rw [show (24 + 1 : ℕ) = 25 by decide, h25_eq_12, h24_eq_12]

/--
  **Sub-case 2-β closure**: chi(15) = chi(12) sub-case ⇒ derive shared chain
  chi(7) = chi(6), chi(5) = chi(12), chi(10) = chi(6), chi(11) = chi(6),
  chi(13) = chi(9), chi(19) = chi(6), chi(17) = chi(9).

  Then split on chi(20):
  - chi(20) = chi(9): immediate mono via (9, 17, 20).
  - chi(20) = chi(6): extend chain via sub2_beta_i_extended_contradiction.
-/
theorem bAdicEquation_3_sub2_beta_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_6 : χ 16 = χ 6) (h18_eq_9 : χ 18 = χ 9) (h24_eq_12 : χ 24 = χ 12)
    (h15_eq_12 : χ 15 = χ 12) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have h4_eq_9 := bAdicEquation_3_chi_4_eq_9_when_chi_24_eq_12 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h24_eq_12
  have h8_eq_9 := bAdicEquation_3_chi_8_eq_9_in_sub4 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12
  -- chi(7) = chi(6): (24, 7, 15) gives chi(7) ≠ chi(12); (9, 4, 7) gives chi(7) ≠ chi(9).
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 7
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h7_eq_12]
    · show χ 7 = χ (7 + 8)
      rw [show (7 + 8 : ℕ) = 15 by decide, h15_eq_12, ← h7_eq_12]
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 4
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h4_eq_9]
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h7_eq_9, ← h4_eq_9]
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have h7_eq_6 : χ 7 = χ 6 := by omega
  -- chi(5) = chi(12): (6, 5, 7) gives chi(5) ≠ chi(6); (9, 5, 8) gives chi(5) ≠ chi(9).
  have h5_ne_6 : χ 5 ≠ χ 6 := by
    intro h5_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 5
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h5_eq_6]
    · show χ 5 = χ (5 + 2)
      rw [show (5 + 2 : ℕ) = 7 by decide, h7_eq_6, ← h5_eq_6]
  have h5_ne_9 :=
    bAdicEquation_3_chi_5_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have h5_eq_12 : χ 5 = χ 12 := by omega
  -- chi(10) = chi(6): (15, 5, 10) gives chi(10) ≠ chi(12); (18, 4, 10) gives chi(10) ≠ chi(9).
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 5
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_12, ← h5_eq_12]
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide, h10_eq_12, ← h5_eq_12]
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 4
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h4_eq_9]
    · show χ 4 = χ (4 + 6)
      rw [show (4 + 6 : ℕ) = 10 by decide, h10_eq_9, ← h4_eq_9]
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have h10_eq_6 : χ 10 = χ 6 := by omega
  -- chi(11) = chi(6): (12, 11, 15) gives chi(11) ≠ chi(12); (9, 8, 11) gives chi(11) ≠ chi(9).
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 11
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h11_eq_12]
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h15_eq_12, ← h11_eq_12]
  have h11_ne_9 :=
    bAdicEquation_3_chi_11_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have h11_eq_6 : χ 11 = χ 6 := by omega
  -- chi(13) = chi(9): (6, 11, 13) gives chi(13) ≠ chi(6); (24, 5, 13) gives chi(13) ≠ chi(12).
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 11
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h11_eq_6]
    · show χ 11 = χ (11 + 2)
      rw [show (11 + 2 : ℕ) = 13 by decide, h13_eq_6, ← h11_eq_6]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 5
      rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_12, ← h5_eq_12]
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide, h13_eq_12, ← h5_eq_12]
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have h13_eq_9 : χ 13 = χ 9 := by omega
  -- chi(19) = chi(6): (18, 13, 19) gives chi(19) ≠ chi(9); (12, 15, 19) gives chi(19) ≠ chi(12).
  have h19_ne_9 : χ 19 ≠ χ 9 := by
    intro h19_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 13
      rw [show (3 * 6 : ℕ) = 18 by decide, h18_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 6)
      rw [show (13 + 6 : ℕ) = 19 by decide, h19_eq_9, ← h13_eq_9]
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 15
      rw [show (3 * 4 : ℕ) = 12 by decide]; exact h15_eq_12.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h19_eq_12, ← h15_eq_12]
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have h19_eq_6 : χ 19 = χ 6 := by omega
  -- chi(17) = chi(9): (6, 17, 19) gives chi(17) ≠ chi(6); (15, 12, 17) gives chi(17) ≠ chi(12).
  have h17_ne_6 : χ 17 ≠ χ 6 := by
    intro h17_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 17
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h17_eq_6]
    · show χ 17 = χ (17 + 2)
      rw [show (17 + 2 : ℕ) = 19 by decide, h19_eq_6, ← h17_eq_6]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 12
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have h17_eq_9 : χ 17 = χ 9 := by omega
  -- Split on chi(20).
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have h15_ne_20 : χ 15 ≠ χ 20 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (3 * 5) ≠ χ (4 * 5); exact h
  have h20_ne_12 : χ 20 ≠ χ 12 := by intro h; apply h15_ne_20; rw [h15_eq_12, h]
  have h20_or : χ 20 = χ 6 ∨ χ 20 = χ 9 := by omega
  rcases h20_or with h20_eq_6 | h20_eq_9
  · -- 2-β-i (chi(20) = chi(6)). Delegate to extended helper.
    exact bAdicEquation_3_sub2_beta_i_extended_contradiction (n := n) χ h26 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h18_eq_9 h24_eq_12 h15_eq_12 h17_eq_9 h19_eq_6 h20_eq_6
  · -- 2-β-ii (chi(20) = chi(9)). MONO via (9, 17, 20): chi(9) = chi(17) = chi(20) = chi(9).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 17
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h17_eq_9]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_9, h20_eq_9]

/--
  **FULL CLOSURE of sub-case 2** = (chi(16) = chi(6), chi(18) = chi(9)) +
  chi(24) = chi(12). Bundles 2-α and 2-β via chi(15) split.
-/
theorem bAdicEquation_3_sub2_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12)
    (h16_eq_6 : χ 16 = χ 6) (h18_eq_9 : χ 18 = χ 9) (h24_eq_12 : χ 24 = χ 12) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h4_eq_9 := bAdicEquation_3_chi_4_eq_9_when_chi_24_eq_12 (n := n) χ (by omega) hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12 h24_eq_12
  have h15_ne_9 :=
    bAdicEquation_3_chi_15_ne_chi_9_when_chi_4_eq_9 (n := n) χ (by omega) hNoMono h4_eq_9
  have h15_or : χ 15 = χ 6 ∨ χ 15 = χ 12 := by omega
  rcases h15_or with h15_eq_6 | h15_eq_12
  · exact bAdicEquation_3_sub2_alpha_contradiction (n := n) χ (by omega) hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_6 h18_eq_9 h24_eq_12 h15_eq_6
  · exact bAdicEquation_3_sub2_beta_contradiction (n := n) χ h26 hχk hNoMono
      h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_6 h18_eq_9 h24_eq_12 h15_eq_12

/-! ### §59. CompressionHyp 3 3 — '(6,9,12) all distinct' branch FULL CLOSURE.

  Combines all 4 sub-cases via (chi(16), chi(18)) ∈ {chi(6), chi(9)}² split:
  - sub1: (chi(6), chi(6)) → (6, 16, 18) mono immediate.
  - sub2: (chi(6), chi(9)) → bAdicEquation_3_sub2_contradiction.
  - sub3: (chi(9), chi(6)) → bAdicEquation_3_sub3_contradiction.
  - sub4: (chi(9), chi(9)) → bAdicEquation_3_sub4_contradiction.

  Plus the chi(24) = chi(12) reduction for sub2, sub3 (chi(16) ≠ chi(18))
  via bAdicEquation_3_chi_24_eq_chi_12_when_16_18_distinct.
-/

/--
  **(6,9,12) all distinct branch FULL CLOSURE**: NO mono-free 3-coloring χ
  of [1, n] (n ≥ 26) for bAdicEquation 3 has chi(6), chi(9), chi(12) all
  distinct. (Equivalently: under (6,9,12) distinct, get mono.)

  This is the MAIN result for the "all distinct" branch in the contrapositive
  of CompressionHyp 3 3. Bundles all 4 sub-cases via (chi(16), chi(18)) split.
-/
theorem bAdicEquation_3_no_chi_6_9_12_all_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_ne_9 : χ 6 ≠ χ 9) (h6_ne_12 : χ 6 ≠ χ 12) (h9_ne_12 : χ 9 ≠ χ 12) :
    False := by
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(16) ≠ chi(12) (self-loop xy m=4); chi(18) ≠ chi(12) (self-loop xz m=6).
  have h12_ne_16 := bAdicEquation_3_chi_12_ne_chi_16 χ (by omega) hNoMono
  have h12_ne_18 := bAdicEquation_3_chi_12_ne_chi_18 χ (by omega) hNoMono
  -- chi(16), chi(18) ∈ {chi(6), chi(9)}.
  have h16_or : χ 16 = χ 6 ∨ χ 16 = χ 9 := by omega
  have h18_or : χ 18 = χ 6 ∨ χ 18 = χ 9 := by omega
  rcases h16_or with h16_eq_6 | h16_eq_9
  · rcases h18_or with h18_eq_6 | h18_eq_9
    · -- sub1: chi(16) = chi(18) = chi(6).
      exact bAdicEquation_3_no_chi_16_18_both_eq_6 (n := n) χ (by omega) hNoMono
        h16_eq_6 h18_eq_6
    · -- sub2: chi(16) = chi(6), chi(18) = chi(9). chi(24) = chi(12) forced.
      have h16_ne_18 : χ 16 ≠ χ 18 := by rw [h16_eq_6, h18_eq_9]; exact h6_ne_9
      have h24_eq_12 := bAdicEquation_3_chi_24_eq_chi_12_when_16_18_distinct (n := n) χ
        (by omega) hχk hNoMono h6_ne_9 h6_ne_12 h9_ne_12 h16_ne_18
      exact bAdicEquation_3_sub2_contradiction (n := n) χ h26 hχk hNoMono
        h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_6 h18_eq_9 h24_eq_12
  · rcases h18_or with h18_eq_6 | h18_eq_9
    · -- sub3: chi(16) = chi(9), chi(18) = chi(6). chi(24) = chi(12) forced.
      have h16_ne_18 : χ 16 ≠ χ 18 := by rw [h16_eq_9, h18_eq_6]; exact h6_ne_9.symm
      have h24_eq_12 := bAdicEquation_3_chi_24_eq_chi_12_when_16_18_distinct (n := n) χ
        (by omega) hχk hNoMono h6_ne_9 h6_ne_12 h9_ne_12 h16_ne_18
      exact bAdicEquation_3_sub3_contradiction (n := n) χ (by omega) hχk hNoMono
        h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_6 h24_eq_12
    · -- sub4: chi(16) = chi(18) = chi(9).
      exact bAdicEquation_3_sub4_contradiction (n := n) χ (by omega) hχk hNoMono
        h6_ne_9 h6_ne_12 h9_ne_12 h16_eq_9 h18_eq_9

/-! ### §60. CompressionHyp 3 3 — case Y (chi(6) = chi(12)) foundational toolkit.

  In case Y, chi(6) = chi(12) (forced if (6,9,12) NOT all distinct under
  chi(6) ≠ chi(9) ≠ chi(12)). This gives many Rado triple constraints of
  form (12, y, y+4) and (6, y, y+2).

  Key forced non-equalities:
    chi(2), chi(10), chi(14) ≠ chi(6) (from various Rado triples).
-/

/--
  **chi(2) ≠ chi(6) under case Y (chi(6) = chi(12))**.

  Direct from (12, 2, 6) Rado triple at b=3, d=4, y=2: NOT (chi(12) =
  chi(2) AND chi(2) = chi(6)). Since chi(12) = chi(6), forces chi(2) ≠ chi(6).
-/
theorem bAdicEquation_3_chi_2_ne_chi_6_when_chi_6_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) :
    χ 2 ≠ χ 6 := by
  intro h2_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 2) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 2
    rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, ← h2_eq_6]
  · show χ 2 = χ (2 + 4)
    rw [show (2 + 4 : ℕ) = 6 by decide]; exact h2_eq_6

/--
  **chi(10) ≠ chi(6) under case Y (chi(6) = chi(12))**.

  Direct from (12, 6, 10) Rado triple at b=3, d=4, y=6: NOT (chi(12) =
  chi(6) AND chi(6) = chi(10)). Since chi(12) = chi(6), forces chi(10) ≠ chi(6).
-/
theorem bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) :
    χ 10 ≠ χ 6 := by
  intro h10_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 6
    rw [show (3 * 4 : ℕ) = 12 by decide]; exact h6_eq_12.symm
  · show χ 6 = χ (6 + 4)
    rw [show (6 + 4 : ℕ) = 10 by decide]; exact h10_eq_6.symm

/--
  **chi(14) ≠ chi(6) under case Y (chi(6) = chi(12))**.

  Direct from (6, 12, 14) Rado triple at b=3, d=2, y=12: NOT (chi(6) =
  chi(12) AND chi(12) = chi(14)). Since chi(6) = chi(12), forces chi(14) ≠
  chi(12) = chi(6).
-/
theorem bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h14 : 14 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) :
    χ 14 ≠ χ 6 := by
  intro h14_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 2) = χ 12
    rw [show (3 * 2 : ℕ) = 6 by decide]; exact h6_eq_12
  · show χ 12 = χ (12 + 2)
    rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_6, ← h6_eq_12]

/--
  **Case Y master non-A invariant**: in case Y (chi(6) = chi(12)), under
  mono-free 3-coloring of [1, n] (n ≥ 24) for bAdicEquation 3, all the
  following positions have chi != chi(6):
    chi(2), chi(4), chi(8), chi(10), chi(14), chi(16), chi(18).

  (All from self-loops or case Y Rado triples.)
-/
theorem bAdicEquation_3_case_Y_chi_ne_chi_6_bundle
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) :
    χ 2 ≠ χ 6 ∧ χ 4 ≠ χ 6 ∧ χ 8 ≠ χ 6 ∧ χ 10 ≠ χ 6 ∧
    χ 14 ≠ χ 6 ∧ χ 16 ≠ χ 6 ∧ χ 18 ≠ χ 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bAdicEquation_3_chi_2_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  · -- chi(4) ≠ chi(6): self-loop xz m=2.
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 2) (by omega) (by omega)
    show χ 4 ≠ χ 6
    have h' : χ (2 * 2) ≠ χ (3 * 2) := h
    convert h' using 2 <;> decide
  · -- chi(8) ≠ chi(6): self-loop xy m=2.
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 2) (by omega) (by omega)
    show χ 8 ≠ χ 6
    have h' : χ (3 * 2) ≠ χ (4 * 2) := h
    intro hne; apply h'
    show χ (3 * 2) = χ (4 * 2)
    rw [show (3 * 2 : ℕ) = 6 by decide, show (4 * 2 : ℕ) = 8 by decide]
    exact hne.symm
  · exact bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  · exact bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  · -- chi(16) ≠ chi(6): self-loop xy m=4 gives chi(12) ≠ chi(16). chi(12) = chi(6).
    have h := bAdicEquation_3_chi_12_ne_chi_16 χ (by omega) hNoMono
    intro h16_eq_6
    apply h; rw [h6_eq_12.symm, h16_eq_6]
  · -- chi(18) ≠ chi(6): self-loop xz m=6 gives chi(12) ≠ chi(18). chi(12) = chi(6).
    have h := bAdicEquation_3_chi_12_ne_chi_18 χ (by omega) hNoMono
    intro h18_eq_6
    apply h; rw [h6_eq_12.symm, h18_eq_6]

/--
  **chi(24) = chi(6) in case Y when chi(16) ≠ chi(18)**.

  In case Y (chi(6) = chi(12)), chi(16), chi(18) ∈ {0, 1, 2} \ {chi(6)} = the
  2 colors not equal to chi(6). If chi(16) ≠ chi(18), they exhaust these 2
  colors. Combined with chi(24) ≠ chi(16) AND chi(24) ≠ chi(18), forces
  chi(24) ∉ those 2 colors. Hence chi(24) = chi(6).
-/
theorem bAdicEquation_3_case_Y_chi_24_eq_chi_6_when_chi_16_18_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h16_ne_18 : χ 16 ≠ χ 18) :
    χ 24 = χ 6 := by
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  -- chi(16) ≠ chi(6), chi(18) ≠ chi(6) from bundle.
  have ⟨_, _, _, _, _, h16_ne_6, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  -- chi(24) ≠ chi(16) self-loop xz m=8, chi(24) ≠ chi(18) self-loop xy m=6.
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ h24 hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  -- chi(16), chi(18) take the 2 colors ≠ chi(6); chi(24) ∉ those, so chi(24) = chi(6).
  omega

/--
  **DICHOTOMY in case Y**: chi(16) = chi(18) ↔ chi(24) ≠ chi(6).

  Contrapositive of `bAdicEquation_3_case_Y_chi_24_eq_chi_6_when_chi_16_18_distinct`.

  This is the KEY structural dichotomy for case Y analysis:
  - Branch (I): chi(24) = chi(6) (= A). chi(16), chi(18) can be different
    (∈ {B, C}, possibly distinct).
  - Branch (II): chi(24) ≠ chi(6). Then chi(16) = chi(18) (both = same value
    in {B, C}).

  This bundles the case Y attack into 2 distinct sub-branches.
-/
theorem bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 16 = χ 18 := by
  by_contra h16_ne_18
  exact h24_ne_6 (bAdicEquation_3_case_Y_chi_24_eq_chi_6_when_chi_16_18_distinct (n := n) χ
    h24 hχk hNoMono h6_eq_12 h16_ne_18)

/--
  **UNIFIED chi(10) = chi(24) in case Y + chi(24) ≠ chi(6)**.

  HIGH-LEVERAGE structural invariant for branch (II) of case Y. Holds in
  BOTH sub-cases (chi(24) = B and chi(24) = C):

  - chi(16) = chi(18) (from dichotomy R+221).
  - chi(10) ≠ chi(18) (from (18, 10, 16) Rado with chi(18) = chi(16)).
  - chi(10) ≠ chi(6) (case Y bundle).
  - chi(24) ≠ chi(16), chi(24) ≠ chi(6).
  - Hence chi(10), chi(24) both take the "other" non-{chi(6), chi(16)} color,
    so chi(10) = chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 10 = χ 24 := by
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have ⟨_, _, _, h10_ne_6, _, h16_ne_6, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ h24 hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  -- chi(10) ≠ chi(18): from (18, 10, 16) Rado triple (chi(18) = chi(16)).
  have h10_ne_18 : χ 10 ≠ χ 18 := by
    intro h10_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 10
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h10_eq_18.symm
    · show χ 10 = χ (10 + 6)
      rw [show (10 + 6 : ℕ) = 16 by decide]
      exact h10_eq_18.trans h16_eq_18.symm
  omega

/--
  **UNIFIED chi(2) determination in case Y + chi(24) ≠ chi(6)**.

  chi(2) takes the 3rd color w.r.t. {chi(6), chi(24)}. Specifically:
  - chi(2) ≠ chi(6) (case Y bundle).
  - chi(2) ≠ chi(24): from (24, 2, 10) Rado with chi(24) = chi(10) (UNIFIED above).

  So chi(2) is in {0, 1, 2} \ {chi(6), chi(24)} = singleton when chi(6) ≠ chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_2_ne_chi_24_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 2 ≠ χ 24 := by
  intro h2_eq_24
  have h10_eq_24 := bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 2) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 2
    rw [show (3 * 8 : ℕ) = 24 by decide, ← h2_eq_24]
  · show χ 2 = χ (2 + 8)
    rw [show (2 + 8 : ℕ) = 10 by decide, h10_eq_24, ← h2_eq_24]

/--
  **UNIFIED chi(2) = chi(18) in case Y + chi(24) ≠ chi(6)** (Branch II).

  chi(2) and chi(18) BOTH take "the color ≠ chi(6) AND ≠ chi(24)" = the
  unique value in {B, C} \\ {chi(24)}.

  This is a HIGH-LEVERAGE structural identity that unifies the Branch II
  sub-cases (chi(24) = chi(9) vs chi(24) = 3rd color) under a single
  invariant.
-/
theorem bAdicEquation_3_case_Y_chi_2_eq_chi_18_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 2 = χ 18 := by
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have ⟨h2_ne_6, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h2_ne_24 := bAdicEquation_3_case_Y_chi_2_ne_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  -- chi(2), chi(18) ≠ chi(6) AND ≠ chi(24). So both = singleton non-{A, chi(24)}.
  omega

/--
  **UNIFIED chi(8) = chi(24) in case Y + chi(24) ≠ chi(6)** (Branch II).

  Via (18, 2, 8) Rado triple: chi(18) = chi(2) (UNIFIED above), so need
  chi(8) = chi(18) for mono. Hence chi(8) ≠ chi(18). Combined with chi(8) ≠
  chi(6) (bundle), chi(8) takes the OTHER non-A color = chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 8 = χ 24 := by
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have ⟨_, _, h8_ne_6, _, _, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h2_eq_18 := bAdicEquation_3_case_Y_chi_2_eq_chi_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  -- chi(8) ≠ chi(18): from (18, 2, 8) Rado with chi(18) = chi(2).
  have h8_ne_18 : χ 8 ≠ χ 18 := by
    intro h8_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 2
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h2_eq_18.symm
    · show χ 2 = χ (2 + 6)
      rw [show (2 + 6 : ℕ) = 8 by decide, h8_eq_18, ← h2_eq_18]
  -- chi(8) ≠ chi(6), ≠ chi(18). chi(18) ≠ chi(24), chi(24) ≠ chi(6). So chi(8) = chi(24).
  omega

/--
  **UNIFIED chi(22) ≠ chi(18) in case Y + chi(24) ≠ chi(6)** (Branch II).

  From (18, 16, 22) Rado: chi(18) = chi(16) = chi(22) needs all = V.
  chi(16) = chi(18) = V (Branch II), so chi(22) ≠ V for non-mono.

  So chi(22) ∈ {chi(6), chi(24)} = {A, chi(24)}. Narrows chi(22) to 2 options.
-/
theorem bAdicEquation_3_case_Y_chi_22_ne_chi_18_when_chi_24_ne_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 22 ≠ χ 18 := by
  intro h22_eq_18
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 16
    rw [show (3 * 6 : ℕ) = 18 by decide]; exact h16_eq_18.symm
  · show χ 16 = χ (16 + 6)
    rw [show (16 + 6 : ℕ) = 22 by decide, h22_eq_18, ← h16_eq_18]

/--
  **MASTER Branch (II) skeleton** (case Y + chi(24) ≠ chi(6)): bundles all
  unified structural invariants into one theorem.

  States: chi(16) = chi(18) = chi(2) (= V, the "other" non-A color)
       ∧ chi(10) = chi(24) = chi(8) (= chi(24))
       ∧ chi(22) ≠ chi(18) (so chi(22) ∈ {chi(6), chi(24)})

  Encodes the 8-position structure of Branch (II):
    Class A (chi(6) value): {6, 12}
    Class V (chi(18) value): {2, 16, 18}
    Class W (chi(24) value): {8, 10, 24}
    chi(22): in {A, W}

  This is the HIGHEST-LEVERAGE structural compression for Branch (II).
-/
theorem bAdicEquation_3_case_Y_branch_II_skeleton
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 16 = χ 18 ∧ χ 2 = χ 18 ∧ χ 10 = χ 24 ∧ χ 8 = χ 24 ∧ χ 22 ≠ χ 18 :=
  ⟨bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6,
   bAdicEquation_3_case_Y_chi_2_eq_chi_18_when_chi_24_ne_6 (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6,
   bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6,
   bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6,
   bAdicEquation_3_case_Y_chi_22_ne_chi_18_when_chi_24_ne_6 (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6⟩

/--
  **CRITICAL MONO TRIPLE in Branch (II)**: (15, 5, 10) Rado.

  In Branch (II), chi(10) = chi(24). For (15, 5, 10) Rado triple: chi(15) =
  chi(5) AND chi(5) = chi(10) gives mono. Since chi(10) = chi(24), this
  simplifies to: chi(15) = chi(5) = chi(24) → False.

  Combined with chi(15) ≠ chi(20) self-loop, gives a CLEAN MONO when
  chi(15) and chi(5) both equal chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_15_5_eq_chi_24_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h15_eq_24 : χ 15 = χ 24) (h5_eq_24 : χ 5 = χ 24) :
    False := by
  have h10_eq_24 := bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 5
    rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_24, ← h5_eq_24]
  · show χ 5 = χ (5 + 5)
    rw [show (5 + 5 : ℕ) = 10 by decide, h10_eq_24, ← h5_eq_24]

/--
  **CRITICAL MONO TRIPLE in Branch (II)**: (3, 23, 24) Rado.

  chi(3) = chi(23) = chi(24) → mono. Since chi(24) is fixed, this gives mono
  when chi(3) = chi(23) = chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_3_23_eq_chi_24_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_24 : χ 3 = χ 24) (h23_eq_24 : χ 23 = χ 24) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 23) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 23
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_24, ← h23_eq_24]
  · show χ 23 = χ (23 + 1)
    rw [show (23 + 1 : ℕ) = 24 by decide]; exact h23_eq_24

/--
  **CRITICAL MONO TRIPLE in Branch (II)**: (12, 15, 19) Rado.

  chi(12) = chi(15) = chi(19) → mono. Since chi(12) = chi(6) in case Y, this
  gives mono when chi(15) = chi(19) = chi(6).
-/
theorem bAdicEquation_3_case_Y_chi_15_19_eq_chi_6_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12)
    (h15_eq_6 : χ 15 = χ 6) (h19_eq_6 : χ 19 = χ 6) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 15
    rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12]; exact h15_eq_6.symm
  · show χ 15 = χ (15 + 4)
    rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_6, ← h19_eq_6]

/-! ### §63. CompressionHyp 3 3 — Branch (I) (chi(24) = chi(6)) foundational. -/

/--
  **Branch (I) chi(22) ≠ chi(6)**: when chi(24) = chi(6) (Branch I of case Y),
  chi(22) ≠ chi(6). From (6, 22, 24) Rado.
-/
theorem bAdicEquation_3_case_Y_chi_22_ne_chi_6_when_chi_24_eq_6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_6 : χ 24 = χ 6) :
    χ 22 ≠ χ 6 := by
  intro h22_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 22) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 2) = χ 22
    rw [show (3 * 2 : ℕ) = 6 by decide, ← h22_eq_6]
  · show χ 22 = χ (22 + 2)
    rw [show (22 + 2 : ℕ) = 24 by decide, h24_eq_6, ← h22_eq_6]

/--
  **Branch (I) chi(26) ≠ chi(6)**: when chi(24) = chi(6) (Branch I) and n ≥ 26.
  From (6, 24, 26) Rado.
-/
theorem bAdicEquation_3_case_Y_chi_26_ne_chi_6_when_chi_24_eq_6
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_6 : χ 24 = χ 6) :
    χ 26 ≠ χ 6 := by
  intro h26_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 2) = χ 24
    rw [show (3 * 2 : ℕ) = 6 by decide]; exact h24_eq_6.symm
  · show χ 24 = χ (24 + 2)
    rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_6, ← h26_eq_6]

/--
  **Branch (I) foundational bundle**: when chi(24) = chi(6) (Branch I of
  case Y), the chi values at {22, 26} are NOT chi(6). Combined with the
  case Y bundle, chi at all of {2, 4, 8, 10, 14, 16, 18, 22, 26} ≠ chi(6).

  Only chi(6), chi(12), chi(24) = chi(6) among even positions in [2, 26].
-/
theorem bAdicEquation_3_case_Y_branch_I_chi_ne_chi_6_bundle
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_eq_6 : χ 24 = χ 6) :
    χ 2 ≠ χ 6 ∧ χ 4 ≠ χ 6 ∧ χ 8 ≠ χ 6 ∧ χ 10 ≠ χ 6 ∧
    χ 14 ≠ χ 6 ∧ χ 16 ≠ χ 6 ∧ χ 18 ≠ χ 6 ∧
    χ 22 ≠ χ 6 ∧ χ 26 ≠ χ 6 := by
  have ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ (by omega) hNoMono h6_eq_12
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · exact bAdicEquation_3_case_Y_chi_22_ne_chi_6_when_chi_24_eq_6 (n := n) χ (by omega) hNoMono h24_eq_6
  · exact bAdicEquation_3_case_Y_chi_26_ne_chi_6_when_chi_24_eq_6 (n := n) χ h26 hNoMono h24_eq_6

/-! ### §64. Branch (II) chi(9) sub-case split. -/

/--
  **Branch (II) chi(9) split**: in case Y + chi(24) ≠ chi(6), chi(9) takes
  one of two values: chi(9) = chi(18) (i.e., chi(9) is "V" in our notation)
  OR chi(9) = chi(24) (i.e., chi(9) is "W").

  Reason: chi(9) ≠ chi(6) (self-loop). chi(9) ≠ A. chi(9) ∈ {V, W}. By
  Branch II skeleton, V = chi(18) and W = chi(24).
-/
theorem bAdicEquation_3_case_Y_branch_II_chi_9_split
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    χ 9 = χ 18 ∨ χ 9 = χ 24 := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have ⟨_, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  omega

/--
  **Branch (II) + chi(9) = chi(24) sub-case (II-W)**: chi(11) ≠ chi(24).

  From (9, 8, 11) Rado: chi(9) = chi(8) = chi(11) gives mono. chi(8) = chi(24)
  (skeleton). If chi(9) = chi(24), need chi(11) = chi(24) for mono. So
  chi(11) ≠ chi(24).
-/
theorem bAdicEquation_3_case_Y_branch_II_chi_11_ne_chi_24_when_chi_9_eq_24
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h9_eq_24 : χ 9 = χ 24) :
    χ 11 ≠ χ 24 := by
  intro h11_eq_24
  have h8_eq_24 := bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 8
    rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_24, ← h8_eq_24]
  · show χ 8 = χ (8 + 3)
    rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_24, ← h11_eq_24]

/--
  **Branch (II) + chi(9) = chi(18) sub-case (II-V)**: chi(13), chi(19) ≠ chi(18).

  From (9, 13, 16) and (9, 16, 19) Rado triples with chi(9) = chi(16) = V = chi(18).
-/
theorem bAdicEquation_3_case_Y_branch_II_chi_13_19_ne_chi_18_when_chi_9_eq_18
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h9_eq_18 : χ 9 = χ 18) :
    χ 13 ≠ χ 18 ∧ χ 19 ≠ χ 18 := by
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  -- chi(16) = chi(9): combine h16_eq_18 and h9_eq_18.
  have h16_eq_9 : χ 16 = χ 9 := h16_eq_18.trans h9_eq_18.symm
  refine ⟨?_, ?_⟩
  · -- chi(13) ≠ chi(9) = chi(18) from (9, 13, 16) Rado, chi(16) = chi(9).
    intro h13_eq_18
    have h13_eq_9 : χ 13 = χ 9 := h13_eq_18.trans h9_eq_18.symm
    exact bAdicEquation_3_chi_13_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono
      h16_eq_9 h13_eq_9
  · intro h19_eq_18
    have h19_eq_9 : χ 19 = χ 9 := h19_eq_18.trans h9_eq_18.symm
    exact bAdicEquation_3_chi_19_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono
      h16_eq_9 h19_eq_9

/-! ### §65. Branch (II) (15, 11, 16) mono closure + (24, 9, 17) closure. -/

/--
  **(15, 11, 16) MONO TRIPLE**: chi(15) = chi(11) = chi(16) → False.
  Direct Rado triple at b=3, d=5, y=11.
-/
theorem bAdicEquation_3_rado_15_11_16_mono
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_11 : χ 15 = χ 11) (h11_eq_16 : χ 11 = χ 16) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 11) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 11
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_11
  · show χ 11 = χ (11 + 5)
    rw [show (11 + 5 : ℕ) = 16 by decide]; exact h11_eq_16

/--
  **(24, 9, 17) MONO TRIPLE**: chi(24) = chi(9) = chi(17) → False.
  Direct Rado triple at b=3, d=8, y=9.
-/
theorem bAdicEquation_3_rado_24_9_17_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_9 : χ 24 = χ 9) (h9_eq_17 : χ 9 = χ 17) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 9
    rw [show (3 * 8 : ℕ) = 24 by decide]; exact h24_eq_9
  · show χ 9 = χ (9 + 8)
    rw [show (9 + 8 : ℕ) = 17 by decide]; exact h9_eq_17

/--
  **(24, 1, 9) MONO TRIPLE**: chi(24) = chi(1) = chi(9) → False.
  Direct Rado triple at b=3, d=8, y=1.
-/
theorem bAdicEquation_3_rado_24_1_9_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_1 : χ 24 = χ 1) (h1_eq_9 : χ 1 = χ 9) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 1) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 1
    rw [show (3 * 8 : ℕ) = 24 by decide]; exact h24_eq_1
  · show χ 1 = χ (1 + 8)
    rw [show (1 + 8 : ℕ) = 9 by decide]; exact h1_eq_9

/--
  **(9, 10, 13) MONO TRIPLE**: chi(9) = chi(10) = chi(13) → False.
  Direct Rado triple at b=3, d=3, y=10.
-/
theorem bAdicEquation_3_rado_9_10_13_mono
    {n : ℕ} (χ : ℕ → ℕ) (h13 : 13 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_10 : χ 9 = χ 10) (h10_eq_13 : χ 10 = χ 13) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 10
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_10
  · show χ 10 = χ (10 + 3)
    rw [show (10 + 3 : ℕ) = 13 by decide]; exact h10_eq_13

/--
  **(15, 2, 7) MONO TRIPLE**: chi(15) = chi(2) = chi(7) → False.
  Direct Rado triple at b=3, d=5, y=2.
-/
theorem bAdicEquation_3_rado_15_2_7_mono
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_2 : χ 15 = χ 2) (h2_eq_7 : χ 2 = χ 7) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 2) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 2
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_2
  · show χ 2 = χ (2 + 5)
    rw [show (2 + 5 : ℕ) = 7 by decide]; exact h2_eq_7

/--
  **CLOSURE for Branch (II) sub-case II-V + chi(15) = chi(18)**: if
  chi(15) = chi(18) (= V class), then (15, 11, 16) mono with chi(11) = chi(15)
  closes.

  Specifically: in Branch (II), chi(16) = chi(18) (skeleton). If chi(15) =
  chi(18) AND chi(11) = chi(18), then chi(15) = chi(11) = chi(16) = chi(18).
  By (15, 11, 16) mono, False.
-/
theorem bAdicEquation_3_case_Y_branch_II_chi_15_11_eq_chi_18_closure
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h15_eq_18 : χ 15 = χ 18) (h11_eq_18 : χ 11 = χ 18) :
    False := by
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  -- chi(15) = chi(11) and chi(11) = chi(16). Apply (15, 11, 16) mono.
  exact bAdicEquation_3_rado_15_11_16_mono (n := n) χ (by omega) hNoMono
    (h15_eq_18.trans h11_eq_18.symm) (h11_eq_18.trans h16_eq_18.symm)

/--
  **CLOSURE for Branch (II) sub-case II-W (chi(9) = chi(24))**: if
  chi(9) = chi(24) AND chi(17) = chi(9), then (24, 9, 17) mono triple closes.
-/
theorem bAdicEquation_3_case_Y_branch_II_chi_24_17_eq_chi_9_closure
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_24 : χ 9 = χ 24) (h17_eq_9 : χ 17 = χ 9) :
    False :=
  bAdicEquation_3_rado_24_9_17_mono (n := n) χ h24 hNoMono h9_eq_24.symm h17_eq_9.symm

/--
  **(9, 1, 4) MONO TRIPLE**: chi(9) = chi(1) = chi(4) → False.
  Direct Rado triple at b=3, d=3, y=1.
-/
theorem bAdicEquation_3_rado_9_1_4_mono
    {n : ℕ} (χ : ℕ → ℕ) (h9 : 9 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_1 : χ 9 = χ 1) (h1_eq_4 : χ 1 = χ 4) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 1
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_1
  · show χ 1 = χ (1 + 3)
    rw [show (1 + 3 : ℕ) = 4 by decide]; exact h1_eq_4

/-! ### §66. Branch (II) sub-case II-V + chi(15) = chi(18) FULL CLOSURE.

  This is the FIRST FULL CLOSURE of a Branch (II) sub-sub-case via a
  21-step structural chain ending in chi(3) = chi(4) self-loop violation.

  Hypotheses: case Y, Branch II (chi(24) ≠ chi(6)), sub-case II-V
  (chi(9) = chi(18)), specific chi(15) = chi(18).

  Chain (each step uses skeleton + Rado triple):
    chi(14) = chi(24), chi(21) = chi(6), chi(22) = chi(6), chi(3) = chi(24),
    chi(19) = chi(24), chi(11) = chi(6), chi(7) = chi(18), chi(4) = chi(24)
    → chi(3) = chi(4) = chi(24) → violates self-loop xy m=1.
-/

/-- Helper Step (II-V-15V-1): derive chi(14) = chi(24) and chi(21) = chi(6). -/
theorem bAdicEquation_3_branch_II_V_15_eq_18_step1
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h15_eq_18 : χ 15 = χ 18) :
    χ 14 = χ 24 ∧ χ 21 = χ 6 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have ⟨_, _, _, _, h14_ne_6, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ (by omega) hNoMono h6_eq_12
  -- chi(14) ≠ chi(18): from (15, 9, 14) Rado, chi(15) = chi(9) = chi(18).
  have h14_ne_18 : χ 14 ≠ χ 18 := by
    intro h14_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 9
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_18, ← h9_eq_18]
    · show χ 9 = χ (9 + 5)
      rw [show (9 + 5 : ℕ) = 14 by decide, h14_eq_18, ← h9_eq_18]
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h14_eq_24 : χ 14 = χ 24 := by omega
  -- chi(21) ≠ chi(14) self-loop xz m=7.
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  -- chi(21) ≠ chi(18) from sub4 lemma (with chi(16) = chi(18) = chi(9) = chi(18)).
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h21_ne_9 : χ 21 ≠ χ 9 :=
    bAdicEquation_3_chi_21_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h9_eq_18.symm
  have h21_ne_18 : χ 21 ≠ χ 18 := by intro h; apply h21_ne_9; rw [h, ← h9_eq_18]
  have h21_ne_24 : χ 21 ≠ χ 24 := by intro h; apply h14_ne_21; rw [h14_eq_24, ← h]
  have h21_eq_6 : χ 21 = χ 6 := by omega
  exact ⟨h14_eq_24, h21_eq_6⟩

/-- Helper Step (II-V-15V-2): derive chi(22) = chi(6), chi(3) = chi(24), chi(19) = chi(24). -/
theorem bAdicEquation_3_branch_II_V_15_eq_18_step2
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h14_eq_24 : χ 14 = χ 24) (h21_eq_6 : χ 21 = χ 6) :
    χ 22 = χ 6 ∧ χ 3 = χ 24 ∧ χ 19 = χ 24 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h9_ne_12 := bAdicEquation_3_chi_9_ne_chi_12 χ (by omega) hNoMono
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h22_ne_18 := bAdicEquation_3_case_Y_chi_22_ne_chi_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  -- chi(22) ≠ chi(24): from (24, 14, 22) Rado, chi(24) = chi(14) = chi(24).
  have h22_ne_24 : χ 22 ≠ χ 24 := by
    intro h22_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 14
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h14_eq_24]
    · show χ 14 = χ (14 + 8)
      rw [show (14 + 8 : ℕ) = 22 by decide, h22_eq_24, ← h14_eq_24]
  have h22_eq_6 : χ 22 = χ 6 := by omega
  -- chi(3) ≠ chi(6): from (3, 21, 22) chi(21) = chi(22) = chi(6).
  have h3_ne_6 : χ 3 ≠ χ 6 := by
    intro h3_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 21
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h21_eq_6]
    · show χ 21 = χ (21 + 1)
      rw [show (21 + 1 : ℕ) = 22 by decide, h21_eq_6, ← h22_eq_6]
  -- chi(3) ≠ chi(18): from (18, 3, 9) chi(18) = chi(9) = chi(18).
  have h3_ne_18 : χ 3 ≠ χ 18 := by
    intro h3_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 3
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h3_eq_18]
    · show χ 3 = χ (3 + 6)
      rw [show (3 + 6 : ℕ) = 9 by decide, h9_eq_18]; exact h3_eq_18
  have h3_eq_24 : χ 3 = χ 24 := by omega
  -- chi(19) ≠ chi(6): from (6, 19, 21) Rado at b=3, d=2, y=19.
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 19
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h19_eq_6]
    · show χ 19 = χ (19 + 2)
      rw [show (19 + 2 : ℕ) = 21 by decide, h21_eq_6, ← h19_eq_6]
  -- chi(19) ≠ chi(18): from (9, 16, 19) chi(9) = chi(16) = chi(18).
  have h16_eq_9 : χ 16 = χ 9 := h16_eq_18.trans h9_eq_18.symm
  have h19_ne_9 :=
    bAdicEquation_3_chi_19_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono h16_eq_9
  have h19_ne_18 : χ 19 ≠ χ 18 := by intro h; apply h19_ne_9; rw [h, ← h9_eq_18]
  have h19_eq_24 : χ 19 = χ 24 := by omega
  exact ⟨h22_eq_6, h3_eq_24, h19_eq_24⟩

/--
  **FULL CLOSURE of Branch (II) sub-case II-V + chi(15) = chi(18)**.

  After helpers (steps 1, 2), we have:
    chi(14) = chi(24), chi(21) = chi(6), chi(22) = chi(6),
    chi(3) = chi(24), chi(19) = chi(24).

  Step 3: derive chi(11) = chi(6), chi(7) = chi(18), chi(4) = chi(24).
  Closure: chi(3) = chi(4) = chi(24) violates self-loop xy m=1.
-/
theorem bAdicEquation_3_branch_II_V_15_eq_18_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h15_eq_18 : χ 15 = χ 18) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have ⟨_, h4_ne_6, _, _, _, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ (by omega) hNoMono h6_eq_12
  -- Apply step 1 + step 2.
  have ⟨h14_eq_24, h21_eq_6⟩ :=
    bAdicEquation_3_branch_II_V_15_eq_18_step1 (n := n) χ h26 hχk hNoMono h6_eq_12 h24_ne_6
      h9_eq_18 h15_eq_18
  have ⟨h22_eq_6, h3_eq_24, h19_eq_24⟩ :=
    bAdicEquation_3_branch_II_V_15_eq_18_step2 (n := n) χ h26 hχk hNoMono h6_eq_12 h24_ne_6
      h9_eq_18 h14_eq_24 h21_eq_6
  -- Step 3: chi(11) = chi(6).
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h16_eq_9 : χ 16 = χ 9 := h16_eq_18.trans h9_eq_18.symm
  -- chi(11) ≠ chi(18): from (15, 11, 16) Rado, chi(15) = chi(16) = chi(18).
  have h11_ne_18 : χ 11 ≠ χ 18 := by
    intro h11_eq_18
    exact bAdicEquation_3_rado_15_11_16_mono (n := n) χ (by omega) hNoMono
      (h15_eq_18.trans h11_eq_18.symm) (h11_eq_18.trans h16_eq_18.symm)
  -- chi(11) ≠ chi(24): from (24, 11, 19) Rado, chi(24) = chi(19).
  have h11_ne_24 : χ 11 ≠ χ 24 := by
    intro h11_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 11
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h11_eq_24]
    · show χ 11 = χ (11 + 8)
      rw [show (11 + 8 : ℕ) = 19 by decide, h19_eq_24, ← h11_eq_24]
  have h11_eq_6 : χ 11 = χ 6 := by omega
  -- Step 4: chi(7) = chi(18).
  -- chi(7) ≠ chi(6): from (12, 7, 11) Rado, chi(12) = chi(11) = chi(6).
  have h7_ne_6 : χ 7 ≠ χ 6 := by
    intro h7_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 7
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, ← h7_eq_6]
    · show χ 7 = χ (7 + 4)
      rw [show (7 + 4 : ℕ) = 11 by decide, h11_eq_6, ← h7_eq_6]
  -- chi(7) ≠ chi(24): from (3, 7, 8) Rado, chi(3) = chi(8) = chi(24).
  have h8_eq_24 := bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h7_ne_24 : χ 7 ≠ χ 24 := by
    intro h7_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 7
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_24, ← h7_eq_24]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h8_eq_24, ← h7_eq_24]
  have h7_eq_18 : χ 7 = χ 18 := by omega
  -- Step 5: chi(4) = chi(24).
  -- chi(4) ≠ chi(18): from (9, 4, 7) Rado, chi(9) = chi(7) = chi(18).
  have h4_ne_18 : χ 4 ≠ χ 18 := by
    intro h4_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 4
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_18, ← h4_eq_18]
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h7_eq_18, ← h4_eq_18]
  have h4_eq_24 : χ 4 = χ 24 := by omega
  -- Closure: chi(3) = chi(4) = chi(24). Self-loop xy m=1 (chi(3) ≠ chi(4)) → False.
  have h3_ne_4 : χ 3 ≠ χ 4 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 1) (by omega) (by omega)
    show χ 3 ≠ χ 4
    have h' : χ (3 * 1) ≠ χ (4 * 1) := h
    intro h34
    apply h'
    show χ (3 * 1) = χ (4 * 1)
    rw [show (3 * 1 : ℕ) = 3 by decide, show (4 * 1 : ℕ) = 4 by decide]; exact h34
  apply h3_ne_4
  rw [h3_eq_24, h4_eq_24]

/-! ### §67. Branch (II) sub-case II-V + chi(15) = chi(6) FULL CLOSURE. -/

/-- Helper Step (II-V-15-6-1): derive chi(13) = chi(24), chi(19) = chi(24),
    chi(11) = chi(18), chi(14) = chi(24). -/
theorem bAdicEquation_3_branch_II_V_15_eq_6_step1
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h15_eq_6 : χ 15 = χ 6) :
    χ 13 = χ 24 ∧ χ 19 = χ 24 ∧ χ 11 = χ 18 ∧ χ 14 = χ 24 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have ⟨_, _, _, _, h14_ne_6, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ (by omega) hNoMono h6_eq_12
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h16_eq_9 : χ 16 = χ 9 := h16_eq_18.trans h9_eq_18.symm
  -- chi(13) ≠ chi(9) = chi(18): sub4 lemma.
  have h13_ne_9 :=
    bAdicEquation_3_chi_13_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono h16_eq_9
  have h13_ne_18 : χ 13 ≠ χ 18 := by intro h; apply h13_ne_9; rw [h, ← h9_eq_18]
  -- chi(13) ≠ chi(6): from (6, 13, 15) Rado, chi(15) = chi(6).
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 13
      rw [show (3 * 2 : ℕ) = 6 by decide, ← h13_eq_6]
    · show χ 13 = χ (13 + 2)
      rw [show (13 + 2 : ℕ) = 15 by decide, h15_eq_6, ← h13_eq_6]
  have h13_eq_24 : χ 13 = χ 24 := by omega
  -- chi(19) ≠ chi(18): sub4 lemma.
  have h19_ne_9 :=
    bAdicEquation_3_chi_19_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono h16_eq_9
  have h19_ne_18 : χ 19 ≠ χ 18 := by intro h; apply h19_ne_9; rw [h, ← h9_eq_18]
  -- chi(19) ≠ chi(6): from (12, 15, 19) Rado, chi(15) = chi(6) = chi(12).
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 15
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12]; exact h15_eq_6.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_6, ← h19_eq_6]
  have h19_eq_24 : χ 19 = χ 24 := by omega
  -- chi(11) ≠ chi(24): from (24, 11, 19) Rado, chi(19) = chi(24).
  have h11_ne_24 : χ 11 ≠ χ 24 := by
    intro h11_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 11
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h11_eq_24]
    · show χ 11 = χ (11 + 8)
      rw [show (11 + 8 : ℕ) = 19 by decide, h19_eq_24, ← h11_eq_24]
  -- chi(11) ≠ chi(6): from (15, 6, 11) Rado, chi(15) = chi(6).
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 6
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_6
    · show χ 6 = χ (6 + 5)
      rw [show (6 + 5 : ℕ) = 11 by decide]; exact h11_eq_6.symm
  have h11_eq_18 : χ 11 = χ 18 := by omega
  -- chi(14) ≠ chi(18): from (9, 11, 14) Rado, chi(9) = chi(11) = chi(18).
  have h14_ne_18 : χ 14 ≠ χ 18 := by
    intro h14_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 11
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_18, ← h11_eq_18]
    · show χ 11 = χ (11 + 3)
      rw [show (11 + 3 : ℕ) = 14 by decide, h14_eq_18, ← h11_eq_18]
  have h14_eq_24 : χ 14 = χ 24 := by omega
  exact ⟨h13_eq_24, h19_eq_24, h11_eq_18, h14_eq_24⟩

/-- Helper Step (II-V-15-6-2): derive chi(21) = chi(6), chi(22) = chi(6), chi(3) = chi(24),
    chi(5) = chi(6), chi(7) = chi(18), chi(4) = chi(24). -/
theorem bAdicEquation_3_branch_II_V_15_eq_6_step2
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h15_eq_6 : χ 15 = χ 6)
    (h13_eq_24 : χ 13 = χ 24) (h11_eq_18 : χ 11 = χ 18) (h14_eq_24 : χ 14 = χ 24) :
    χ 21 = χ 6 ∧ χ 22 = χ 6 ∧ χ 3 = χ 24 ∧ χ 5 = χ 6 ∧ χ 7 = χ 18 ∧ χ 4 = χ 24 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have ⟨_, h4_ne_6, h8_ne_6, _, _, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ (by omega) hNoMono h6_eq_12
  have h22_ne_18 := bAdicEquation_3_case_Y_chi_22_ne_chi_18_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h8_eq_24 := bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  -- chi(21) ≠ chi(14) = chi(24) self-loop xz m=7.
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  have h21_ne_24 : χ 21 ≠ χ 24 := by intro h; apply h14_ne_21; rw [h14_eq_24, ← h]
  -- chi(21) ≠ chi(18): from (9, 18, 21) Rado, chi(9) = chi(18).
  have h21_ne_18 : χ 21 ≠ χ 18 := by
    intro h21_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 18
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_18
    · show χ 18 = χ (18 + 3)
      rw [show (18 + 3 : ℕ) = 21 by decide]; exact h21_eq_18.symm
  have h21_eq_6 : χ 21 = χ 6 := by omega
  -- chi(22) ≠ chi(24): from (24, 14, 22) Rado, chi(14) = chi(24).
  have h22_ne_24 : χ 22 ≠ χ 24 := by
    intro h22_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 14
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h14_eq_24]
    · show χ 14 = χ (14 + 8)
      rw [show (14 + 8 : ℕ) = 22 by decide, h22_eq_24, ← h14_eq_24]
  have h22_eq_6 : χ 22 = χ 6 := by omega
  -- chi(3) ≠ chi(6): from (3, 21, 22) chi(21) = chi(22) = chi(6).
  have h3_ne_6 : χ 3 ≠ χ 6 := by
    intro h3_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 21
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h21_eq_6]
    · show χ 21 = χ (21 + 1)
      rw [show (21 + 1 : ℕ) = 22 by decide, h21_eq_6, ← h22_eq_6]
  -- chi(3) ≠ chi(18): from (18, 3, 9) chi(18) = chi(9).
  have h3_ne_18 : χ 3 ≠ χ 18 := by
    intro h3_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 3
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h3_eq_18]
    · show χ 3 = χ (3 + 6)
      rw [show (3 + 6 : ℕ) = 9 by decide, h9_eq_18]; exact h3_eq_18
  have h3_eq_24 : χ 3 = χ 24 := by omega
  -- chi(5) ≠ chi(18): from (9, 2, 5) — wait actually (9, 5, 8) since chi(8) = chi(24) ≠ chi(9).
  -- chi(5) ≠ chi(24): from (24, 5, 13) chi(13) = chi(24).
  have h5_ne_24 : χ 5 ≠ χ 24 := by
    intro h5_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 5
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h5_eq_24]
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide, h13_eq_24, ← h5_eq_24]
  -- chi(5) ≠ chi(18): from (18, 5, 11) chi(11) = chi(18).
  have h5_ne_18 : χ 5 ≠ χ 18 := by
    intro h5_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 5
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h5_eq_18]
    · show χ 5 = χ (5 + 6)
      rw [show (5 + 6 : ℕ) = 11 by decide, h11_eq_18, ← h5_eq_18]
  have h5_eq_6 : χ 5 = χ 6 := by omega
  -- chi(7) ≠ chi(6): from (6, 5, 7) chi(5) = chi(6).
  have h7_ne_6 : χ 7 ≠ χ 6 := by
    intro h7_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 5
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h5_eq_6.symm
    · show χ 5 = χ (5 + 2)
      rw [show (5 + 2 : ℕ) = 7 by decide, h7_eq_6, ← h5_eq_6]
  -- chi(7) ≠ chi(24): from (3, 7, 8) chi(3) = chi(8) = chi(24).
  have h7_ne_24 : χ 7 ≠ χ 24 := by
    intro h7_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 7
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_24, ← h7_eq_24]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h8_eq_24, ← h7_eq_24]
  have h7_eq_18 : χ 7 = χ 18 := by omega
  -- chi(4) ≠ chi(18): from (9, 4, 7) chi(9) = chi(7) = chi(18).
  have h4_ne_18 : χ 4 ≠ χ 18 := by
    intro h4_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 4
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_18, ← h4_eq_18]
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h7_eq_18, ← h4_eq_18]
  have h4_eq_24 : χ 4 = χ 24 := by omega
  exact ⟨h21_eq_6, h22_eq_6, h3_eq_24, h5_eq_6, h7_eq_18, h4_eq_24⟩

/-- **FULL CLOSURE of II-V + chi(15) = chi(6)**: chi(3) = chi(4) = chi(24)
    violates self-loop xy m=1. -/
theorem bAdicEquation_3_branch_II_V_15_eq_6_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_18 : χ 9 = χ 18) (h15_eq_6 : χ 15 = χ 6) :
    False := by
  have ⟨h13_eq_24, h19_eq_24, h11_eq_18, h14_eq_24⟩ :=
    bAdicEquation_3_branch_II_V_15_eq_6_step1 (n := n) χ h26 hχk hNoMono h6_eq_12 h24_ne_6
      h9_eq_18 h15_eq_6
  have ⟨_, _, h3_eq_24, _, _, h4_eq_24⟩ :=
    bAdicEquation_3_branch_II_V_15_eq_6_step2 (n := n) χ h26 hχk hNoMono h6_eq_12 h24_ne_6
      h9_eq_18 h15_eq_6 h13_eq_24 h11_eq_18 h14_eq_24
  -- Self-loop xy m=1: chi(3) ≠ chi(4). chi(3) = chi(4) = chi(24). Contradiction.
  have h3_ne_4 : χ 3 ≠ χ 4 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 1) (by omega) (by omega)
    show χ 3 ≠ χ 4
    have h' : χ (3 * 1) ≠ χ (4 * 1) := h
    intro h34
    apply h'
    show χ (3 * 1) = χ (4 * 1)
    rw [show (3 * 1 : ℕ) = 3 by decide, show (4 * 1 : ℕ) = 4 by decide]; exact h34
  apply h3_ne_4
  rw [h3_eq_24, h4_eq_24]

/-- **FULL CLOSURE of Branch (II) sub-case II-V**: bundles both chi(15) sub-cases. -/
theorem bAdicEquation_3_branch_II_V_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h9_eq_18 : χ 9 = χ 18) :
    False := by
  -- chi(15) ∈ {chi(6), chi(18)}: chi(15) ≠ chi(10) = chi(24) (self-loop + skeleton).
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h6_ne_18 : χ 6 ≠ χ 18 := by intro h; apply h6_ne_9; rw [h, ← h9_eq_18]
  have h10_eq_24 := bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ (by omega)
    hχk hNoMono h6_eq_12 h24_ne_6
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  have h15_ne_24 : χ 15 ≠ χ 24 := by intro h; apply h10_ne_15; rw [h10_eq_24, ← h]
  have h15_or : χ 15 = χ 6 ∨ χ 15 = χ 18 := by omega
  rcases h15_or with h15_eq_6 | h15_eq_18
  · exact bAdicEquation_3_branch_II_V_15_eq_6_contradiction (n := n) χ h26 hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_18 h15_eq_6
  · exact bAdicEquation_3_branch_II_V_15_eq_18_contradiction (n := n) χ h26 hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_18 h15_eq_18

/-! ### §68. Branch (II) sub-case II-W (chi(9) = chi(24)) FULL CLOSURE.

  Surprisingly SHORT closure compared to II-V:
  - chi(15) = chi(6): chi(17) ∈ {chi(6), chi(18)} (chi(17) ≠ chi(24)). Both sub-cases mono.
    - chi(17) = chi(18): (18, 11, 17) mono with chi(11) = chi(18).
    - chi(17) = chi(6): (15, 12, 17) mono with chi(15) = chi(12) = chi(17) = chi(6).
  - chi(15) = chi(18): chi(11) = chi(6) forced; chi(13) = chi(18) forced; (15, 13, 18) mono.
-/

/-- **CLOSURE for II-W + chi(15) = chi(6)**. chi(17) split: both sub-cases mono. -/
theorem bAdicEquation_3_branch_II_W_15_eq_6_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_24 : χ 9 = χ 24) (h15_eq_6 : χ 15 = χ 6) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have ⟨_, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  -- chi(11) ≠ chi(6) from (12, 11, 15) chi(15) = chi(6) = chi(12).
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 11
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, ← h11_eq_6]
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h15_eq_6, ← h11_eq_6]
  -- chi(11) ≠ chi(24) (R+226).
  have h11_ne_24 := bAdicEquation_3_case_Y_branch_II_chi_11_ne_chi_24_when_chi_9_eq_24
    (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6 h9_eq_24
  -- chi(11) = chi(18) (only remaining).
  have h11_eq_18 : χ 11 = χ 18 := by omega
  -- chi(17): split on chi(17) ∈ {0, 1, 2}.
  -- chi(17) ≠ chi(24) from (24, 9, 17) chi(24) = chi(9) = chi(24).
  have h17_ne_24 : χ 17 ≠ χ 24 := by
    intro h17_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 9
      rw [show (3 * 8 : ℕ) = 24 by decide]; exact h9_eq_24.symm
    · show χ 9 = χ (9 + 8)
      rw [show (9 + 8 : ℕ) = 17 by decide, h17_eq_24, ← h9_eq_24]
  -- chi(17) ∈ {chi(6), chi(18)} = {A, V}.
  have h17_or : χ 17 = χ 6 ∨ χ 17 = χ 18 := by omega
  rcases h17_or with h17_eq_6 | h17_eq_18
  · -- chi(17) = chi(6) → (15, 12, 17) mono: chi(15) = chi(12) = chi(17) = chi(6).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 12
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_6.trans h6_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_6, ← h6_eq_12]
  · -- chi(17) = chi(18) → (18, 11, 17) mono: chi(18) = chi(11) = chi(17) = chi(18).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 11
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h11_eq_18.symm
    · show χ 11 = χ (11 + 6)
      rw [show (11 + 6 : ℕ) = 17 by decide, h17_eq_18]; exact h11_eq_18

/-- **CLOSURE for II-W + chi(15) = chi(18)**: (15, 13, 18) mono via chi(11) = chi(6) → chi(13) = chi(18). -/
theorem bAdicEquation_3_branch_II_W_15_eq_18_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6)
    (h9_eq_24 : χ 9 = χ 24) (h15_eq_18 : χ 15 = χ 18) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have ⟨_, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h16_eq_18 := bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  -- chi(11) ≠ chi(18) from (15, 11, 16) chi(15) = chi(16) = chi(18).
  have h11_ne_18 : χ 11 ≠ χ 18 := by
    intro h11_eq_18
    exact bAdicEquation_3_rado_15_11_16_mono (n := n) χ (by omega) hNoMono
      (h15_eq_18.trans h11_eq_18.symm) (h11_eq_18.trans h16_eq_18.symm)
  -- chi(11) ≠ chi(24) (R+226).
  have h11_ne_24 := bAdicEquation_3_case_Y_branch_II_chi_11_ne_chi_24_when_chi_9_eq_24
    (n := n) χ h24 hχk hNoMono h6_eq_12 h24_ne_6 h9_eq_24
  -- chi(11) = chi(6).
  have h11_eq_6 : χ 11 = χ 6 := by omega
  -- chi(13) ≠ chi(6) from (6, 11, 13) chi(6) = chi(11) = chi(6).
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 11
      rw [show (3 * 2 : ℕ) = 6 by decide]; exact h11_eq_6.symm
    · show χ 11 = χ (11 + 2)
      rw [show (11 + 2 : ℕ) = 13 by decide, h13_eq_6]; exact h11_eq_6
  -- chi(13) ≠ chi(24) from (9, 10, 13) chi(9) = chi(10) = chi(24).
  have h10_eq_24 := bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have h13_ne_24 : χ 13 ≠ χ 24 := by
    intro h13_eq_24
    exact bAdicEquation_3_rado_9_10_13_mono (n := n) χ (by omega) hNoMono
      (h9_eq_24.trans h10_eq_24.symm) (h10_eq_24.trans h13_eq_24.symm)
  -- chi(13) = chi(18).
  have h13_eq_18 : χ 13 = χ 18 := by omega
  -- MONO via (15, 13, 18): chi(15) = chi(13) = chi(18).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 13
    rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_18, ← h13_eq_18]
  · show χ 13 = χ (13 + 5)
    rw [show (13 + 5 : ℕ) = 18 by decide]; exact h13_eq_18

/-- **FULL CLOSURE of Branch (II) sub-case II-W**: bundles both chi(15) sub-cases. -/
theorem bAdicEquation_3_branch_II_W_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h9_eq_24 : χ 9 = χ 24) :
    False := by
  -- chi(15) ∈ {chi(6), chi(18)}: chi(15) ≠ chi(10) = chi(24).
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  have ⟨_, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h10_eq_24 := bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6 (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  have h15_ne_24 : χ 15 ≠ χ 24 := by intro h; apply h10_ne_15; rw [h10_eq_24, ← h]
  have h15_or : χ 15 = χ 6 ∨ χ 15 = χ 18 := by omega
  rcases h15_or with h15_eq_6 | h15_eq_18
  · exact bAdicEquation_3_branch_II_W_15_eq_6_contradiction (n := n) χ h24 hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_24 h15_eq_6
  · exact bAdicEquation_3_branch_II_W_15_eq_18_contradiction (n := n) χ h24 hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_24 h15_eq_18

/-- **MASTER Branch (II) FULL CLOSURE**: case Y + chi(24) ≠ chi(6) → False. -/
theorem bAdicEquation_3_case_Y_branch_II_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) :
    False := by
  have h9_or := bAdicEquation_3_case_Y_branch_II_chi_9_split (n := n) χ (by omega) hχk hNoMono
    h6_eq_12 h24_ne_6
  rcases h9_or with h9_eq_18 | h9_eq_24
  · exact bAdicEquation_3_branch_II_V_contradiction (n := n) χ h26 hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_18
  · exact bAdicEquation_3_branch_II_W_contradiction (n := n) χ (by omega) hχk hNoMono
      h6_eq_12 h24_ne_6 h9_eq_24


/-! ### §61. STATUS: kernel-pure CompressionHyp 3 3 reduces to case Y closure.

  **Achievement summary** (as of R+217):

  (1) For any mono-free 3-coloring χ of [1, n] (n ≥ 26) for bAdicEquation 3,
      chi(6), chi(9), chi(12) cannot all be distinct
      (= bAdicEquation_3_no_chi_6_9_12_all_distinct, kernel-pure).
  (2) Combined with chi(6) ≠ chi(9) (self-loop xz m=3) and chi(9) ≠ chi(12)
      (self-loop xy m=3), this forces chi(6) = chi(12) in case Y.
  (3) In case Y: chi at {6, 9, 12} only uses 2 colors. CompressionHyp 3 3
      satisfied iff 3rd color absent at the OTHER multiples-of-3, i.e.,
      chi at {3, 15, 18, 21, 24} ⊆ {chi(6), chi(9)}.

  **Remaining for CompressionHyp 3 3 kernel-pure**: prove in case Y that
  chi at {3, 15, 18, 21, 24} ⊆ {chi(6), chi(9)}. Equivalent contrapositive:
  show 5 sub-sub-cases (one per position holding 3rd color) lead to mono.

  Toolkit ready: bAdicEquation_3_case_Y_chi_ne_chi_6_bundle gives 7 forced
  chi != chi(6) constraints. bAdicEquation_3_case_Y_chi_24_eq_chi_6_when
  _chi_16_18_distinct gives chi(24) = chi(6) in the chi(16) != chi(18)
  sub-branch. Multi-week structural enumeration remains.
-/

/--
  **MAIN RESULT (so far)**: in any mono-free 3-coloring of [1, n] (n ≥ 26)
  for bAdicEquation 3, chi(6) = chi(12).

  Direct consequence of bAdicEquation_3_no_chi_6_9_12_all_distinct:
  if chi(6) ≠ chi(12), then (chi(6), chi(9), chi(12)) all distinct (combined
  with self-loop chi(6) ≠ chi(9), chi(9) ≠ chi(12)), giving contradiction.

  KERNEL-PURE. This is the "case Y forced" lemma — the first major
  structural conclusion about mono-free 3-colorings for bAdicEquation 3.
-/
theorem bAdicEquation_3_chi_6_eq_chi_12_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 6 = χ 12 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- chi(6) ≠ chi(9) from self-loop xz m=3.
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  -- chi(9) ≠ chi(12) from self-loop xy m=3.
  have h9_ne_12 := bAdicEquation_3_chi_9_ne_chi_12 χ (by omega) hNoMono
  -- Suppose chi(6) ≠ chi(12). Then (6,9,12) all distinct → contradiction.
  by_contra h6_ne_12
  exact bAdicEquation_3_no_chi_6_9_12_all_distinct (n := n) χ h26 hχk hNoMono
    h6_ne_9 h6_ne_12 h9_ne_12

/-! ### §62. CompressionHyp 3 3 — case Y + chi(24) = 3rd color: forced chain.

  In case Y (chi(6) = chi(12)), if chi(24) ≠ chi(6) AND chi(24) ≠ chi(9),
  then chi(24) takes the 3rd color. Forces a cascade:

  - chi(16) = chi(9): from chi(24) ≠ chi(16), chi(16) ≠ chi(6), and chi(24) =
    3rd color (so chi(16) ≠ 3rd color too, forcing chi(16) = chi(9)).
  - chi(18) = chi(9): similar via chi(24) ≠ chi(18) and chi(18) ≠ chi(6).
  - chi(10) = chi(24): from (18, 10, 16) Rado, since chi(18) = chi(16) = chi(9)
    forces chi(10) ≠ chi(9); chi(10) ≠ chi(6) (bundle), so chi(10) = 3rd
    color = chi(24).

  This is the FIRST major chain in case Y sub-case enumeration toward
  CompressionHyp 3 3 closure.
-/

/--
  **chi(16) = chi(9) when case Y + chi(24) = 3rd color**.
-/
theorem bAdicEquation_3_case_Y_chi_16_eq_9_when_chi_24_third
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h24_ne_9 : χ 24 ≠ χ 9) :
    χ 16 = χ 9 := by
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have ⟨_, _, _, _, _, h16_ne_6, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ h24 hNoMono
  omega

/--
  **chi(18) = chi(9) when case Y + chi(24) = 3rd color**.
-/
theorem bAdicEquation_3_case_Y_chi_18_eq_9_when_chi_24_third
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h24_ne_9 : χ 24 ≠ χ 9) :
    χ 18 = χ 9 := by
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have ⟨_, _, _, _, _, _, h18_ne_6⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ h24 hNoMono
  omega

/--
  **chi(10) = chi(24) when case Y + chi(24) = 3rd color**.

  From the chain: chi(16) = chi(18) = chi(9) (above). Then (18, 10, 16) Rado:
  chi(18) = chi(10) = chi(16) all = chi(9) → mono. So chi(10) ≠ chi(9).
  Combined with chi(10) ≠ chi(6) (bundle), chi(10) = 3rd color = chi(24).
-/
theorem bAdicEquation_3_case_Y_chi_10_eq_24_when_chi_24_third
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h24_ne_9 : χ 24 ≠ χ 9) :
    χ 10 = χ 24 := by
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have ⟨_, _, _, h10_ne_6, _, _, _⟩ :=
    bAdicEquation_3_case_Y_chi_ne_chi_6_bundle (n := n) χ h24 hNoMono h6_eq_12
  have h16_eq_9 := bAdicEquation_3_case_Y_chi_16_eq_9_when_chi_24_third (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6 h24_ne_9
  have h18_eq_9 := bAdicEquation_3_case_Y_chi_18_eq_9_when_chi_24_third (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6 h24_ne_9
  -- chi(10) ≠ chi(9): from (18, 10, 16) Rado triple.
  have h10_ne_9 : χ 10 ≠ χ 9 :=
    bAdicEquation_3_chi_10_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h16_eq_9 h18_eq_9
  -- chi(10) < 3, ≠ chi(6), ≠ chi(9). chi(24) ≠ chi(6), chi(9). So chi(10) = chi(24).
  omega

/--
  **Case Y + chi(24) = 3rd color + chi(15) = chi(6) + chi(8) = chi(9) closure**.

  Chain: chi(16) = chi(18) = chi(9) (cascade R+219).
  chi(11) = chi(24): from (12, 11, 15) chi(11) != chi(6); (9, 8, 11) chi(11) != chi(9).
  chi(19) = chi(6): from (24, 11, 19) chi(19) != chi(24); (9, 16, 19) chi(19) != chi(9).
  MONO via (12, 15, 19): chi(12) = chi(15) = chi(19) = chi(6).
-/
theorem bAdicEquation_3_case_Y_chi_24_third_chi_15_eq_6_chi_8_eq_9_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h6_eq_12 : χ 6 = χ 12) (h24_ne_6 : χ 24 ≠ χ 6) (h24_ne_9 : χ 24 ≠ χ 9)
    (h15_eq_6 : χ 15 = χ 6) (h8_eq_9 : χ 8 = χ 9) :
    False := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h16_eq_9 := bAdicEquation_3_case_Y_chi_16_eq_9_when_chi_24_third (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6 h24_ne_9
  have h18_eq_9 := bAdicEquation_3_case_Y_chi_18_eq_9_when_chi_24_third (n := n) χ h24
    hχk hNoMono h6_eq_12 h24_ne_6 h24_ne_9
  -- chi(11) ≠ chi(6): from (12, 11, 15) Rado triple.
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 4) = χ 11
      rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, ← h11_eq_6]
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h15_eq_6, ← h11_eq_6]
  -- chi(11) ≠ chi(9): from (9, 8, 11) Rado + chi(8) = chi(9).
  have h11_ne_9 :=
    bAdicEquation_3_chi_11_ne_chi_9_in_sub4 (n := n) χ (by omega) hNoMono h8_eq_9
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have h11_eq_24 : χ 11 = χ 24 := by omega
  -- chi(19) ≠ chi(24): from (24, 11, 19) Rado triple.
  have h19_ne_24 : χ 19 ≠ χ 24 := by
    intro h19_eq_24
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 8) = χ 11
      rw [show (3 * 8 : ℕ) = 24 by decide, ← h11_eq_24]
    · show χ 11 = χ (11 + 8)
      rw [show (11 + 8 : ℕ) = 19 by decide, h19_eq_24, ← h11_eq_24]
  -- chi(19) ≠ chi(9): from sub4 lemma.
  have h19_ne_9 :=
    bAdicEquation_3_chi_19_ne_chi_9_when_chi_16_eq_9 (n := n) χ (by omega) hNoMono h16_eq_9
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have h19_eq_6 : χ 19 = χ 6 := by omega
  -- MONO via (12, 15, 19): chi(12) = chi(15) = chi(19) = chi(6).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 15
    rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12]; exact h15_eq_6.symm
  · show χ 15 = χ (15 + 4)
    rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_6, ← h19_eq_6]

/--
  **MAJOR STRUCTURAL THEOREM**: in any mono-free 3-coloring χ of [1, n]
  (n ≥ 26) for bAdicEquation 3, chi(24) = chi(6) (= chi(12)).

  Combines bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (case Y forced) with
  bAdicEquation_3_case_Y_branch_II_contradiction (Branch II contradiction).

  Direct contrapositive: chi(24) ≠ chi(6) in mono-free 3-coloring → False.

  This narrows the structure of mono-free 3-colorings drastically.
  KERNEL-PURE.
-/
theorem bAdicEquation_3_chi_24_eq_chi_6_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 24 = χ 6 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  by_cases h24_eq_6 : χ 24 = χ 6
  · exact h24_eq_6
  · exfalso
    exact bAdicEquation_3_case_Y_branch_II_contradiction (n := n) χ h26 hχk hNoMono
      h6_eq_12 h24_eq_6

/--
  **chi(20) ≠ chi(6) FORCED** in mono-free 3-coloring of [1, n] (n ≥ 26)
  for bAdicEquation 3.

  Direct consequence of chi(24) = chi(6) (R+233): the (12, 20, 24) Rado
  triple needs chi(20) ≠ chi(12) = chi(6) = chi(24) for non-mono.

  KERNEL-PURE.
-/
theorem bAdicEquation_3_chi_20_ne_chi_6_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 20 ≠ χ 6 := by
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  intro h20_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 20) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 4) = χ 20
    rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, ← h20_eq_6]
  · show χ 20 = χ (20 + 4)
    rw [show (20 + 4 : ℕ) = 24 by decide, h24_eq_6, ← h20_eq_6]

/--
  **MAJOR STRUCTURAL BUNDLE**: in any mono-free 3-coloring χ of [1, n]
  (n ≥ 26) for bAdicEquation 3, the chi values are heavily constrained:

  chi(6) = chi(12) = chi(24) (= "color A", forced)
  chi(9), chi(2), chi(4), chi(8), chi(10), chi(14), chi(16), chi(18),
  chi(20), chi(22), chi(26) ALL ≠ chi(6) (= color A)

  So chi(6) = A appears at exactly {6, 12, 24} among the even positions in
  [2, 26]. The 11 other even positions all take a non-A color (B or C).

  KERNEL-PURE summary of mono-free 3-coloring structure for bAdicEquation 3.
-/
theorem bAdicEquation_3_monoFree_structure
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 6 = χ 12 ∧ χ 24 = χ 6 ∧
    χ 2 ≠ χ 6 ∧ χ 4 ≠ χ 6 ∧ χ 8 ≠ χ 6 ∧ χ 10 ≠ χ 6 ∧
    χ 14 ≠ χ 6 ∧ χ 16 ≠ χ 6 ∧ χ 18 ≠ χ 6 ∧ χ 20 ≠ χ 6 ∧
    χ 22 ≠ χ 6 ∧ χ 26 ≠ χ 6 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have ⟨h2_ne_6, h4_ne_6, h8_ne_6, h10_ne_6, h14_ne_6, h16_ne_6, h18_ne_6, h22_ne_6, h26_ne_6⟩ :=
    bAdicEquation_3_case_Y_branch_I_chi_ne_chi_6_bundle (n := n) χ h26 hNoMono h6_eq_12 h24_eq_6
  exact ⟨h6_eq_12, h24_eq_6, h2_ne_6, h4_ne_6, h8_ne_6, h10_ne_6, h14_ne_6, h16_ne_6,
         h18_ne_6, h20_ne_6, h22_ne_6, h26_ne_6⟩

/-! ### §69. Branch (I) structural toolkit — chi(20) sub-case split.

  In Branch (I) (chi(24) = chi(6) = chi(12) = "A"), chi(20) ∈ {B, C} (both
  non-A colors). We can further split on chi(20) = chi(9) (= B) vs
  chi(20) ≠ chi(9).
-/

/--
  **chi(20) sub-case split**: in mono-free chi (Branch I), chi(20) takes
  one of 2 values: chi(20) = chi(9) (= B) or chi(20) is the 3rd color.

  Specifically: chi(20) ∈ {chi(9), c} where c is the unique value
  ∉ {chi(6), chi(9)}.

  KERNEL-PURE.
-/
theorem bAdicEquation_3_chi_20_in_chi_9_or_3rd_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 20 = χ 9 ∨ (χ 20 ≠ χ 6 ∧ χ 20 ≠ χ 9) := by
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  by_cases h20_eq_9 : χ 20 = χ 9
  · exact Or.inl h20_eq_9
  · exact Or.inr ⟨h20_ne_6, h20_eq_9⟩

/--
  **chi(18) sub-case split** in mono-free 3-coloring (Branch I).

  chi(18) ≠ chi(6) (bundle). So chi(18) ∈ {chi(9), 3rd color}.
-/
theorem bAdicEquation_3_chi_18_in_chi_9_or_3rd_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 18 = χ 9 ∨ (χ 18 ≠ χ 6 ∧ χ 18 ≠ χ 9) := by
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have ⟨_, _, _, _, _, _, _, _, h18_ne_6, _, _, _⟩ :=
    bAdicEquation_3_monoFree_structure (n := n) χ h26 hχk hNoMono
  by_cases h18_eq_9 : χ 18 = χ 9
  · exact Or.inl h18_eq_9
  · exact Or.inr ⟨h18_ne_6, h18_eq_9⟩

/-! ### §70. CONDITIONAL R_3(3) = 27 closure (explicit Branch (I) obligation). -/

/--
  **CONDITIONAL master theorem**: assuming Branch (I) closure (= case Y +
  chi(24) = chi(6) → False for any mono-free 3-coloring), there is NO mono-free
  3-coloring of [1, n] (n ≥ 26) for bAdicEquation 3.

  Combines:
  - R+218 (chi(6) = chi(12) forced).
  - R+232 (Branch II contradiction: chi(24) ≠ chi(6) → False).
  - Branch (I) hypothesis: chi(24) = chi(6) → False.

  Result: mono-free 3-coloring impossible → R_3(3) ≤ 27 (modulo bridge to
  project's IsKPartitionRegularAt).

  The hypothesis `branchIClosure` is the remaining genuine mathematical
  obligation. Not a placeholder — it states a real theorem to prove.
-/
theorem bAdicEquation_3_no_monoFree_assuming_branch_I
    {n : ℕ} (h26 : 26 ≤ n)
    (branchIClosure : ∀ χ : ℕ → ℕ, IsKColoring n 3 χ →
      ¬ HasMonoSolution (bAdicEquation 3) n χ →
      χ 24 = χ 6 → False) :
    ∀ χ : ℕ → ℕ, IsKColoring n 3 χ → HasMonoSolution (bAdicEquation 3) n χ := by
  intro χ hχk
  by_contra hNoMono
  -- chi(24) = chi(6) forced (R+233).
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  -- Apply Branch (I) closure.
  exact branchIClosure χ hχk hNoMono h24_eq_6

/-! ### §71. Branch (I) sub-case closure tools.

  Branch (I) closure requires deriving mono in sub-cases where 3rd color
  appears at chi(3), chi(15), chi(18), or chi(21) (= surjection at
  multiples-of-3).

  Key reusable mono triples for Branch (I):
  - (15, 13, 18) mono: closes chi(15) = chi(13) = chi(18) all same color
    (relevant when chi(15) = chi(18) = C, derive chi(13) = C).
  - (9, 11, 14) mono: closes chi(9) = chi(11) = chi(14) all = B = chi(9).
  - (9, 20, 23) mono: closes chi(9) = chi(20) = chi(23) all = B.
  - (9, 22, 25) mono: closes chi(9) = chi(22) = chi(25) all = B.
  - (3, 23, 24) mono: closes chi(3) = chi(23) = chi(24) all = A = chi(24).
-/

/-- **(15, 13, 18) mono**: chi(15) = chi(13) = chi(18) → False. -/
theorem bAdicEquation_3_rado_15_13_18_mono
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_13 : χ 15 = χ 13) (h13_eq_18 : χ 13 = χ 18) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 13
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_13
  · show χ 13 = χ (13 + 5)
    rw [show (13 + 5 : ℕ) = 18 by decide]; exact h13_eq_18

/-- **(9, 11, 14) mono**: chi(9) = chi(11) = chi(14) → False. -/
theorem bAdicEquation_3_rado_9_11_14_mono
    {n : ℕ} (χ : ℕ → ℕ) (h14 : 14 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_11 : χ 9 = χ 11) (h11_eq_14 : χ 11 = χ 14) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 11) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 11
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_11
  · show χ 11 = χ (11 + 3)
    rw [show (11 + 3 : ℕ) = 14 by decide]; exact h11_eq_14

/-- **(9, 20, 23) mono**: chi(9) = chi(20) = chi(23) → False. -/
theorem bAdicEquation_3_rado_9_20_23_mono
    {n : ℕ} (χ : ℕ → ℕ) (h23 : 23 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_20 : χ 9 = χ 20) (h20_eq_23 : χ 20 = χ 23) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 20) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 20
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_20
  · show χ 20 = χ (20 + 3)
    rw [show (20 + 3 : ℕ) = 23 by decide]; exact h20_eq_23

/-- **(9, 22, 25) mono**: chi(9) = chi(22) = chi(25) → False. -/
theorem bAdicEquation_3_rado_9_22_25_mono
    {n : ℕ} (χ : ℕ → ℕ) (h25 : 25 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_22 : χ 9 = χ 22) (h22_eq_25 : χ 22 = χ 25) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 22) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 22
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_22
  · show χ 22 = χ (22 + 3)
    rw [show (22 + 3 : ℕ) = 25 by decide]; exact h22_eq_25

/-- **(3, 23, 24) mono**: chi(3) = chi(23) = chi(24) → False. -/
theorem bAdicEquation_3_rado_3_23_24_mono
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_23 : χ 3 = χ 23) (h23_eq_24 : χ 23 = χ 24) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 23) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 23
    rw [show (3 * 1 : ℕ) = 3 by decide]; exact h3_eq_23
  · show χ 23 = χ (23 + 1)
    rw [show (23 + 1 : ℕ) = 24 by decide]; exact h23_eq_24

/-! ### §72. χ(27) constraints in mono-free 3-coloring (Branch I infra).

  At n ≥ 27, position 27 = 3·9 = 3^3 provides Rado triples absent at n ≤ 26.
  These are essential for closing Branch I, since the valuation coloring
  (which gives the only mono-free 3-coloring at n = 26 up to permutation)
  breaks specifically at n = 27 via the (27, 1, 10) triple.

  Triples (27, y, y+9) for y ∈ [1, 18]:
  - y = 18: degenerate → self-loop χ(27) ≠ χ(18).
  - y = 9: χ(27) = χ(9) = χ(18) impossible.
  - y ∈ {1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17}: nonmultiples-of-3 family.
  - y ∈ {3, 6, 12, 15}: multiples-of-3 family.

  All kernel-pure consequences of `bAdicEquation_general_rado_constraint`.
-/

/-- **χ(27) ≠ χ(18) FORCED**: self-loop at b=3, m=9 (requires n ≥ 27). -/
theorem bAdicEquation_3_chi_27_ne_chi_18_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 27 ≠ χ 18 := by
  have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 9) (by omega) (by omega)
  -- h : χ (2 * 9) ≠ χ (3 * 9), i.e., χ 18 ≠ χ 27.
  intro h27_eq_18
  apply h
  show χ 18 = χ 27
  exact h27_eq_18.symm

/-- **(27, y, y+9) mono triple template**: chi(27) = chi(y) = chi(y+9) → False.
  Helper for all subsequent χ(27) constraints (Branch I closure).
-/
theorem bAdicEquation_3_rado_27_y_yp9_mono
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (y : ℕ) (hy : 1 ≤ y) (hyp9 : y + 9 ≤ n)
    (h27_eq_y : χ 27 = χ y) (hy_eq_yp9 : χ y = χ (y + 9)) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := y) (by omega) hy (by omega) hyp9
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ y
    rw [show (3 * 9 : ℕ) = 27 by decide]; exact h27_eq_y
  · exact hy_eq_yp9

/-- **χ(27) ≠ χ(9) when χ(9) = χ(18)**: from (27, 9, 18) Rado triple.
  In Branch I-V (χ(9) = χ(18)), forces χ(27) into a different color.
-/
theorem bAdicEquation_3_chi_27_ne_chi_9_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 27 ≠ χ 9 := by
  intro h27_eq_9
  have h27_eq_18 : χ 27 = χ 18 := h27_eq_9.trans h9_eq_18
  exact bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono h27_eq_18

/-- **χ(27) ≠ χ(6) OR χ(15) ≠ χ(6)**: from (27, 6, 15) Rado triple. -/
theorem bAdicEquation_3_chi_27_15_not_both_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_6 : χ 27 = χ 6) (h15_eq_6 : χ 15 = χ 6) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 6 (by omega) (by omega)
    h27_eq_6 (by rw [h15_eq_6])

/-- **χ(27) ≠ χ(12) OR χ(21) ≠ χ(12)**: from (27, 12, 21) Rado triple. -/
theorem bAdicEquation_3_chi_27_21_not_both_eq_chi_12
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_12 : χ 27 = χ 12) (h21_eq_12 : χ 21 = χ 12) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 12 (by omega) (by omega)
    h27_eq_12 (by rw [h21_eq_12])

/-- **χ(27) ≠ χ(15) OR χ(24) ≠ χ(15)**: from (27, 15, 24) Rado triple. -/
theorem bAdicEquation_3_chi_27_24_not_both_eq_chi_15
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_15 : χ 27 = χ 15) (h24_eq_15 : χ 24 = χ 15) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 15 (by omega) (by omega)
    h27_eq_15 (by rw [h24_eq_15])

/-- **χ(27) ≠ χ(3) OR χ(12) ≠ χ(3)**: from (27, 3, 12) Rado triple. -/
theorem bAdicEquation_3_chi_27_12_not_both_eq_chi_3
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_3 : χ 27 = χ 3) (h12_eq_3 : χ 12 = χ 3) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 3 (by omega) (by omega)
    h27_eq_3 (by rw [h12_eq_3])

/-- **χ(27) ≠ χ(1) OR χ(10) ≠ χ(1)**: from (27, 1, 10) Rado triple.

  CRUCIAL: this is the triple that breaks the valuation coloring extension
  from [1, 26] to [1, 27]. Without it, the valuation coloring is mono-free.
-/
theorem bAdicEquation_3_chi_27_10_not_both_eq_chi_1
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_1 : χ 27 = χ 1) (h10_eq_1 : χ 10 = χ 1) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 1 (by omega) (by omega)
    h27_eq_1 (by rw [h10_eq_1])

/-- **(27, 2, 11) mono**: kills extension where χ(2) = χ(11) = χ(27). -/
theorem bAdicEquation_3_chi_27_11_not_both_eq_chi_2
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_2 : χ 27 = χ 2) (h11_eq_2 : χ 11 = χ 2) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 2 (by omega) (by omega)
    h27_eq_2 (by rw [h11_eq_2])

/-- **(27, 4, 13) mono**. -/
theorem bAdicEquation_3_chi_27_13_not_both_eq_chi_4
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_4 : χ 27 = χ 4) (h13_eq_4 : χ 13 = χ 4) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 4 (by omega) (by omega)
    h27_eq_4 (by rw [h13_eq_4])

/-- **(27, 5, 14) mono**. -/
theorem bAdicEquation_3_chi_27_14_not_both_eq_chi_5
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_5 : χ 27 = χ 5) (h14_eq_5 : χ 14 = χ 5) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 5 (by omega) (by omega)
    h27_eq_5 (by rw [h14_eq_5])

/-- **(27, 7, 16) mono**. -/
theorem bAdicEquation_3_chi_27_16_not_both_eq_chi_7
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_7 : χ 27 = χ 7) (h16_eq_7 : χ 16 = χ 7) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 7 (by omega) (by omega)
    h27_eq_7 (by rw [h16_eq_7])

/-- **(27, 8, 17) mono**. -/
theorem bAdicEquation_3_chi_27_17_not_both_eq_chi_8
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_8 : χ 27 = χ 8) (h17_eq_8 : χ 17 = χ 8) :
    False :=
  bAdicEquation_3_rado_27_y_yp9_mono (n := n) χ h27 hNoMono 8 (by omega) (by omega)
    h27_eq_8 (by rw [h17_eq_8])

/-! ### §73. Propagation lemmas: χ at multiples-of-3 forces neighbour ≠ same color.

  When χ(3k) takes a specific color c on a multiple-of-3 position 3k,
  Rado triples (3k, y, y+k) force χ(y), χ(y+k) ≠ c for specific (y, y+k)
  pairs where one of them is forced (e.g., χ(6) = A forces χ(neighbours) ≠ A
  when paired with χ(other) = A).

  These "A-class propagation" lemmas constrain WHICH positions can hold A
  in any mono-free Branch I 3-coloring. They are essential for excluding
  configurations and pinning down chi values on odd positions.
-/

/-- **χ(15) = χ(6) → χ(11) ≠ χ(6)**: Rado triple (15, 6, 11). -/
theorem bAdicEquation_3_chi_11_ne_chi_6_when_chi_15_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_6 : χ 15 = χ 6) :
    χ 11 ≠ χ 6 := by
  intro h11_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 6
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_6
  · show χ 6 = χ (6 + 5)
    rw [show (6 + 5 : ℕ) = 11 by decide, h11_eq_6]

/-- **χ(15) = χ(12) → χ(17) ≠ χ(12)**: Rado triple (15, 12, 17). -/
theorem bAdicEquation_3_chi_17_ne_chi_12_when_chi_15_eq_chi_12
    {n : ℕ} (χ : ℕ → ℕ) (h17 : 17 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_12 : χ 15 = χ 12) :
    χ 17 ≠ χ 12 := by
  intro h17_eq_12
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 12
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h15_eq_12
  · show χ 12 = χ (12 + 5)
    rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]

/-- **χ(15) = χ(24) → χ(19) ≠ χ(24)**: Rado triple (15, 19, 24). -/
theorem bAdicEquation_3_chi_19_ne_chi_24_when_chi_15_eq_chi_24
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_24 : χ 15 = χ 24) :
    χ 19 ≠ χ 24 := by
  intro h19_eq_24
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 19
    rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_24, ← h19_eq_24]
  · show χ 19 = χ (19 + 5)
    rw [show (19 + 5 : ℕ) = 24 by decide, h19_eq_24]

/-- **χ(15) = χ(6) → χ(1) ≠ χ(6)**: Rado triple (15, 1, 6). -/
theorem bAdicEquation_3_chi_1_ne_chi_6_when_chi_15_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_6 : χ 15 = χ 6) :
    χ 1 ≠ χ 6 := by
  intro h1_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 1) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 1
    rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_6, ← h1_eq_6]
  · show χ 1 = χ (1 + 5)
    rw [show (1 + 5 : ℕ) = 6 by decide, h1_eq_6]

/-- **Branch I + χ(15) = A: χ(1), χ(11), χ(17), χ(19) all ≠ A**. Bundle form.
  These force the 4 odd positions {1, 11, 17, 19} to take non-A colors in
  any Branch I mono-free with χ(15) = A.
-/
theorem bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h15_eq_6 : χ 15 = χ 6) :
    χ 1 ≠ χ 6 ∧ χ 11 ≠ χ 6 ∧ χ 17 ≠ χ 6 ∧ χ 19 ≠ χ 6 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have h1_ne_6 := bAdicEquation_3_chi_1_ne_chi_6_when_chi_15_eq_chi_6 (n := n) χ (by omega) hNoMono h15_eq_6
  have h11_ne_6 := bAdicEquation_3_chi_11_ne_chi_6_when_chi_15_eq_chi_6 (n := n) χ (by omega) hNoMono h15_eq_6
  have h15_eq_12 : χ 15 = χ 12 := h15_eq_6.trans h6_eq_12
  have h15_eq_24 : χ 15 = χ 24 := h15_eq_6.trans h24_eq_6.symm
  have h17_ne_12 := bAdicEquation_3_chi_17_ne_chi_12_when_chi_15_eq_chi_12 (n := n) χ (by omega) hNoMono h15_eq_12
  have h17_ne_6 : χ 17 ≠ χ 6 := fun h => h17_ne_12 (h.trans h6_eq_12)
  have h19_ne_24 := bAdicEquation_3_chi_19_ne_chi_24_when_chi_15_eq_chi_24 (n := n) χ (by omega) hNoMono h15_eq_24
  have h19_ne_6 : χ 19 ≠ χ 6 := fun h => h19_ne_24 (h.trans h24_eq_6.symm)
  exact ⟨h1_ne_6, h11_ne_6, h17_ne_6, h19_ne_6⟩

/-! ### §74. χ(3) propagation lemmas: χ(3) = A → odd-position forcing.

  Triples (3, y, y+1) for y ∈ {5, 6, 11, 23}: when χ(y) = A and χ(3) = A,
  triple mono unless χ(y+1) ≠ A. These give forced ≠ A on χ(6+1) = χ(7),
  χ(11+1) = χ(12) (but χ(12) = A trivially in Branch I, so this gives an
  actual constraint = no), χ(5+1) = χ(6) (= A trivially), χ(23+1) = χ(24)
  (= A trivially).

  Useful constraints from χ(3) = A:
  - (3, 5, 6): χ(3) = A = χ(5) = χ(6) = A. Need χ(5) ≠ A.
  - (3, 7, 8): χ(3) = A = χ(7) = χ(8). Conditional.
  - (3, 11, 12): χ(3) = A = χ(11) = χ(12) = A. Need χ(11) ≠ A.
  - (3, 23, 24): χ(3) = A = χ(23) = χ(24) = A. Need χ(23) ≠ A.
-/

/-- **χ(3) = χ(6) → χ(5) ≠ χ(6)**: Rado triple (3, 5, 6). -/
theorem bAdicEquation_3_chi_5_ne_chi_6_when_chi_3_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h6 : 6 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_6 : χ 3 = χ 6) :
    χ 5 ≠ χ 6 := by
  intro h5_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 5
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h5_eq_6]
  · show χ 5 = χ (5 + 1)
    rw [show (5 + 1 : ℕ) = 6 by decide, h5_eq_6]

/-- **χ(3) = χ(12) → χ(11) ≠ χ(12)**: Rado triple (3, 11, 12). -/
theorem bAdicEquation_3_chi_11_ne_chi_12_when_chi_3_eq_chi_12
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_12 : χ 3 = χ 12) :
    χ 11 ≠ χ 12 := by
  intro h11_eq_12
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 11
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_12, ← h11_eq_12]
  · show χ 11 = χ (11 + 1)
    rw [show (11 + 1 : ℕ) = 12 by decide, h11_eq_12]

/-- **χ(3) = χ(24) → χ(23) ≠ χ(24)**: Rado triple (3, 23, 24). -/
theorem bAdicEquation_3_chi_23_ne_chi_24_when_chi_3_eq_chi_24
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_24 : χ 3 = χ 24) :
    χ 23 ≠ χ 24 := by
  intro h23_eq_24
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 23) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 23
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_24, ← h23_eq_24]
  · show χ 23 = χ (23 + 1)
    rw [show (23 + 1 : ℕ) = 24 by decide, h23_eq_24]

/-- **Branch I + χ(3) = A: χ(5), χ(11), χ(23) all ≠ A**. Bundle form. -/
theorem bAdicEquation_3_chi_3_eq_A_forces_odd_ne_A
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_6 : χ 3 = χ 6) :
    χ 5 ≠ χ 6 ∧ χ 11 ≠ χ 6 ∧ χ 23 ≠ χ 6 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have h5_ne_6 := bAdicEquation_3_chi_5_ne_chi_6_when_chi_3_eq_chi_6 (n := n) χ (by omega) hNoMono h3_eq_6
  have h3_eq_12 : χ 3 = χ 12 := h3_eq_6.trans h6_eq_12
  have h11_ne_12 := bAdicEquation_3_chi_11_ne_chi_12_when_chi_3_eq_chi_12 (n := n) χ (by omega) hNoMono h3_eq_12
  have h11_ne_6 : χ 11 ≠ χ 6 := fun h => h11_ne_12 (h.trans h6_eq_12)
  have h3_eq_24 : χ 3 = χ 24 := h3_eq_6.trans h24_eq_6.symm
  have h23_ne_24 := bAdicEquation_3_chi_23_ne_chi_24_when_chi_3_eq_chi_24 (n := n) χ (by omega) hNoMono h3_eq_24
  have h23_ne_6 : χ 23 ≠ χ 6 := fun h => h23_ne_24 (h.trans h24_eq_6.symm)
  exact ⟨h5_ne_6, h11_ne_6, h23_ne_6⟩

/-! ### §75. χ(21) propagation lemmas: triples (21, y, y+7) constraints. -/

/-- **χ(21) = χ(6) → χ(13) ≠ χ(6)**: Rado triple (21, 6, 13). -/
theorem bAdicEquation_3_chi_13_ne_chi_6_when_chi_21_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h21_eq_6 : χ 21 = χ 6) :
    χ 13 ≠ χ 6 := by
  intro h13_eq_6
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 7) (y := 6) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 7) = χ 6
    rw [show (3 * 7 : ℕ) = 21 by decide]; exact h21_eq_6
  · show χ 6 = χ (6 + 7)
    rw [show (6 + 7 : ℕ) = 13 by decide, h13_eq_6]

/-- **χ(21) = χ(12) → χ(19) ≠ χ(12)**: Rado triple (21, 12, 19). -/
theorem bAdicEquation_3_chi_19_ne_chi_12_when_chi_21_eq_chi_12
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h21_eq_12 : χ 21 = χ 12) :
    χ 19 ≠ χ 12 := by
  intro h19_eq_12
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 7) (y := 12) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 7) = χ 12
    rw [show (3 * 7 : ℕ) = 21 by decide]; exact h21_eq_12
  · show χ 12 = χ (12 + 7)
    rw [show (12 + 7 : ℕ) = 19 by decide, h19_eq_12]

/-- **Branch I + χ(21) = A: χ(13), χ(19) all ≠ A**. Bundle form. -/
theorem bAdicEquation_3_chi_21_eq_A_forces_odd_ne_A
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h21_eq_6 : χ 21 = χ 6) :
    χ 13 ≠ χ 6 ∧ χ 19 ≠ χ 6 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h13_ne_6 := bAdicEquation_3_chi_13_ne_chi_6_when_chi_21_eq_chi_6 (n := n) χ (by omega) hNoMono h21_eq_6
  have h21_eq_12 : χ 21 = χ 12 := h21_eq_6.trans h6_eq_12
  have h19_ne_12 := bAdicEquation_3_chi_19_ne_chi_12_when_chi_21_eq_chi_12 (n := n) χ (by omega) hNoMono h21_eq_12
  have h19_ne_6 : χ 19 ≠ χ 6 := fun h => h19_ne_12 (h.trans h6_eq_12)
  exact ⟨h13_ne_6, h19_ne_6⟩

/-! ### §76. KEY STRUCTURAL: χ(9) = χ(18) forced in mono-free Branch I at n ≥ 27.

  Branch I-W means χ(9) ≠ χ(18), i.e., χ(9), χ(18) are the two non-A colors
  {B, C} in some order. The closure of Branch I-W (= proof that this leads
  to contradiction) is the key remaining structural obligation for kernel-pure
  CompressionHyp 3 3.

  **Status**: open. Requires multi-week structural attack analogous to Branch
  II's V/W closures (∼ 200+ lines per sub-case). The χ(27) infrastructure in
  §72 + propagation lemmas in §73-§75 are essential tools.

  Phrased positively: if proven, this gives `χ(9) = χ(18) in mono-free` —
  forcing the V branch and reducing CompressionHyp 3 3 to "χ(3), χ(15), χ(21)
  ∈ {A, χ(9)}" (the latter is also open).
-/

/-- **Sketch goal (conditional)**: If Branch I-W closes (χ(9) ≠ χ(18) → False),
  then χ(9) = χ(18) is forced in any mono-free 3-coloring of [1, n] (n ≥ 26).

  This is a clean wrapper that isolates the remaining obligation. The proof
  obligation `branchIWClosure` is the central open question. Context
  parameters (n, χ, h26, hχk, hNoMono) are listed for future expansion when
  the closure proof requires them in scope.
-/
theorem bAdicEquation_3_chi_9_eq_chi_18_in_monoFree_from_branch_I_W_closure
    {n : ℕ} (χ : ℕ → ℕ) (_h26 : 26 ≤ n)
    (_hχk : IsKColoring n 3 χ)
    (_hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (branchIWClosure : χ 9 ≠ χ 18 → False) :
    χ 9 = χ 18 := by
  by_contra h9_ne_18
  exact branchIWClosure h9_ne_18

/-! ### §77. Branch I-V key forcings: χ(9) = χ(18) implies multiples-of-3 ≠ χ(9).

  Under Branch I-V hypothesis (χ(9) = χ(18), automatic in mono-free if
  Branch I-W closes), Rado triples (18, 9, 15) and (9, 18, 21) directly
  force χ(15), χ(21) ≠ χ(9). Combined with the bundle (χ(15), χ(21) ≠ A
  is NOT yet established — they can be A), this gives:

  - χ(15), χ(21) ∈ {A, 3rd_color} where A = χ(6), 3rd_color = the color
    not in {A, χ(9)}.

  For CompressionHyp 3 3 to hold in I-V, we further need χ(15), χ(21) ∈
  {A, χ(9)}, which combined with the above means χ(15), χ(21) = A.

  These §77 lemmas establish the "≠ χ(9)" half. The "≠ 3rd_color" half
  (= χ(15), χ(21) = A) requires further structural work using §72 χ(27)
  triples + §73-75 propagation lemmas.
-/

/-- **In Branch I-V (χ(9) = χ(18)): χ(15) ≠ χ(9)**.

  Direct from Rado triple (18, 9, 15) = (3·6, 9, 15): χ(18) = χ(9) = χ(15)
  is mono. Since hypothesis gives χ(18) = χ(9), χ(15) = χ(9) would make
  all three equal.
-/
theorem bAdicEquation_3_chi_15_ne_chi_9_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h18 : 18 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 15 ≠ χ 9 := by
  intro h15_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 9
    rw [show (3 * 6 : ℕ) = 18 by decide]; exact h9_eq_18.symm
  · show χ 9 = χ (9 + 6)
    rw [show (9 + 6 : ℕ) = 15 by decide]; exact h15_eq_9.symm

/-- **In Branch I-V (χ(9) = χ(18)): χ(21) ≠ χ(9)**.

  Direct from Rado triple (9, 18, 21) = (3·3, 18, 21): χ(9) = χ(18) = χ(21)
  is mono. Since χ(9) = χ(18) by hypothesis, χ(21) = χ(9) makes mono.
-/
theorem bAdicEquation_3_chi_21_ne_chi_9_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h21 : 21 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 21 ≠ χ 9 := by
  intro h21_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 18
    rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_18
  · show χ 18 = χ (18 + 3)
    rw [show (18 + 3 : ℕ) = 21 by decide, h21_eq_9, ← h9_eq_18]

/-- **In Branch I-V (χ(9) = χ(18)): χ(3) ≠ χ(9) OR χ(12) ≠ χ(9)**.

  Triple (3·1, 12, 13) doesn't apply directly. Use (12, 6, 10)? Wait, need
  to think. Actually use (12, 9, 13)? Hmm.

  Direct Rado triple at d=4, y=9: (12, 9, 13). χ(12) = χ(9) = χ(13). χ(12) =
  A. χ(9) ≠ A. So auto.

  Try (3, 9, 12): not Rado for d=1, y=9, z=10. (3, 9, 10): χ(3) = χ(9) = χ(10).
  In I-V context: if χ(3) = χ(9) and χ(10) = χ(9), mono.
  This is a CONDITIONAL constraint, not a direct forcing of χ(3) ≠ χ(9).
-/
theorem bAdicEquation_3_chi_3_chi_10_not_both_eq_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h10 : 10 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h3_eq_9 : χ 3 = χ 9) (h10_eq_9 : χ 10 = χ 9) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 9
    rw [show (3 * 1 : ℕ) = 3 by decide]; exact h3_eq_9
  · show χ 9 = χ (9 + 1)
    rw [show (9 + 1 : ℕ) = 10 by decide, h10_eq_9]

/-- **In Branch I-V: bundle of {15, 21} ≠ χ(9) forcings**. -/
theorem bAdicEquation_3_branch_I_V_chi_15_21_ne_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 15 ≠ χ 9 ∧ χ 21 ≠ χ 9 := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi_15_ne_chi_9_when_chi_9_eq_chi_18 (n := n) χ (by omega) hNoMono h9_eq_18
  · exact bAdicEquation_3_chi_21_ne_chi_9_when_chi_9_eq_chi_18 (n := n) χ (by omega) hNoMono h9_eq_18

/-! ### §78. Status / Roadmap for kernel-pure R_3(3) = 27.

  Current architecture (as of this round):

  **PROVEN kernel-pure** (in `bAdicEquation_3_monoFree_structure`):
    χ(6) = χ(12) = χ(24) (call it A), and 11 specific even positions ∈
    [2, 26] take colors in {B, C} \\\\ {A}.

  **OPEN structural obligations** for CompressionHyp 3 3 kernel-pure:

  (1) **Branch I-W closure**: χ(9) ≠ χ(18) → False.
      Equivalent: χ(9) = χ(18) in any mono-free 3-coloring of [1, n] (n ≥ 26).
      Strategy: analogous to Branch II V/W (each ~200 lines). Uses §72 χ(27)
      triples extensively. Multi-week formalisation work.

  (2) **Branch I-V completion**: in Branch I-V (χ(9) = χ(18) = B), prove
      χ(15), χ(21), χ(3) ∈ {A, B} (i.e., ≠ 3rd_color).
      Currently we have: χ(15) ≠ B, χ(21) ≠ B (§77). So χ(15), χ(21) ∈
      {A, 3rd_color}. Must rule out the 3rd_color sub-cases.
      Strategy: similar enumeration with §73-§75 propagation tools.

  **PROVEN kernel-pure** (in this round):
    §72: χ(27) ≠ χ(18), and all (27, y, y+9) mono triple templates.
    §73-§75: "χ(15) = A → odd ≠ A" propagation bundles.
    §77: χ(15), χ(21) ≠ χ(9) in Branch I-V.
    §76: scaffold for Branch I-W closure (conditional).

  Once both obligations close, the cascade architecture in
  `isRadoNumber_radoEq_3_three_27_from_hypotheses` directly gives
  R_3(3) = 27 kernel-pure (the remaining `OmittedPairHyp 3 3` is a similar
  but separate structural obligation).
-/

/-! ### §78.5. Pure-Nat helper: third-color uniqueness.

  In any 3-color setting (values in {0, 1, 2}), if `a ≠ b` (so {a, b} =
  size-2 subset), then any `c` with `c ≠ a` and `c ≠ b` is the unique
  third value. Hence two such "third"-color values must be equal.

  Pure Presburger arithmetic — kernel-pure.
-/

private theorem third_color_eq {a b c d : ℕ}
    (hc : c < 3) (hd : d < 3) (ha : a < 3) (hb : b < 3)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    c = d := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first | rfl | omega

/-! ### §79. MAJOR Branch I-V structural result: χ(15) = χ(6) FORCED.

  Headline theorem of this round. Under Branch I-V hypothesis (χ(9) = χ(18),
  forced when Branch I-W closes), the value χ(15) MUST equal χ(6) (= A).

  Combined with §77 (χ(15) ≠ χ(9)), this nails χ(15) = A in any mono-free
  3-coloring of [1, n] (n ≥ 26) satisfying Branch I-V.

  **Significance**: this discharges 1 of 4 sub-obligations toward kernel-pure
  `CompressionHyp 3 3`. Remaining for I-V: χ(3), χ(21) ∈ {A, χ(9)} (mostly
  the third-color exclusion for χ(3); χ(21) is constrained by §77 to {A, 3rd},
  and a similar argument should give χ(21) = A).

  **Proof strategy**: Suppose χ(15) is the 3rd color (≠ A, ≠ χ(9)). Derive
  χ(10) = χ(20) = χ(9) (bundle + self-loops). Force χ(14) = χ(15) (third
  color) via triple (18,14,20). Force χ(21) = A via degenerate triple
  (21,14,21) + §77. Force χ(13) = χ(15) via (21,6,13) and (9,10,13). Then
  case-split χ(3) ∈ {3rd, χ(9), A}:
    - χ(3) = 3rd: triple (3,14,15) all equal 3rd → mono.
    - χ(3) = χ(9): triple (3,8,9) forces χ(8) ≠ χ(9). χ(8) ∈ {χ(9), 3rd}
      from bundle, so χ(8) = 3rd. Triple (15,8,13) all equal 3rd → mono.
    - χ(3) = A: cascade. Derive χ(19) = χ(9), χ(16) = 3rd, χ(11) = χ(9),
      χ(8) = 3rd via several triples. Again (15,8,13) mono.
-/

set_option maxHeartbeats 800000 in
/-- Helper for §79: in Branch I-V with χ(15) the third color, derive χ(20) = χ(9).
  χ(20) ≠ χ(6) (bundle) AND χ(20) ≠ χ(15) (self-loop) → χ(20) = χ(9).
-/
theorem bAdicEquation_3_branch_I_V_chi_20_eq_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9) :
    χ 20 = χ 9 := by
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h15_ne_20 : χ 15 ≠ χ 20 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (3 * 5) ≠ χ (4 * 5); exact h
  omega

set_option maxHeartbeats 800000 in
/-- Helper for §79: χ(10) = χ(9) similarly. -/
theorem bAdicEquation_3_branch_I_V_chi_10_eq_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9) :
    χ 10 = χ 9 := by
  -- Use the case_Y bundle which gives χ(10) ≠ χ(6) under chi(6) = chi(12).
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h10_ne_6 := bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  omega

set_option maxHeartbeats 800000 in
/-- Helper: χ(14) = χ(15) via triple (18, 14, 20). -/
theorem bAdicEquation_3_branch_I_V_chi_14_eq_chi_15
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9) :
    χ 14 = χ 15 := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h20_eq_9 := bAdicEquation_3_branch_I_V_chi_20_eq_chi_9 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 14
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h9_eq_18]; exact h14_eq_9.symm
    · show χ 14 = χ (14 + 6)
      rw [show (14 + 6 : ℕ) = 20 by decide, h20_eq_9, ← h14_eq_9]
  -- χ(14), χ(15) both ≠ χ(6) and ≠ χ(9); all < 3; χ(6) ≠ χ(9). Force χ(14) = χ(15).
  exact third_color_eq hχ14 hχ15 hχ6 hχ9 h6_ne_9 h14_ne_6 h14_ne_9 h15_ne_6 h15_ne_9

set_option maxHeartbeats 800000 in
/-- Helper: χ(21) = χ(6) via self-loop (21,14,21) + §77. -/
theorem bAdicEquation_3_branch_I_V_chi_21_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9) :
    χ 21 = χ 6 := by
  have h14_eq_15 := bAdicEquation_3_branch_I_V_chi_14_eq_chi_15 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have h21_ne_9 := bAdicEquation_3_chi_21_ne_chi_9_when_chi_9_eq_chi_18
    (n := n) χ (by omega) hNoMono h9_eq_18
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  have h21_ne_15 : χ 21 ≠ χ 15 := fun h => h14_ne_21 (h14_eq_15.trans h.symm)
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  -- χ(21), χ(6) both ≠ χ(9), ≠ χ(15). χ(9) ≠ χ(15). All < 3. Force χ(21) = χ(6).
  exact third_color_eq hχ21 hχ6 hχ9 hχ15 h15_ne_9.symm h21_ne_9 h21_ne_15
    h6_ne_9 h15_ne_6.symm

set_option maxHeartbeats 800000 in
/-- Helper: χ(13) = χ(15) via (21,6,13) + (9,10,13). -/
theorem bAdicEquation_3_branch_I_V_chi_13_eq_chi_15
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9) :
    χ 13 = χ 15 := by
  have h21_eq_6 := bAdicEquation_3_branch_I_V_chi_21_eq_chi_6 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have h10_eq_9 := bAdicEquation_3_branch_I_V_chi_10_eq_chi_9 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h13_ne_6 : χ 13 ≠ χ 6 := by
    intro h13_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 6
      rw [show (3 * 7 : ℕ) = 21 by decide]; exact h21_eq_6
    · show χ 6 = χ (6 + 7)
      rw [show (6 + 7 : ℕ) = 13 by decide, h13_eq_6]
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 10
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h10_eq_9.symm
    · show χ 10 = χ (10 + 3)
      rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_9, h13_eq_9]
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  exact third_color_eq hχ13 hχ15 hχ6 hχ9 h6_ne_9 h13_ne_6 h13_ne_9 h15_ne_6 h15_ne_9

set_option maxHeartbeats 400000 in
/-- Helper: mono triple (15, 8, 13). Need n ≥ 15 (for x=15) and n ≥ 13 (for z=13). -/
theorem bAdicEquation_3_branch_I_V_mono_15_8_13
    {n : ℕ} (χ : ℕ → ℕ) (h15 : 15 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h8_eq_15 : χ 8 = χ 15) (h13_eq_15 : χ 13 = χ 15) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 5) = χ 8
    rw [show (3 * 5 : ℕ) = 15 by decide]; exact h8_eq_15.symm
  · show χ 8 = χ (8 + 5)
    rw [show (8 + 5 : ℕ) = 13 by decide, h8_eq_15, h13_eq_15]

set_option maxHeartbeats 800000 in
/-- Helper for case χ(3) = χ(15) third color: triple (3, 14, 15) mono. -/
theorem bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_15
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9)
    (h3_eq_15 : χ 3 = χ 15) :
    False := by
  have h14_eq_15 := bAdicEquation_3_branch_I_V_chi_14_eq_chi_15 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 14) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 1) = χ 14
    rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_15, ← h14_eq_15]
  · show χ 14 = χ (14 + 1)
    rw [show (14 + 1 : ℕ) = 15 by decide, h14_eq_15]

set_option maxHeartbeats 800000 in
/-- Helper for case χ(3) = χ(9): derive χ(8) = χ(15) via (3,8,9). -/
theorem bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_9
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9)
    (h3_eq_9 : χ 3 = χ 9) :
    False := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  -- χ(8) ≠ χ(12) = χ(6) via self-loop m=4.
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  have h13_eq_15 := bAdicEquation_3_branch_I_V_chi_13_eq_chi_15 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h8_ne_9 : χ 8 ≠ χ 9 := by
    intro h8_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 8
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h8_eq_9]
    · show χ 8 = χ (8 + 1)
      rw [show (8 + 1 : ℕ) = 9 by decide, h8_eq_9]
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h8_eq_15 : χ 8 = χ 15 := third_color_eq hχ8 hχ15 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h15_ne_6 h15_ne_9
  exact bAdicEquation_3_branch_I_V_mono_15_8_13 (n := n) χ (by omega) hNoMono h8_eq_15 h13_eq_15

set_option maxHeartbeats 1600000 in
/-- Helper for case χ(3) = χ(6): the deep cascade derivation. -/
theorem bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_6
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h15_ne_6 : χ 15 ≠ χ 6) (h15_ne_9 : χ 15 ≠ χ 9)
    (h3_eq_6 : χ 3 = χ 6) :
    False := by
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ h26 hχk hNoMono
  have h14_eq_15 := bAdicEquation_3_branch_I_V_chi_14_eq_chi_15 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have h21_eq_6 := bAdicEquation_3_branch_I_V_chi_21_eq_chi_6 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have h13_eq_15 := bAdicEquation_3_branch_I_V_chi_13_eq_chi_15 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  -- χ(19) ≠ χ(15) via (15, 14, 19).
  have h19_ne_15 : χ 19 ≠ χ 15 := by
    intro h19_eq_15
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 14
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h14_eq_15.symm
    · show χ 14 = χ (14 + 5)
      rw [show (14 + 5 : ℕ) = 19 by decide, h14_eq_15, ← h19_eq_15]
  -- χ(19) ≠ χ(6) via (21, 12, 19).
  have h19_ne_6 : χ 19 ≠ χ 6 := by
    intro h19_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 12
      rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_6, h6_eq_12]
    · show χ 12 = χ (12 + 7)
      rw [show (12 + 7 : ℕ) = 19 by decide, h19_eq_6, h6_eq_12]
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h19_eq_9 : χ 19 = χ 9 := third_color_eq hχ19 hχ9 hχ15 hχ6 h15_ne_6
    h19_ne_15 h19_ne_6 h15_ne_9.symm h6_ne_9.symm
  -- χ(16) ≠ χ(9) via (9, 16, 19).
  have h16_ne_9 : χ 16 ≠ χ 9 := by
    intro h16_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 16
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h16_eq_9.symm
    · show χ 16 = χ (16 + 3)
      rw [show (16 + 3 : ℕ) = 19 by decide, h19_eq_9, ← h16_eq_9]
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ (by omega) hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ h26 hχk hNoMono
  have h16_ne_6 : χ 16 ≠ χ 6 := fun h => h16_ne_24 (h.trans h24_eq_6.symm)
  have h16_eq_15 : χ 16 = χ 15 := third_color_eq hχ16 hχ15 hχ6 hχ9 h6_ne_9 h16_ne_6
    h16_ne_9 h15_ne_6 h15_ne_9
  -- χ(11) ≠ χ(6) via (3, 11, 12).
  have h11_ne_6 : χ 11 ≠ χ 6 := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 11
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h11_eq_6]
    · show χ 11 = χ (11 + 1)
      rw [show (11 + 1 : ℕ) = 12 by decide, h11_eq_6, h6_eq_12]
  -- χ(11) ≠ χ(15) via (15, 11, 16).
  have h11_ne_15 : χ 11 ≠ χ 15 := by
    intro h11_eq_15
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 11
      rw [show (3 * 5 : ℕ) = 15 by decide]; exact h11_eq_15.symm
    · show χ 11 = χ (11 + 5)
      rw [show (11 + 5 : ℕ) = 16 by decide, h11_eq_15, h16_eq_15]
  have h11_eq_9 : χ 11 = χ 9 := third_color_eq hχ11 hχ9 hχ15 hχ6 h15_ne_6
    h11_ne_15 h11_ne_6 h15_ne_9.symm h6_ne_9.symm
  -- χ(8) ≠ χ(9) via (9, 8, 11).
  have h8_ne_9 : χ 8 ≠ χ 9 := by
    intro h8_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 8
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h8_eq_9.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_9, h11_eq_9]
  -- χ(8) ≠ χ(12) = χ(6) via self-loop m=4.
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  have h8_eq_15 : χ 8 = χ 15 := third_color_eq hχ8 hχ15 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9
    h15_ne_6 h15_ne_9
  exact bAdicEquation_3_branch_I_V_mono_15_8_13 (n := n) χ (by omega) hNoMono h8_eq_15 h13_eq_15

set_option maxHeartbeats 800000 in
/-- **MAJOR: χ(15) = χ(6) in Branch I-V**.

  In any mono-free 3-coloring χ of [1, n] (n ≥ 26) for `bAdicEquation 3`,
  if χ(9) = χ(18) (Branch I-V hypothesis, automatic when Branch I-W closes),
  then χ(15) = χ(6).

  Equivalently: χ(15) lies in {χ(6), χ(9)} (since trichotomy + §77's
  χ(15) ≠ χ(9) leaves only χ(15) = χ(6)).

  Kernel-pure. Self-contained from §77 + general Rado constraint. Uses no
  χ(27) infra. Works at n ≥ 26.
-/
theorem bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 15 = χ 6 := by
  by_contra h15_ne_6
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have h15_ne_9 := bAdicEquation_3_chi_15_ne_chi_9_when_chi_9_eq_chi_18
    (n := n) χ (by omega) hNoMono h9_eq_18
  -- Case split on χ(3) ∈ {χ(15) (3rd), χ(9), χ(6)}.
  by_cases h3_eq_15 : χ 3 = χ 15
  · exact bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_15 (n := n) χ h26 hχk hNoMono
      h9_eq_18 h15_ne_6 h15_ne_9 h3_eq_15
  by_cases h3_eq_9 : χ 3 = χ 9
  · exact bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_9 (n := n) χ h26 hχk hNoMono
      h9_eq_18 h15_ne_6 h15_ne_9 h3_eq_9
  -- χ(3) ≠ χ(15), ≠ χ(9). χ(3) < 3. χ(6) < 3, χ(6) ≠ χ(9) and χ(6) ≠ χ(15).
  -- So χ(3) = χ(6).
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h3_eq_6 : χ 3 = χ 6 := by omega
  exact bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_6 (n := n) χ h26 hχk hNoMono
    h9_eq_18 h15_ne_6 h15_ne_9 h3_eq_6

/-! ### §80. MAJOR Branch I-V structural result: χ(21) = χ(6) FORCED at n ≥ 27.

  Builds on §79's `chi_15_eq_chi_6_when_chi_9_eq_chi_18`. Closes the 2nd of 4
  Branch I-V sub-obligations toward kernel-pure `CompressionHyp 3 3`.

  **Strategy**: by_contra. Suppose χ(21) is the third color (≠ χ(6), ≠ χ(9)).
  Derive an 8-step cascade ending in mono triple (27, 8, 17), all three
  equal to the third color.

  Cascade chain:
    χ(14) = χ(9) via self-loop χ(14) ≠ χ(21) + bundle χ(14) ≠ χ(6).
    χ(20) = χ(21) via (18, 14, 20) Rado: forces χ(20) ≠ χ(9).
    χ(17) = χ(21) via (9, 14, 17) + §73 χ(17) ≠ χ(6) (from χ(15) = χ(6)).
    χ(10) = χ(9) via (21, 10, 17) Rado: forces χ(10) ≠ χ(21).
    χ(13) = χ(6) via (9, 10, 13) + (21, 13, 20) Rado.
    χ(3) = χ(9) via (3, 12, 13) + (3, 20, 21) Rado.
    χ(8) = χ(21) via (3, 8, 9) Rado: forces χ(8) ≠ χ(9); bundle χ(8) ≠ χ(6).
    χ(27) = χ(21) via self-loop χ(27) ≠ χ(18) + (27, 6, 15): χ(27) ≠ χ(6).
    MONO (27, 8, 17) : χ(27) = χ(8) = χ(17) = χ(21).

  Requires n ≥ 27 for χ(27) infrastructure.
-/

set_option maxHeartbeats 3200000 in
/-- **MAJOR: χ(21) = χ(6) in Branch I-V at n ≥ 27**.

  In any mono-free 3-coloring χ of [1, n] (n ≥ 27) for `bAdicEquation 3`,
  if χ(9) = χ(18) (Branch I-V hypothesis), then χ(21) = χ(6).

  Equivalently: χ(21) lies in {χ(6), χ(9)} (since §77 gives χ(21) ≠ χ(9)).

  Kernel-pure. Uses §72 χ(27) triple (27, 8, 17) — the FIRST non-trivial use
  of §72 infrastructure for actual closure. Validates the χ(27) build-out.
-/
theorem bAdicEquation_3_chi_21_eq_chi_6_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 21 = χ 6 := by
  by_contra h21_ne_6
  -- Setup: extract previously-proven facts.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h15_eq_6 := bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18 (n := n) χ (by omega)
    hχk hNoMono h9_eq_18
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h21_ne_9 := bAdicEquation_3_chi_21_ne_chi_9_when_chi_9_eq_chi_18 (n := n) χ (by omega)
    hNoMono h9_eq_18
  -- Bundles for χ(*) ≠ χ(6).
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h10_ne_6 := bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  -- χ(17) ≠ χ(6) from §73 propagation.
  have ⟨_h1_ne_6, h11_ne_6, h17_ne_6, h19_ne_6⟩ :=
    bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h15_eq_6
  -- All chi values < 3.
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  have h8_ne_6 : χ 8 ≠ χ 6 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    -- h : χ(8) ≠ χ(12).
    show χ 8 ≠ χ 6
    intro heq; apply h
    show χ (2 * 4) = χ (3 * 4); rw [show (2 * 4 : ℕ) = 8 by decide, show (3 * 4 : ℕ) = 12 by decide]
    exact heq.trans h6_eq_12
  -- STEP 1: χ(14) = χ(9) via self-loop χ(14) ≠ χ(21).
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ6 hχ21 (Ne.symm h21_ne_6) h14_ne_6 h14_ne_21 (Ne.symm h6_ne_9) (Ne.symm h21_ne_9)
  -- STEP 2: χ(20) = χ(21) via (18, 14, 20) forces χ(20) ≠ χ(9).
  have h20_ne_9 : χ 20 ≠ χ 9 := by
    intro h20_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 14
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h9_eq_18, ← h14_eq_9]
    · show χ 14 = χ (14 + 6)
      rw [show (14 + 6 : ℕ) = 20 by decide, h20_eq_9, h14_eq_9]
  have h20_eq_21 : χ 20 = χ 21 :=
    third_color_eq hχ20 hχ21 hχ6 hχ9 h6_ne_9 h20_ne_6 h20_ne_9 h21_ne_6 h21_ne_9
  -- STEP 3: χ(17) = χ(21) via (9, 14, 17) forces χ(17) ≠ χ(9); χ(17) ≠ χ(6).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 14
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h14_eq_9.symm
    · show χ 14 = χ (14 + 3)
      rw [show (14 + 3 : ℕ) = 17 by decide, h14_eq_9, h17_eq_9]
  have h17_eq_21 : χ 17 = χ 21 :=
    third_color_eq hχ17 hχ21 hχ6 hχ9 h6_ne_9 h17_ne_6 h17_ne_9 h21_ne_6 h21_ne_9
  -- STEP 4: χ(10) = χ(9) via (21, 10, 17) forces χ(10) ≠ χ(21).
  have h10_ne_21 : χ 10 ≠ χ 21 := by
    intro h10_eq_21
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 10
      rw [show (3 * 7 : ℕ) = 21 by decide, ← h10_eq_21]
    · show χ 10 = χ (10 + 7)
      rw [show (10 + 7 : ℕ) = 17 by decide, h17_eq_21, ← h10_eq_21]
  have h10_eq_9 : χ 10 = χ 9 :=
    third_color_eq hχ10 hχ9 hχ6 hχ21 (Ne.symm h21_ne_6) h10_ne_6 h10_ne_21 (Ne.symm h6_ne_9) (Ne.symm h21_ne_9)
  -- STEP 5: χ(13) = χ(6) via (9, 10, 13) + (21, 13, 20).
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 10
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h10_eq_9.symm
    · show χ 10 = χ (10 + 3)
      rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_9, h13_eq_9]
  have h13_ne_21 : χ 13 ≠ χ 21 := by
    intro h13_eq_21
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 13
      rw [show (3 * 7 : ℕ) = 21 by decide]; exact h13_eq_21.symm
    · show χ 13 = χ (13 + 7)
      rw [show (13 + 7 : ℕ) = 20 by decide, h13_eq_21, h20_eq_21]
  have h13_eq_6 : χ 13 = χ 6 :=
    third_color_eq hχ13 hχ6 hχ9 hχ21 (Ne.symm h21_ne_9) h13_ne_9 h13_ne_21 h6_ne_9 (Ne.symm h21_ne_6)
  -- STEP 6: χ(3) = χ(9) via (3, 12, 13) + (3, 20, 21).
  have h3_ne_6 : χ 3 ≠ χ 6 := by
    intro h3_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 12
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, h6_eq_12]
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_6, ← h6_eq_12]
  have h3_ne_21 : χ 3 ≠ χ 21 := by
    intro h3_eq_21
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 20
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_21, ← h20_eq_21]
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_21]
  have h3_eq_9 : χ 3 = χ 9 :=
    third_color_eq hχ3 hχ9 hχ6 hχ21 (Ne.symm h21_ne_6) h3_ne_6 h3_ne_21 (Ne.symm h6_ne_9) (Ne.symm h21_ne_9)
  -- STEP 7: χ(8) = χ(21) via (3, 8, 9) forces χ(8) ≠ χ(9).
  have h8_ne_9 : χ 8 ≠ χ 9 := by
    intro h8_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 8
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h8_eq_9]
    · show χ 8 = χ (8 + 1)
      rw [show (8 + 1 : ℕ) = 9 by decide, h8_eq_9]
  have h8_eq_21 : χ 8 = χ 21 :=
    third_color_eq hχ8 hχ21 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h21_ne_6 h21_ne_9
  -- STEP 8: χ(27) = χ(21) via self-loop + (27, 6, 15).
  have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
  have h27_ne_9 : χ 27 ≠ χ 9 := fun h => h27_ne_18 (h.trans h9_eq_18)
  have h27_ne_6 : χ 27 ≠ χ 6 := by
    intro h27_eq_6
    exact bAdicEquation_3_chi_27_15_not_both_eq_chi_6 (n := n) χ h27 hNoMono h27_eq_6 h15_eq_6
  have h27_eq_21 : χ 27 = χ 21 :=
    third_color_eq hχ27 hχ21 hχ6 hχ9 h6_ne_9 h27_ne_6 h27_ne_9 h21_ne_6 h21_ne_9
  -- FINAL: mono triple (27, 8, 17) all equal χ(21).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 8
    rw [show (3 * 9 : ℕ) = 27 by decide, h27_eq_21, ← h8_eq_21]
  · show χ 8 = χ (8 + 9)
    rw [show (8 + 9 : ℕ) = 17 by decide, h8_eq_21, h17_eq_21]

/-! ### §81. MAJOR Branch I-V structural result: χ(3) = χ(6) FORCED at n ≥ 27.

  Closes 3rd of 3 Branch I-V multiples-of-3 sub-obligations ( closed χ(15)=A,
   closed χ(21)=A, this round closes χ(3)=A). After this round, Branch I-V
  fully discharges `CompressionHyp 3 3`'s requirement that multiples-of-3 ⊆
  {χ(6), χ(9)}.

  Two sub-cases:
  - **Sub-case A** (χ(3) = χ(9)): cascade χ(8), χ(17), χ(27) all = third color.
    Mono triple (27, 8, 17) → False.
  - **Sub-case B** (χ(3) = third color): cascade χ(5), χ(14), χ(27) all = third color.
    Mono triple (27, 5, 14) → False.
-/

set_option maxHeartbeats 1600000 in
/-- **Sub-case A**: in Branch I-V, χ(3) = χ(9) → False. Cascade ends at (27, 8, 17). -/
theorem bAdicEquation_3_chi_3_eq_chi_9_in_branch_I_V_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h3_eq_9 : χ 3 = χ 9) :
    False := by
  -- Setup: extract prior facts.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h15_eq_6 := bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18 (n := n) χ (by omega)
    hχk hNoMono h9_eq_18
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  -- χ(17) ≠ χ(6) from §73 (chi_15 = A propagation).
  have ⟨_h1_ne_6, _h11_ne_6, h17_ne_6, _h19_ne_6⟩ :=
    bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h15_eq_6
  -- χ(8) ≠ χ(6) from self-loop χ(8) ≠ χ(12) + χ(12) = χ(6).
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  -- χ values < 3.
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  -- χ(8) ≠ χ(9) via triple (3, 8, 9): χ(3) = χ(9) = χ(8) → mono.
  have h8_ne_9 : χ 8 ≠ χ 9 := by
    intro h8_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 8
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h8_eq_9]
    · show χ 8 = χ (8 + 1)
      rw [show (8 + 1 : ℕ) = 9 by decide, h8_eq_9]
  -- χ(17) ≠ χ(9) via triple (3, 17, 18) with χ(3) = χ(9) = χ(18).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 17
      rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 1)
      rw [show (17 + 1 : ℕ) = 18 by decide, h17_eq_9, h9_eq_18]
  -- χ(27) ≠ χ(9) via self-loop χ(27) ≠ χ(18) + h9_eq_18.
  have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
  have h27_ne_9 : χ 27 ≠ χ 9 := fun h => h27_ne_18 (h.trans h9_eq_18)
  -- χ(27) ≠ χ(6) via (27, 6, 15) with χ(15) = χ(6).
  have h27_ne_6 : χ 27 ≠ χ 6 := by
    intro h27_eq_6
    exact bAdicEquation_3_chi_27_15_not_both_eq_chi_6 (n := n) χ h27 hNoMono h27_eq_6 h15_eq_6
  -- third_color_eq: χ(8) = χ(27) (both = third color, ≠ χ(6) and ≠ χ(9)).
  have h8_eq_27 : χ 8 = χ 27 :=
    third_color_eq hχ8 hχ27 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h27_ne_6 h27_ne_9
  -- third_color_eq: χ(17) = χ(27).
  have h17_eq_27 : χ 17 = χ 27 :=
    third_color_eq hχ17 hχ27 hχ6 hχ9 h6_ne_9 h17_ne_6 h17_ne_9 h27_ne_6 h27_ne_9
  -- MONO (27, 8, 17): all = χ(27).
  exact bAdicEquation_3_chi_27_17_not_both_eq_chi_8 (n := n) χ h27 hNoMono
    (Eq.symm h8_eq_27) (h17_eq_27.trans (Eq.symm h8_eq_27))

set_option maxHeartbeats 3200000 in
/-- **Sub-case B**: in Branch I-V, χ(3) = third color (≠ χ(6), ≠ χ(9)) → False.
  Cascade derives χ(5), χ(14), χ(27) all = χ(3). Mono triple (27, 5, 14). -/
theorem bAdicEquation_3_chi_3_third_in_branch_I_V_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) (h3_ne_6 : χ 3 ≠ χ 6) (h3_ne_9 : χ 3 ≠ χ 9) :
    False := by
  -- Setup.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h15_eq_6 := bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18 (n := n) χ (by omega)
    hχk hNoMono h9_eq_18
  have h21_eq_6 := bAdicEquation_3_chi_21_eq_chi_6_when_chi_9_eq_chi_18 (n := n) χ h27
    hχk hNoMono h9_eq_18
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have ⟨_h1_ne_6, _h11_ne_6, h17_ne_6, _h19_ne_6⟩ :=
    bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h15_eq_6
  -- Bundles for χ(*) ≠ χ(6).
  have h2_ne_6 := bAdicEquation_3_chi_2_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h10_ne_6 := bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  -- χ values < 3.
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  -- STEP 1: χ(2) = χ(9) (self-loop χ(2) ≠ χ(3) + bundle).
  have h2_ne_3 : χ 2 ≠ χ 3 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 1) (by omega) (by omega)
    show χ (2 * 1) ≠ χ (3 * 1); exact h
  have h2_eq_9 : χ 2 = χ 9 :=
    third_color_eq hχ2 hχ9 hχ6 hχ3 (Ne.symm h3_ne_6) h2_ne_6 h2_ne_3 (Ne.symm h6_ne_9) (Ne.symm h3_ne_9)
  -- STEP 2: χ(27) = χ(3).
  have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
  have h27_ne_9 : χ 27 ≠ χ 9 := fun h => h27_ne_18 (h.trans h9_eq_18)
  have h27_ne_6 : χ 27 ≠ χ 6 := by
    intro h27_eq_6
    exact bAdicEquation_3_chi_27_15_not_both_eq_chi_6 (n := n) χ h27 hNoMono h27_eq_6 h15_eq_6
  have h27_eq_3 : χ 27 = χ 3 :=
    third_color_eq hχ27 hχ3 hχ6 hχ9 h6_ne_9 h27_ne_6 h27_ne_9 h3_ne_6 h3_ne_9
  -- STEP 3: χ(8) = χ(3) via (18, 2, 8) with χ(2) = χ(9) = χ(18).
  have h8_ne_9 : χ 8 ≠ χ 9 := by
    intro h8_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 2
      rw [show (3 * 6 : ℕ) = 18 by decide, ← h9_eq_18, ← h2_eq_9]
    · show χ 2 = χ (2 + 6)
      rw [show (2 + 6 : ℕ) = 8 by decide, h8_eq_9, h2_eq_9]
  have h8_eq_3 : χ 8 = χ 3 :=
    third_color_eq hχ8 hχ3 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h3_ne_6 h3_ne_9
  -- STEP 4: χ(17) = χ(9) via (27, 8, 17) forces χ(17) ≠ χ(3).
  have h17_ne_3 : χ 17 ≠ χ 3 := by
    intro h17_eq_3
    exact bAdicEquation_3_chi_27_17_not_both_eq_chi_8 (n := n) χ h27 hNoMono
      (h27_eq_3.trans (Eq.symm h8_eq_3)) (h17_eq_3.trans (Eq.symm h8_eq_3))
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ6 hχ3 (Ne.symm h3_ne_6) h17_ne_6 h17_ne_3 (Ne.symm h6_ne_9) (Ne.symm h3_ne_9)
  -- STEP 5: χ(14) = χ(3) via (9, 14, 17) with χ(9) = χ(17) forces χ(14) ≠ χ(9).
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 14
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h14_eq_9.symm
    · show χ 14 = χ (14 + 3)
      rw [show (14 + 3 : ℕ) = 17 by decide, h17_eq_9, h14_eq_9]
  have h14_eq_3 : χ 14 = χ 3 :=
    third_color_eq hχ14 hχ3 hχ6 hχ9 h6_ne_9 h14_ne_6 h14_ne_9 h3_ne_6 h3_ne_9
  -- STEP 6: χ(7) = χ(9).
  have h7_ne_6 : χ 7 ≠ χ 6 := by
    intro h7_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 7
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_6, ← h7_eq_6]
    · show χ 7 = χ (7 + 5)
      rw [show (7 + 5 : ℕ) = 12 by decide, ← h6_eq_12, h7_eq_6]
  have h7_ne_3 : χ 7 ≠ χ 3 := by
    intro h7_eq_3
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 1) = χ 7
      rw [show (3 * 1 : ℕ) = 3 by decide]; exact h7_eq_3.symm
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h8_eq_3, h7_eq_3]
  have h7_eq_9 : χ 7 = χ 9 :=
    third_color_eq hχ7 hχ9 hχ6 hχ3 (Ne.symm h3_ne_6) h7_ne_6 h7_ne_3 (Ne.symm h6_ne_9) (Ne.symm h3_ne_9)
  -- STEP 7: χ(5) = χ(3).
  have h5_ne_6 : χ 5 ≠ χ 6 := by
    intro h5_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 5
      rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_6, ← h5_eq_6]
    · show χ 5 = χ (5 + 7)
      rw [show (5 + 7 : ℕ) = 12 by decide, ← h6_eq_12, h5_eq_6]
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 2
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h2_eq_9.symm
    · show χ 2 = χ (2 + 3)
      rw [show (2 + 3 : ℕ) = 5 by decide, h5_eq_9, h2_eq_9]
  have h5_eq_3 : χ 5 = χ 3 :=
    third_color_eq hχ5 hχ3 hχ6 hχ9 h6_ne_9 h5_ne_6 h5_ne_9 h3_ne_6 h3_ne_9
  -- STEP 8 (optional, not needed): χ(10) = χ(3). We don't need it.
  -- FINAL: MONO (27, 5, 14): all = χ(3).
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 5
    rw [show (3 * 9 : ℕ) = 27 by decide, h27_eq_3, ← h5_eq_3]
  · show χ 5 = χ (5 + 9)
    rw [show (5 + 9 : ℕ) = 14 by decide, h5_eq_3, ← h14_eq_3]

set_option maxHeartbeats 800000 in
/-- **MAJOR: χ(3) = χ(6) in Branch I-V at n ≥ 27**.

  Closes 3rd of 3 Branch I-V multiples-of-3 sub-obligations. After this round,
  in any mono-free 3-coloring χ of [1, n] (n ≥ 27) for `bAdicEquation 3` with
  χ(9) = χ(18), multiples {3, 6, 9, 12, 15, 18, 21, 24} all ⊆ {χ(6), χ(9)} —
  i.e., the third color is OMITTED at multiples-of-3 in [3, 24]. Combined with
  Branch I-W closure (still open), this discharges `CompressionHyp 3 3`.
-/
theorem bAdicEquation_3_chi_3_eq_chi_6_when_chi_9_eq_chi_18
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_eq_18 : χ 9 = χ 18) :
    χ 3 = χ 6 := by
  by_contra h3_ne_6
  by_cases h3_eq_9 : χ 3 = χ 9
  · exact bAdicEquation_3_chi_3_eq_chi_9_in_branch_I_V_contradiction
      (n := n) χ h27 hχk hNoMono h9_eq_18 h3_eq_9
  · exact bAdicEquation_3_chi_3_third_in_branch_I_V_contradiction
      (n := n) χ h27 hχk hNoMono h9_eq_18 h3_ne_6 h3_eq_9

/-! ### §82. **HEADLINE**: Branch I-W closure — χ(9) = χ(18) FORCED at n ≥ 27.

  The LAST obligation for kernel-pure `CompressionHyp 3 3`. Together with
  -'s Branch I-V completion, this discharges `lem_compress3_b3`.

  **Strategy**: by_contra. Trichotomy on χ(15) ∈ {χ(6), χ(9), χ(18)}.
  Each case derives False via a short cascade ending in a mono triple:
  - χ(15) = χ(18): cascade forces χ(3) = χ(9), χ(20) = χ(9), χ(21) = χ(9);
    mono (3, 20, 21).
  - χ(15) = χ(9): two χ(11) sub-cases.
    χ(11) = χ(18): forces χ(21) = χ(18); mono (21, 11, 18).
    χ(11) = χ(6): two χ(17) sub-cases.
      χ(17) = χ(6): forces χ(3) = χ(18), χ(20) = χ(18), χ(21) = χ(18); mono (3, 20, 21).
      χ(17) = χ(18): forces χ(3) = χ(18); mono (3, 17, 18).
  - χ(15) = χ(6): two χ(20) sub-cases.
    χ(20) = χ(9): forces χ(11) = χ(18), χ(17) = χ(9); mono (9, 17, 20).
    χ(20) = χ(18): forces χ(14) = χ(9), χ(11) = χ(18), χ(17) = χ(9); mono (9, 14, 17).
-/

set_option maxHeartbeats 3200000 in
/-- **Branch I-W, Case χ(15) = χ(18)**: derive False.

  Forces χ(10) = χ(20) = χ(9), χ(13) = χ(6), χ(21) ≠ χ(6). Then sub-cases on
  χ(21) ∈ {χ(9), χ(18)} each derive False via different mono triples.

  Sub-case χ(21) = χ(18): cascade forces χ(11) = χ(6) (= A), mono (6, 11, 13).
  Sub-case χ(21) = χ(9): cascade forces χ(14) = χ(18). Sub-sub-case on χ(11):
    χ(11) = χ(6): mono (6, 11, 13).
    χ(11) = χ(9): cascade forces χ(3) = χ(9), mono (3, 20, 21).
    χ(11) = χ(18): cascade forces χ(2) = χ(5) = χ(9), mono (9, 2, 5).
-/
theorem bAdicEquation_3_branch_I_W_chi_15_eq_chi_18_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_ne_18 : χ 9 ≠ χ 18) (h15_eq_18 : χ 15 = χ 18) :
    False := by
  -- Setup.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h9_ne_6 : χ 9 ≠ χ 6 := Ne.symm h6_ne_9
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h18_ne_6 : χ 18 ≠ χ 6 := fun h => h18_ne_24 (h.trans h24_eq_6.symm)
  have h6_ne_18 : χ 6 ≠ χ 18 := Ne.symm h18_ne_6
  have h18_ne_9 : χ 18 ≠ χ 9 := Ne.symm h9_ne_18
  -- χ values < 3.
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  -- Bundles.
  have h10_ne_6 := bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h2_ne_6 := bAdicEquation_3_chi_2_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  -- Self-loops.
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  have h15_ne_20 : χ 15 ≠ χ 20 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (3 * 5) ≠ χ (4 * 5); exact h
  have h10_ne_18 : χ 10 ≠ χ 18 := fun h => h10_ne_15 (h.trans h15_eq_18.symm)
  have h20_ne_18 : χ 20 ≠ χ 18 := fun h => h15_ne_20 (h15_eq_18.trans h.symm)
  -- χ(10), χ(20) = χ(9).
  have h10_eq_9 : χ 10 = χ 9 :=
    third_color_eq hχ10 hχ9 hχ6 hχ18 h6_ne_18 h10_ne_6 h10_ne_18 h9_ne_6 h9_ne_18
  have h20_eq_9 : χ 20 = χ 9 :=
    third_color_eq hχ20 hχ9 hχ6 hχ18 h6_ne_18 h20_ne_6 h20_ne_18 h9_ne_6 h9_ne_18
  -- χ(13) = χ(6) via (9, 10, 13) + (15, 13, 18).
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 10
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h10_eq_9.symm
    · show χ 10 = χ (10 + 3)
      rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_9, h13_eq_9]
  have h13_ne_18 : χ 13 ≠ χ 18 := by
    intro h13_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 5) = χ 13
      rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_18, ← h13_eq_18]
    · show χ 13 = χ (13 + 5)
      rw [show (13 + 5 : ℕ) = 18 by decide, h13_eq_18]
  have h13_eq_6 : χ 13 = χ 6 :=
    third_color_eq hχ13 hχ6 hχ9 hχ18 h9_ne_18 h13_ne_9 h13_ne_18 h6_ne_9 h6_ne_18
  -- χ(21) ≠ χ(6) via (21, 6, 13).
  have h21_ne_6 : χ 21 ≠ χ 6 := by
    intro h21_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 7) = χ 6
      rw [show (3 * 7 : ℕ) = 21 by decide]; exact h21_eq_6
    · show χ 6 = χ (6 + 7)
      rw [show (6 + 7 : ℕ) = 13 by decide]; exact h13_eq_6.symm
  -- Helper: mono (6, 11, 13) when chi(11) = chi(6).
  have mono_6_11_13 : χ 11 = χ 6 → False := by
    intro h11_eq_6
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 2) = χ 11
      rw [show (3 * 2 : ℕ) = 6 by decide, h11_eq_6]
    · show χ 11 = χ (11 + 2)
      rw [show (11 + 2 : ℕ) = 13 by decide, h11_eq_6, h13_eq_6]
  -- Case split on χ(21) ∈ {χ(9), χ(18)}.
  by_cases h21_eq_18 : χ 21 = χ 18
  · -- **Sub-case χ(21) = χ(18)**: derive cascade to mono (6, 11, 13).
    have h8_ne_18 : χ 8 ≠ χ 18 := by
      intro h8_eq_18
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 7) = χ 8
        rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_18, ← h8_eq_18]
      · show χ 8 = χ (8 + 7)
        rw [show (8 + 7 : ℕ) = 15 by decide, h15_eq_18, h8_eq_18]
    have h8_eq_9 : χ 8 = χ 9 :=
      third_color_eq hχ8 hχ9 hχ6 hχ18 h6_ne_18 h8_ne_6 h8_ne_18 h9_ne_6 h9_ne_18
    have h11_ne_9 : χ 11 ≠ χ 9 := by
      intro h11_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 3) = χ 8
        rw [show (3 * 3 : ℕ) = 9 by decide]; exact h8_eq_9.symm
      · show χ 8 = χ (8 + 3)
        rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_9, h11_eq_9]
    have h11_ne_18 : χ 11 ≠ χ 18 := by
      intro h11_eq_18
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 7) = χ 11
        rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_18, ← h11_eq_18]
      · show χ 11 = χ (11 + 7)
        rw [show (11 + 7 : ℕ) = 18 by decide, h11_eq_18]
    have h11_eq_6 : χ 11 = χ 6 :=
      third_color_eq hχ11 hχ6 hχ9 hχ18 h9_ne_18 h11_ne_9 h11_ne_18 h6_ne_9 h6_ne_18
    exact mono_6_11_13 h11_eq_6
  · -- **Sub-case χ(21) = χ(9)**: derive cascade ending in various mono.
    have h21_eq_9 : χ 21 = χ 9 :=
      third_color_eq hχ21 hχ9 hχ6 hχ18 h6_ne_18 h21_ne_6 h21_eq_18 h9_ne_6 h9_ne_18
    -- χ(14) = χ(18) via self-loop χ(14) ≠ χ(21) = χ(9), bundle χ(14) ≠ χ(6).
    have h14_ne_21 : χ 14 ≠ χ 21 := by
      have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
      show χ (2 * 7) ≠ χ (3 * 7); exact h
    have h14_ne_9 : χ 14 ≠ χ 9 := fun h => h14_ne_21 (h.trans h21_eq_9.symm)
    have h14_eq_18 : χ 14 = χ 18 :=
      third_color_eq hχ14 hχ18 hχ6 hχ9 h6_ne_9 h14_ne_6 h14_ne_9 h18_ne_6 h18_ne_9
    -- Sub-sub-case χ(11) ∈ {χ(6), χ(9), χ(18)}.
    by_cases h11_eq_6 : χ 11 = χ 6
    · exact mono_6_11_13 h11_eq_6
    · by_cases h11_eq_9 : χ 11 = χ 9
      · -- **χ(11) = χ(9)**: forces χ(8) = χ(18), χ(2) = χ(9), χ(27) = χ(6), χ(3) = χ(9).
        -- (9, 8, 11): forces χ(8) ≠ χ(9).
        have h8_ne_9 : χ 8 ≠ χ 9 := by
          intro h8_eq_9
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 3) = χ 8
            rw [show (3 * 3 : ℕ) = 9 by decide]; exact h8_eq_9.symm
          · show χ 8 = χ (8 + 3)
            rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_9, h11_eq_9]
        have h8_eq_18 : χ 8 = χ 18 :=
          third_color_eq hχ8 hχ18 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h18_ne_6 h18_ne_9
        -- (18, 2, 8): forces χ(2) ≠ χ(18).
        have h2_ne_18 : χ 2 ≠ χ 18 := by
          intro h2_eq_18
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 6) (y := 2) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 6) = χ 2
            rw [show (3 * 6 : ℕ) = 18 by decide, ← h2_eq_18]
          · show χ 2 = χ (2 + 6)
            rw [show (2 + 6 : ℕ) = 8 by decide, h8_eq_18, h2_eq_18]
        have h2_eq_9 : χ 2 = χ 9 :=
          third_color_eq hχ2 hχ9 hχ6 hχ18 h6_ne_18 h2_ne_6 h2_ne_18 h9_ne_6 h9_ne_18
        -- χ(27) ≠ χ(18) (self-loop), χ(27) ≠ χ(9) via (27, 2, 11): χ(2) = χ(11) = χ(9).
        have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
        have h27_ne_9 : χ 27 ≠ χ 9 := by
          intro h27_eq_9
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 9) (y := 2) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 9) = χ 2
            rw [show (3 * 9 : ℕ) = 27 by decide, h27_eq_9, ← h2_eq_9]
          · show χ 2 = χ (2 + 9)
            rw [show (2 + 9 : ℕ) = 11 by decide, h2_eq_9, ← h11_eq_9]
        have h27_eq_6 : χ 27 = χ 6 :=
          third_color_eq hχ27 hχ6 hχ9 hχ18 h9_ne_18 h27_ne_9 h27_ne_18 h6_ne_9 h6_ne_18
        -- (27, 3, 12): forces χ(3) ≠ χ(6).
        have h3_ne_6 : χ 3 ≠ χ 6 := by
          intro h3_eq_6
          exact bAdicEquation_3_chi_27_12_not_both_eq_chi_3 (n := n) χ h27 hNoMono
            (h27_eq_6.trans h3_eq_6.symm) (h6_eq_12.symm.trans h3_eq_6.symm)
        -- (3, 14, 15): forces χ(3) ≠ χ(18) (since χ(14) = χ(15) = χ(18)).
        have h3_ne_18 : χ 3 ≠ χ 18 := by
          intro h3_eq_18
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 1) (y := 14) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 1) = χ 14
            rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_18, ← h14_eq_18]
          · show χ 14 = χ (14 + 1)
            rw [show (14 + 1 : ℕ) = 15 by decide, h15_eq_18, h14_eq_18]
        have h3_eq_9 : χ 3 = χ 9 :=
          third_color_eq hχ3 hχ9 hχ6 hχ18 h6_ne_18 h3_ne_6 h3_ne_18 h9_ne_6 h9_ne_18
        -- MONO (3, 20, 21): χ(3) = χ(20) = χ(21) all = χ(9).
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 1) = χ 20
          rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h20_eq_9]
        · show χ 20 = χ (20 + 1)
          rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_9, h21_eq_9]
      · -- **χ(11) = χ(18)** (since χ(11) ≠ χ(6), ≠ χ(9), so = third color = χ(18)).
        have h11_eq_18 : χ 11 = χ 18 :=
          third_color_eq hχ11 hχ18 hχ6 hχ9 h6_ne_9 h11_eq_6 h11_eq_9 h18_ne_6 h18_ne_9
        -- (18, 5, 11): forces χ(5) ≠ χ(18).
        have h5_ne_18 : χ 5 ≠ χ 18 := by
          intro h5_eq_18
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 6) (y := 5) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 6) = χ 5
            rw [show (3 * 6 : ℕ) = 18 by decide, ← h5_eq_18]
          · show χ 5 = χ (5 + 6)
            rw [show (5 + 6 : ℕ) = 11 by decide, h11_eq_18, h5_eq_18]
        -- (24, 5, 13): forces χ(5) ≠ χ(6).
        have h5_ne_6 : χ 5 ≠ χ 6 := by
          intro h5_eq_6
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 8) = χ 5
            rw [show (3 * 8 : ℕ) = 24 by decide, h24_eq_6, ← h5_eq_6]
          · show χ 5 = χ (5 + 8)
            rw [show (5 + 8 : ℕ) = 13 by decide, h13_eq_6, h5_eq_6]
        have h5_eq_9 : χ 5 = χ 9 :=
          third_color_eq hχ5 hχ9 hχ6 hχ18 h6_ne_18 h5_ne_6 h5_ne_18 h9_ne_6 h9_ne_18
        -- (9, 5, 8): forces χ(8) ≠ χ(9).
        have h8_ne_9 : χ 8 ≠ χ 9 := by
          intro h8_eq_9
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 3) = χ 5
            rw [show (3 * 3 : ℕ) = 9 by decide]; exact h5_eq_9.symm
          · show χ 5 = χ (5 + 3)
            rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_9, h8_eq_9]
        have h8_eq_18 : χ 8 = χ 18 :=
          third_color_eq hχ8 hχ18 hχ6 hχ9 h6_ne_9 h8_ne_6 h8_ne_9 h18_ne_6 h18_ne_9
        -- (18, 2, 8): forces χ(2) ≠ χ(18).
        have h2_ne_18 : χ 2 ≠ χ 18 := by
          intro h2_eq_18
          have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
            (d := 6) (y := 2) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (3 * 6) = χ 2
            rw [show (3 * 6 : ℕ) = 18 by decide, ← h2_eq_18]
          · show χ 2 = χ (2 + 6)
            rw [show (2 + 6 : ℕ) = 8 by decide, h8_eq_18, h2_eq_18]
        have h2_eq_9 : χ 2 = χ 9 :=
          third_color_eq hχ2 hχ9 hχ6 hχ18 h6_ne_18 h2_ne_6 h2_ne_18 h9_ne_6 h9_ne_18
        -- MONO (9, 2, 5): χ(9) = χ(2) = χ(5).
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 2) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 3) = χ 2
          rw [show (3 * 3 : ℕ) = 9 by decide]; exact h2_eq_9.symm
        · show χ 2 = χ (2 + 3)
          rw [show (2 + 3 : ℕ) = 5 by decide, h2_eq_9, h5_eq_9]

/-! ### §83. Branch I-W Case χ(15) = χ(9) closure (2/3 of Branch I-W).

  Continues §82 (Case χ(15) = χ(18) closed). Case χ(15) = χ(6) remains.

  **Cascade**:
    χ(10) = χ(20) = χ(18) (self-loop + bundle)
    χ(14) = χ(16) = χ(9) (triples (18,14,20), (18,10,16))
    χ(11) ≠ χ(9) (triple (9,11,14))
    χ(21) ≠ χ(9) (self-loop (21,14,21))

  Case split χ(11):
  - χ(11) = χ(18): sub-cases on χ(21).
    - χ(21) = χ(18): mono (21,11,18).
    - χ(21) = χ(6): cascade χ(19) = χ(18), χ(17) impossible (third_color_eq + (17 ≠ 18) contradiction).
  - χ(11) = χ(6): forces χ(3) ≠ χ(6) via (3,11,12). Sub-cases on χ(3).
    - χ(3) = χ(9): mono (3,14,15) all = χ(9).
    - χ(3) = χ(18): cascade χ(17) = χ(6), χ(21) = χ(6). Mono (21,17,24) all = χ(6).
-/

set_option maxHeartbeats 6400000 in
theorem bAdicEquation_3_branch_I_W_chi_15_eq_chi_9_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_ne_18 : χ 9 ≠ χ 18) (h15_eq_9 : χ 15 = χ 9) :
    False := by
  -- Setup.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h9_ne_6 : χ 9 ≠ χ 6 := Ne.symm h6_ne_9
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h18_ne_6 : χ 18 ≠ χ 6 := fun h => h18_ne_24 (h.trans h24_eq_6.symm)
  have h6_ne_18 : χ 6 ≠ χ 18 := Ne.symm h18_ne_6
  have h18_ne_9 : χ 18 ≠ χ 9 := Ne.symm h9_ne_18
  -- χ values < 3.
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  -- Bundles.
  have h10_ne_6 := bAdicEquation_3_chi_10_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h16_ne_24 := bAdicEquation_3_chi_16_ne_chi_24 χ (by omega) hNoMono
  have h16_ne_6 : χ 16 ≠ χ 6 := fun h => h16_ne_24 (h.trans h24_eq_6.symm)
  -- Self-loops.
  have h10_ne_15 : χ 10 ≠ χ 15 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (2 * 5) ≠ χ (3 * 5); exact h
  have h15_ne_20 : χ 15 ≠ χ 20 := by
    have h := bAdicEquation_3_self_loop_xy_chain χ hNoMono (m := 5) (by omega) (by omega)
    show χ (3 * 5) ≠ χ (4 * 5); exact h
  have h10_ne_9 : χ 10 ≠ χ 9 := fun h => h10_ne_15 (h.trans h15_eq_9.symm)
  have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h15_ne_20 (h15_eq_9.trans h.symm)
  -- χ(10), χ(20) = χ(18). (third color of {6, 9})
  have h10_eq_18 : χ 10 = χ 18 :=
    third_color_eq hχ10 hχ18 hχ6 hχ9 h6_ne_9 h10_ne_6 h10_ne_9 h18_ne_6 h18_ne_9
  have h20_eq_18 : χ 20 = χ 18 :=
    third_color_eq hχ20 hχ18 hχ6 hχ9 h6_ne_9 h20_ne_6 h20_ne_9 h18_ne_6 h18_ne_9
  -- (18, 14, 20) forces χ(14) ≠ χ(18) (since χ(18) = χ(20) = χ(18)).
  have h14_ne_18 : χ 14 ≠ χ 18 := by
    intro h14_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 14
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h14_eq_18.symm
    · show χ 14 = χ (14 + 6)
      rw [show (14 + 6 : ℕ) = 20 by decide, h20_eq_18, h14_eq_18]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ6 hχ18 h6_ne_18 h14_ne_6 h14_ne_18 h9_ne_6 h9_ne_18
  -- (18, 10, 16) forces χ(16) ≠ χ(18) (since χ(10) = χ(18)).
  have h16_ne_18 : χ 16 ≠ χ 18 := by
    intro h16_eq_18
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 10
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h10_eq_18.symm
    · show χ 10 = χ (10 + 6)
      rw [show (10 + 6 : ℕ) = 16 by decide, h16_eq_18, h10_eq_18]
  have h16_eq_9 : χ 16 = χ 9 :=
    third_color_eq hχ16 hχ9 hχ6 hχ18 h6_ne_18 h16_ne_6 h16_ne_18 h9_ne_6 h9_ne_18
  -- (9, 11, 14) forces χ(11) ≠ χ(9) (since χ(9) = χ(14) = χ(9)).
  -- Triple (9, 11, 14): 9 + 33 = 42 = 3*14 ✓.
  have h11_ne_9 : χ 11 ≠ χ 9 := by
    intro h11_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 11
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h11_eq_9.symm
    · show χ 11 = χ (11 + 3)
      rw [show (11 + 3 : ℕ) = 14 by decide, h11_eq_9, h14_eq_9]
  -- Self-loop χ(14) ≠ χ(21).
  have h14_ne_21 : χ 14 ≠ χ 21 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 7) (by omega) (by omega)
    show χ (2 * 7) ≠ χ (3 * 7); exact h
  have h21_ne_9 : χ 21 ≠ χ 9 := fun h => h14_ne_21 (h14_eq_9.trans h.symm)
  -- Case split on χ(11).
  by_cases h11_eq_18 : χ 11 = χ 18
  · -- **Sub-case 1: χ(11) = χ(18)**
    by_cases h21_eq_18 : χ 21 = χ 18
    · -- Mono triple (21, 11, 18): 21 + 33 = 54 = 3*18 ✓. All = χ(18).
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 7) = χ 11
        rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_18, ← h11_eq_18]
      · show χ 11 = χ (11 + 7)
        rw [show (11 + 7 : ℕ) = 18 by decide, h11_eq_18]
    · -- **χ(21) ≠ χ(18)**: derive χ(21) = χ(6), then χ(17) impossible.
      have h21_eq_6 : χ 21 = χ 6 :=
        third_color_eq hχ21 hχ6 hχ9 hχ18 h9_ne_18 h21_ne_9 h21_eq_18 h6_ne_9 h6_ne_18
      -- (21, 12, 19): force χ(19) ≠ χ(6).
      have h19_ne_6 : χ 19 ≠ χ 6 := by
        intro h19_eq_6
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 7) (y := 12) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 7) = χ 12
          rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_6, h6_eq_12]
        · show χ 12 = χ (12 + 7)
          rw [show (12 + 7 : ℕ) = 19 by decide, h19_eq_6, h6_eq_12]
      -- (15, 14, 19): force χ(19) ≠ χ(9).
      have h19_ne_9 : χ 19 ≠ χ 9 := by
        intro h19_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 5) (y := 14) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 5) = χ 14
          rw [show (3 * 5 : ℕ) = 15 by decide, h15_eq_9, ← h14_eq_9]
        · show χ 14 = χ (14 + 5)
          rw [show (14 + 5 : ℕ) = 19 by decide, h14_eq_9, h19_eq_9]
      have h19_eq_18 : χ 19 = χ 18 :=
        third_color_eq hχ19 hχ18 hχ6 hχ9 h6_ne_9 h19_ne_6 h19_ne_9 h18_ne_6 h18_ne_9
      -- (12, 17, 21): force χ(17) ≠ χ(6). Triple: 12+51=63=3·21 ✓. χ(12)=A=χ(21)=A.
      have h17_ne_6 : χ 17 ≠ χ 6 := by
        intro h17_eq_6
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 4) (y := 17) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 4) = χ 17
          rw [show (3 * 4 : ℕ) = 12 by decide, ← h6_eq_12, h17_eq_6]
        · show χ 17 = χ (17 + 4)
          rw [show (17 + 4 : ℕ) = 21 by decide, h21_eq_6, h17_eq_6]
      -- (9, 14, 17): force χ(17) ≠ χ(9).
      have h17_ne_9 : χ 17 ≠ χ 9 := by
        intro h17_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 3) = χ 14
          rw [show (3 * 3 : ℕ) = 9 by decide]; exact h14_eq_9.symm
        · show χ 14 = χ (14 + 3)
          rw [show (14 + 3 : ℕ) = 17 by decide, h17_eq_9, h14_eq_9]
      -- (18, 11, 17): force χ(17) ≠ χ(18).
      have h17_ne_18 : χ 17 ≠ χ 18 := by
        intro h17_eq_18
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 6) (y := 11) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 6) = χ 11
          rw [show (3 * 6 : ℕ) = 18 by decide, ← h11_eq_18]
        · show χ 11 = χ (11 + 6)
          rw [show (11 + 6 : ℕ) = 17 by decide, h17_eq_18, h11_eq_18]
      -- Three exclusions on χ(17): use third_color_eq to derive χ(17) = χ(18), then contradiction.
      have h17_eq_18 : χ 17 = χ 18 :=
        third_color_eq hχ17 hχ18 hχ6 hχ9 h6_ne_9 h17_ne_6 h17_ne_9 h18_ne_6 h18_ne_9
      exact h17_ne_18 h17_eq_18
  · -- **Sub-case 2: χ(11) = χ(6)** (since χ(11) ≠ χ(9), ≠ χ(18)).
    have h11_eq_6 : χ 11 = χ 6 :=
      third_color_eq hχ11 hχ6 hχ9 hχ18 h9_ne_18 h11_ne_9 h11_eq_18 h6_ne_9 h6_ne_18
    -- (3, 11, 12) forces χ(3) ≠ χ(6).
    have h3_ne_6 : χ 3 ≠ χ 6 := by
      intro h3_eq_6
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 1) = χ 11
        rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_6, ← h11_eq_6]
      · show χ 11 = χ (11 + 1)
        rw [show (11 + 1 : ℕ) = 12 by decide, h11_eq_6, h6_eq_12]
    by_cases h3_eq_9 : χ 3 = χ 9
    · -- Mono triple (3, 14, 15): 3 + 42 = 45 = 3*15 ✓. All = χ(9).
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 1) (y := 14) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 1) = χ 14
        rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_9, ← h14_eq_9]
      · show χ 14 = χ (14 + 1)
        rw [show (14 + 1 : ℕ) = 15 by decide, h14_eq_9, h15_eq_9]
    · -- **χ(3) = χ(18)**: cascade to mono (21, 17, 24).
      have h3_eq_18 : χ 3 = χ 18 :=
        third_color_eq hχ3 hχ18 hχ6 hχ9 h6_ne_9 h3_ne_6 h3_eq_9 h18_ne_6 h18_ne_9
      -- (3, 17, 18) forces χ(17) ≠ χ(18) (since χ(3) = χ(18)).
      have h17_ne_18 : χ 17 ≠ χ 18 := by
        intro h17_eq_18
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 1) (y := 17) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 1) = χ 17
          rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_18, ← h17_eq_18]
        · show χ 17 = χ (17 + 1)
          rw [show (17 + 1 : ℕ) = 18 by decide, h17_eq_18]
      -- (9, 14, 17) forces χ(17) ≠ χ(9).
      have h17_ne_9 : χ 17 ≠ χ 9 := by
        intro h17_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 3) = χ 14
          rw [show (3 * 3 : ℕ) = 9 by decide]; exact h14_eq_9.symm
        · show χ 14 = χ (14 + 3)
          rw [show (14 + 3 : ℕ) = 17 by decide, h17_eq_9, h14_eq_9]
      -- χ(17) = χ(6).
      have h17_eq_6 : χ 17 = χ 6 :=
        third_color_eq hχ17 hχ6 hχ9 hχ18 h9_ne_18 h17_ne_9 h17_ne_18 h6_ne_9 h6_ne_18
      -- (3, 20, 21) forces χ(21) ≠ χ(18) (since χ(3) = χ(20) = χ(18)).
      have h21_ne_18 : χ 21 ≠ χ 18 := by
        intro h21_eq_18
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 1) = χ 20
          rw [show (3 * 1 : ℕ) = 3 by decide, h3_eq_18, ← h20_eq_18]
        · show χ 20 = χ (20 + 1)
          rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_18, h21_eq_18]
      -- χ(21) = χ(6).
      have h21_eq_6 : χ 21 = χ 6 :=
        third_color_eq hχ21 hχ6 hχ9 hχ18 h9_ne_18 h21_ne_9 h21_ne_18 h6_ne_9 h6_ne_18
      -- Mono triple (21, 17, 24): 21 + 51 = 72 = 3*24 ✓. All = χ(6).
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 17) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 7) = χ 17
        rw [show (3 * 7 : ℕ) = 21 by decide, h21_eq_6, ← h17_eq_6]
      · show χ 17 = χ (17 + 7)
        rw [show (17 + 7 : ℕ) = 24 by decide, h17_eq_6, ← h24_eq_6]

/-! ### §84. Branch I-W Case χ(15) = χ(6) closure (3/3 of Branch I-W).

  FINAL case for Branch I-W. After this, Branch I-W is fully closed.

  Notation: A = χ(6), B = χ(9), C = χ(18). Branch I-W: B ≠ C. This case: χ(15) = A.

  **Cascade**:
    §73 (chi_15_eq_A_forces_odd_ne_A) gives χ(1), χ(11), χ(17), χ(19) ≠ A.
    χ(27) ≠ A via (27, 6, 15) mono blocker.
    χ(27) ≠ C via self-loop (27 ≠ 18).
    third_color_eq ⟹ χ(27) = B.

  Case split χ(20) ∈ {B, C}:
  - χ(20) = B: (27,11,20) forces χ(11) ≠ B; χ(11) ≠ A; ⟹ χ(11) = C.
              (18,11,17) forces χ(17) ≠ C; χ(17) ≠ A; ⟹ χ(17) = B.
              Mono (9,17,20) all = B.
  - χ(20) = C: (18,14,20) forces χ(14) ≠ C; χ(14) ≠ A; ⟹ χ(14) = B.
              (9,11,14) forces χ(11) ≠ B; χ(11) ≠ A; ⟹ χ(11) = C.
              (18,11,17) forces χ(17) ≠ C; χ(17) ≠ A; ⟹ χ(17) = B.
              Mono (9,14,17) all = B.

  All triples verified:
  - (27, 6, 15): 27+18=45=3·15 ✓
  - (27, 11, 20): 27+33=60=3·20 ✓
  - (18, 11, 17): 18+33=51=3·17 ✓
  - (9, 17, 20): 9+51=60=3·20 ✓
  - (18, 14, 20): 18+42=60=3·20 ✓
  - (9, 11, 14): 9+33=42=3·14 ✓
  - (9, 14, 17): 9+42=51=3·17 ✓
-/

set_option maxHeartbeats 3200000 in
theorem bAdicEquation_3_branch_I_W_chi_15_eq_chi_6_contradiction
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h9_ne_18 : χ 9 ≠ χ 18) (h15_eq_6 : χ 15 = χ 6) :
    False := by
  -- Setup.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h9_ne_6 : χ 9 ≠ χ 6 := Ne.symm h6_ne_9
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h18_ne_6 : χ 18 ≠ χ 6 := fun h => h18_ne_24 (h.trans h24_eq_6.symm)
  have h6_ne_18 : χ 6 ≠ χ 18 := Ne.symm h18_ne_6
  have h18_ne_9 : χ 18 ≠ χ 9 := Ne.symm h9_ne_18
  -- χ values < 3.
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  -- Bundles.
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h20_ne_6 := bAdicEquation_3_chi_20_ne_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  -- §73 propagation: χ(15) = χ(6) forces χ(1), χ(11), χ(17), χ(19) ≠ χ(6).
  have ⟨_h1_ne_6, h11_ne_6, h17_ne_6, _h19_ne_6⟩ :=
    bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h15_eq_6
  -- Step 2: Force χ(27) = χ(9).
  -- χ(27) ≠ χ(6) via §72 (27, 6, 15) mono.
  have h27_ne_6 : χ 27 ≠ χ 6 := by
    intro h27_eq_6
    exact bAdicEquation_3_chi_27_15_not_both_eq_chi_6 (n := n) χ h27 hNoMono h27_eq_6 h15_eq_6
  -- χ(27) ≠ χ(18) via §72 self-loop.
  have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
  -- χ(27) = χ(9) via third_color_eq.
  have h27_eq_9 : χ 27 = χ 9 :=
    third_color_eq hχ27 hχ9 hχ6 hχ18 h6_ne_18 h27_ne_6 h27_ne_18 h9_ne_6 h9_ne_18
  -- Step 3: case split on χ(20).
  by_cases h20_eq_9 : χ 20 = χ 9
  · -- **Case 1: χ(20) = χ(9)** (= B).
    -- (27, 11, 20): 27+33=60=3·20 ✓. χ(27) = χ(9), χ(20) = χ(9). Force χ(11) ≠ χ(9).
    have h11_ne_9 : χ 11 ≠ χ 9 := by
      intro h11_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 9) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 9) = χ 11
        rw [show (3 * 9 : ℕ) = 27 by decide, h27_eq_9, h11_eq_9]
      · show χ 11 = χ (11 + 9)
        rw [show (11 + 9 : ℕ) = 20 by decide, h11_eq_9, h20_eq_9]
    -- χ(11) = χ(18) via third_color_eq.
    have h11_eq_18 : χ 11 = χ 18 :=
      third_color_eq hχ11 hχ18 hχ6 hχ9 h6_ne_9 h11_ne_6 h11_ne_9 h18_ne_6 h18_ne_9
    -- (18, 11, 17): 18+33=51=3·17 ✓. χ(18) = χ(11). Force χ(17) ≠ χ(18).
    have h17_ne_18 : χ 17 ≠ χ 18 := by
      intro h17_eq_18
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 6) = χ 11
        rw [show (3 * 6 : ℕ) = 18 by decide, ← h11_eq_18]
      · show χ 11 = χ (11 + 6)
        rw [show (11 + 6 : ℕ) = 17 by decide, h17_eq_18, h11_eq_18]
    -- χ(17) = χ(9) via third_color_eq.
    have h17_eq_9 : χ 17 = χ 9 :=
      third_color_eq hχ17 hχ9 hχ6 hχ18 h6_ne_18 h17_ne_6 h17_ne_18 h9_ne_6 h9_ne_18
    -- MONO (9, 17, 20): 9+51=60=3·20 ✓. All = χ(9).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 17
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h17_eq_9]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_9, h20_eq_9]
  · -- **Case 2: χ(20) ≠ χ(9)**. Combined with bundle χ(20) ≠ χ(6), gives χ(20) = χ(18).
    have h20_eq_18 : χ 20 = χ 18 :=
      third_color_eq hχ20 hχ18 hχ6 hχ9 h6_ne_9 h20_ne_6 h20_eq_9 h18_ne_6 h18_ne_9
    -- (18, 14, 20): 18+42=60=3·20 ✓. χ(18) = χ(20). Force χ(14) ≠ χ(18).
    have h14_ne_18 : χ 14 ≠ χ 18 := by
      intro h14_eq_18
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 14) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 6) = χ 14
        rw [show (3 * 6 : ℕ) = 18 by decide, ← h14_eq_18]
      · show χ 14 = χ (14 + 6)
        rw [show (14 + 6 : ℕ) = 20 by decide, h20_eq_18, h14_eq_18]
    -- χ(14) = χ(9) via third_color_eq.
    have h14_eq_9 : χ 14 = χ 9 :=
      third_color_eq hχ14 hχ9 hχ6 hχ18 h6_ne_18 h14_ne_6 h14_ne_18 h9_ne_6 h9_ne_18
    -- (9, 11, 14): 9+33=42=3·14 ✓. χ(9) = χ(14). Force χ(11) ≠ χ(9).
    have h11_ne_9 : χ 11 ≠ χ 9 := by
      intro h11_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 3) = χ 11
        rw [show (3 * 3 : ℕ) = 9 by decide, h11_eq_9]
      · show χ 11 = χ (11 + 3)
        rw [show (11 + 3 : ℕ) = 14 by decide, h11_eq_9, h14_eq_9]
    -- χ(11) = χ(18).
    have h11_eq_18 : χ 11 = χ 18 :=
      third_color_eq hχ11 hχ18 hχ6 hχ9 h6_ne_9 h11_ne_6 h11_ne_9 h18_ne_6 h18_ne_9
    -- (18, 11, 17). Force χ(17) ≠ χ(18).
    have h17_ne_18 : χ 17 ≠ χ 18 := by
      intro h17_eq_18
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 6) = χ 11
        rw [show (3 * 6 : ℕ) = 18 by decide, ← h11_eq_18]
      · show χ 11 = χ (11 + 6)
        rw [show (11 + 6 : ℕ) = 17 by decide, h17_eq_18, h11_eq_18]
    -- χ(17) = χ(9).
    have h17_eq_9 : χ 17 = χ 9 :=
      third_color_eq hχ17 hχ9 hχ6 hχ18 h6_ne_18 h17_ne_6 h17_ne_18 h9_ne_6 h9_ne_18
    -- MONO (9, 14, 17): 9+42=51=3·17 ✓. All = χ(9).
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 14
      rw [show (3 * 3 : ℕ) = 9 by decide, ← h14_eq_9]
    · show χ 14 = χ (14 + 3)
      rw [show (14 + 3 : ℕ) = 17 by decide, h14_eq_9, h17_eq_9]

/-! ### §85. **HEADLINE**: Branch I-W master closure — χ(9) = χ(18) FORCED.

  Trichotomy assembly of (§82) + (§83) + (§84).

  After this theorem:
  - Branch I-W → False (no mono-free 3-coloring with χ(9) ≠ χ(18) exists).
  - Combined with Branch I-V cascade (-240), multiples-of-3 ⊆ {χ(6), χ(9)}
    in every mono-free 3-coloring of [1, n] (n ≥ 27) for bAdicEquation 3.
  - This is exactly `CompressionHyp 3 3` content.
  - `lem_compress3_b3` becomes derivable; the axiom can be removed.

  Proof: by contradiction. If χ(9) ≠ χ(18), then trichotomy on χ(15) ∈ {χ(6), χ(9), χ(18)}
  (via `third_color_eq` for the third branch), each leading to one of §82-§84.
-/

theorem bAdicEquation_3_chi_9_eq_chi_18_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 9 = χ 18 := by
  by_contra h9_ne_18
  -- Setup distinctness on {χ(6), χ(9), χ(18)}.
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  have h18_ne_24 := bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono
  have h18_ne_6 : χ 18 ≠ χ 6 := fun h => h18_ne_24 (h.trans h24_eq_6.symm)
  have h18_ne_9 : χ 18 ≠ χ 9 := Ne.symm h9_ne_18
  -- χ values < 3.
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  -- Trichotomy on χ(15) ∈ {χ(6), χ(9), χ(18)}.
  by_cases h15_eq_6 : χ 15 = χ 6
  · exact bAdicEquation_3_branch_I_W_chi_15_eq_chi_6_contradiction
      (n := n) χ h27 hχk hNoMono h9_ne_18 h15_eq_6
  · by_cases h15_eq_9 : χ 15 = χ 9
    · exact bAdicEquation_3_branch_I_W_chi_15_eq_chi_9_contradiction
        (n := n) χ h27 hχk hNoMono h9_ne_18 h15_eq_9
    · -- χ(15) ≠ χ(6) (from h15_eq_6), χ(15) ≠ χ(9) (from h15_eq_9).
      -- third_color_eq: both χ(15), χ(18) avoid {χ(6), χ(9)} ⟹ χ(15) = χ(18).
      have h15_eq_18 : χ 15 = χ 18 :=
        third_color_eq hχ15 hχ18 hχ6 hχ9 h6_ne_9 h15_eq_6 h15_eq_9 h18_ne_6 h18_ne_9
      exact bAdicEquation_3_branch_I_W_chi_15_eq_chi_18_contradiction
        (n := n) χ h27 hχk hNoMono h9_ne_18 h15_eq_18

/-! ### §86. **UPPER BOUND**: No mono-free 3-coloring at n ≥ 27 for bAdicEquation 3.

  The kernel-pure derivation of R_3(3) ≤ 27.

  After (χ(9) = χ(18) forced), Branch I-V cascade (/) gives
  χ(3) = χ(15) = χ(6) in any mono-free coloring. Together with §72 χ(27)
  self-loop, this forces χ(27) ∉ {χ(6), χ(9)} (so χ(27) = "third color"),
  then a sub-case cascade on χ(17) ends in mono triple either way:
  - χ(17) = χ(9): cascade forces χ(2)=χ(9), χ(5)=χ(11)=χ(14)=χ(27); mono (27,5,14).
  - χ(17) = χ(27): cascade forces χ(8)=χ(9)=χ(11); mono (9,8,11).
  - χ(17) = χ(6): excluded by §73 (chi_15=chi_6 propagation).

  Plus the case χ(27) = χ(6) directly gives mono (27,6,15).

  This collapses CompressionHyp 3 3 (at n=27 = b^3) to VACUOUS — the only
  remaining work for R_3(3) ≤ 27 kernel-pure is wiring this into the
  existing cascade_step (next round).
-/

set_option maxHeartbeats 3200000 in
/-- **MAIN: there is no mono-free 3-coloring of [1, n] (n ≥ 27) for bAdicEquation 3**.

  Equivalent to R_3(3) ≤ 27 directly. Kernel-pure.
-/
theorem bAdicEquation_3_no_mono_free_at_27
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    False := by
  -- Setup from +.
  have h6_eq_12 := bAdicEquation_3_chi_6_eq_chi_12_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h24_eq_6 := bAdicEquation_3_chi_24_eq_chi_6_in_monoFree (n := n) χ (by omega) hχk hNoMono
  have h9_eq_18 := bAdicEquation_3_chi_9_eq_chi_18_in_monoFree (n := n) χ h27 hχk hNoMono
  have h15_eq_6 := bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18
    (n := n) χ (by omega) hχk hNoMono h9_eq_18
  have h3_eq_6 := bAdicEquation_3_chi_3_eq_chi_6_when_chi_9_eq_chi_18
    (n := n) χ h27 hχk hNoMono h9_eq_18
  have h6_ne_9 := bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  -- §73 propagation: χ(15) = χ(6) ⟹ χ(1), χ(11), χ(17), χ(19) ≠ χ(6).
  have ⟨_h1_ne_6, h11_ne_6, h17_ne_6, _h19_ne_6⟩ :=
    bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h15_eq_6
  -- §74 propagation: χ(3) = χ(6) ⟹ χ(5), χ(11), χ(23) ≠ χ(6).
  have ⟨h5_ne_6, _h11_ne_6_alt, _h23_ne_6⟩ :=
    bAdicEquation_3_chi_3_eq_A_forces_odd_ne_A (n := n) χ (by omega) hχk hNoMono h3_eq_6
  -- Bundles.
  have h2_ne_6 := bAdicEquation_3_chi_2_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h14_ne_6 := bAdicEquation_3_chi_14_ne_chi_6_when_chi_6_eq_12 χ (by omega) hNoMono h6_eq_12
  have h8_ne_12 : χ 8 ≠ χ 12 := by
    have h := bAdicEquation_3_self_loop_chain χ hNoMono (m := 4) (by omega) (by omega)
    show χ (2 * 4) ≠ χ (3 * 4); exact h
  have h8_ne_6 : χ 8 ≠ χ 6 := fun h => h8_ne_12 (h.trans h6_eq_12)
  -- χ(27) ≠ χ(18) self-loop, ≠ χ(9) via.
  have h27_ne_18 := bAdicEquation_3_chi_27_ne_chi_18_in_monoFree (n := n) χ h27 hNoMono
  have h27_ne_9 : χ 27 ≠ χ 9 := fun h => h27_ne_18 (h.trans h9_eq_18)
  -- χ values < 3.
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  -- Case split on χ(27).
  by_cases h27_eq_6 : χ 27 = χ 6
  · -- Direct mono (27, 6, 15) since χ(15) = χ(6).
    exact bAdicEquation_3_chi_27_15_not_both_eq_chi_6 (n := n) χ h27 hNoMono h27_eq_6 h15_eq_6
  · -- χ(27) ≠ χ(6) and ≠ χ(9). χ(27) = third color.
    -- Case split on χ(17) ∈ {χ(9), χ(27)} (since χ(17) ≠ χ(6) by §73).
    by_cases h17_eq_9 : χ 17 = χ 9
    · -- **Case 1**: χ(17) = χ(9). Cascade ends at MONO (27, 5, 14).
      -- (9, 14, 17): χ(9) = χ(17), χ(14). Force χ(14) ≠ χ(9).
      have h14_ne_9 : χ 14 ≠ χ 9 := by
        intro h14_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 3) = χ 14
          rw [show (3 * 3 : ℕ) = 9 by decide]; exact h14_eq_9.symm
        · show χ 14 = χ (14 + 3)
          rw [show (14 + 3 : ℕ) = 17 by decide, h17_eq_9, h14_eq_9]
      -- χ(14) = χ(27) (third color).
      have h14_eq_27 : χ 14 = χ 27 :=
        third_color_eq hχ14 hχ27 hχ6 hχ9 h6_ne_9 h14_ne_6 h14_ne_9 h27_eq_6 h27_ne_9
      -- (18, 11, 17): χ(18) = χ(9), χ(17) = χ(9), χ(11). Force χ(11) ≠ χ(9).
      have h11_ne_9 : χ 11 ≠ χ 9 := by
        intro h11_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 6) (y := 11) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 6) = χ 11
          rw [show (3 * 6 : ℕ) = 18 by decide, ← h9_eq_18, h11_eq_9]
        · show χ 11 = χ (11 + 6)
          rw [show (11 + 6 : ℕ) = 17 by decide, h17_eq_9, h11_eq_9]
      have h11_eq_27 : χ 11 = χ 27 :=
        third_color_eq hχ11 hχ27 hχ6 hχ9 h6_ne_9 h11_ne_6 h11_ne_9 h27_eq_6 h27_ne_9
      -- (27, 2, 11): χ(27), χ(2), χ(11) = χ(27). Force χ(2) ≠ χ(27).
      have h2_ne_27 : χ 2 ≠ χ 27 := by
        intro h2_eq_27
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 9) (y := 2) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 9) = χ 2
          rw [show (3 * 9 : ℕ) = 27 by decide]; exact h2_eq_27.symm
        · show χ 2 = χ (2 + 9)
          rw [show (2 + 9 : ℕ) = 11 by decide, h2_eq_27, h11_eq_27]
      have h2_eq_9 : χ 2 = χ 9 :=
        third_color_eq hχ2 hχ9 hχ6 hχ27 (Ne.symm h27_eq_6) h2_ne_6 h2_ne_27
          (Ne.symm h6_ne_9) (Ne.symm h27_ne_9)
      -- (9, 2, 5): χ(9), χ(2) = χ(9), χ(5). Force χ(5) ≠ χ(9).
      have h5_ne_9 : χ 5 ≠ χ 9 := by
        intro h5_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 2) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 3) = χ 2
          rw [show (3 * 3 : ℕ) = 9 by decide]; exact h2_eq_9.symm
        · show χ 2 = χ (2 + 3)
          rw [show (2 + 3 : ℕ) = 5 by decide, h2_eq_9, h5_eq_9]
      -- χ(5) = χ(27).
      have h5_eq_27 : χ 5 = χ 27 :=
        third_color_eq hχ5 hχ27 hχ6 hχ9 h6_ne_9 h5_ne_6 h5_ne_9 h27_eq_6 h27_ne_9
      -- MONO (27, 5, 14): 27 + 15 = 42 = 3·14 ✓.
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 9) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 9) = χ 5
        rw [show (3 * 9 : ℕ) = 27 by decide, ← h5_eq_27]
      · show χ 5 = χ (5 + 9)
        rw [show (5 + 9 : ℕ) = 14 by decide, h5_eq_27, ← h14_eq_27]
    · -- **Case 2**: χ(17) ≠ χ(9), ≠ χ(6) (§73). So χ(17) = χ(27) (third color).
      have h17_eq_27 : χ 17 = χ 27 :=
        third_color_eq hχ17 hχ27 hχ6 hχ9 h6_ne_9 h17_ne_6 h17_eq_9 h27_eq_6 h27_ne_9
      -- (27, 8, 17): χ(27), χ(8), χ(17) = χ(27). Force χ(8) ≠ χ(27).
      have h8_ne_27 : χ 8 ≠ χ 27 := by
        intro h8_eq_27
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 9) (y := 8) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 9) = χ 8
          rw [show (3 * 9 : ℕ) = 27 by decide]; exact h8_eq_27.symm
        · show χ 8 = χ (8 + 9)
          rw [show (8 + 9 : ℕ) = 17 by decide, h17_eq_27, h8_eq_27]
      have h8_eq_9 : χ 8 = χ 9 :=
        third_color_eq hχ8 hχ9 hχ6 hχ27 (Ne.symm h27_eq_6) h8_ne_6 h8_ne_27
          (Ne.symm h6_ne_9) (Ne.symm h27_ne_9)
      -- (18, 2, 8): χ(18) = χ(9), χ(2), χ(8) = χ(9). Force χ(2) ≠ χ(9).
      have h2_ne_9 : χ 2 ≠ χ 9 := by
        intro h2_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 6) (y := 2) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 6) = χ 2
          rw [show (3 * 6 : ℕ) = 18 by decide, ← h9_eq_18, h2_eq_9]
        · show χ 2 = χ (2 + 6)
          rw [show (2 + 6 : ℕ) = 8 by decide, h8_eq_9, h2_eq_9]
      have h2_eq_27 : χ 2 = χ 27 :=
        third_color_eq hχ2 hχ27 hχ6 hχ9 h6_ne_9 h2_ne_6 h2_ne_9 h27_eq_6 h27_ne_9
      -- (27, 2, 11): χ(27), χ(2) = χ(27), χ(11). Force χ(11) ≠ χ(27).
      have h11_ne_27 : χ 11 ≠ χ 27 := by
        intro h11_eq_27
        have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
          (d := 9) (y := 2) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 9) = χ 2
          rw [show (3 * 9 : ℕ) = 27 by decide, ← h2_eq_27]
        · show χ 2 = χ (2 + 9)
          rw [show (2 + 9 : ℕ) = 11 by decide, h2_eq_27, h11_eq_27]
      have h11_eq_9 : χ 11 = χ 9 :=
        third_color_eq hχ11 hχ9 hχ6 hχ27 (Ne.symm h27_eq_6) h11_ne_6 h11_ne_27
          (Ne.symm h6_ne_9) (Ne.symm h27_ne_9)
      -- MONO (9, 8, 11): 9 + 24 = 33 = 3·11 ✓. All = χ(9).
      have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (3 * 3) = χ 8
        rw [show (3 * 3 : ℕ) = 9 by decide, ← h8_eq_9]
      · show χ 8 = χ (8 + 3)
        rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_9, h11_eq_9]

/-! ### §87. Vacuous compression at n = 27 (= b^3 for b = 3, k = 3).

  Form matches `cascade_step`'s `hCompress` hypothesis. Used to derive a
  kernel-pure `thm_k3b3` (replacing the project's `lem_compress3_general`
  axiom for the b = 3 case).
-/

theorem bAdicEquation_3_compression_at_27_kernel_pure
    (χ : ℕ → ℕ) (hχk : IsKColoring 27 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) 27 χ) :
    ∃ c₀, c₀ < 3 ∧ ∀ d, 1 ≤ d → d ≤ 9 → χ (3 * d) ≠ c₀ := by
  exfalso
  exact bAdicEquation_3_no_mono_free_at_27 χ (le_refl 27) hχk hNoMono

/-! ### §88. **(b = 4, k = 3) backbone self-loop exclusions** ().

  First concrete migration of the schema to b = 4. Establishes the
  4 backbone self-loop exclusions at n ≥ 64 (= 4^3) using the existing
  parameterized `bAdicEquation_self_loop_chi_diff` (Type C, general b).

  Self-loop pattern: χ((b-1)·m) ≠ χ(b·m) for any m with b·m ≤ n.
  For b = 4, m ∈ {4, 8, 12, 16}: χ(3m) ≠ χ(4m), i.e., χ(12) ≠ χ(16),
  χ(24) ≠ χ(32), χ(36) ≠ χ(48), χ(48) ≠ χ(64).

  These are the analogues of the b = 3 self-loops at m = 4, 8, 12 etc.
  (which gave χ(8) ≠ χ(12), χ(16) ≠ χ(24), etc., used in the Branch I-V
  cascade backbone).

  All four theorems are instantiations of `bAdicEquation_self_loop_chi_diff`
  at b = 4. Each is verified by computing the explicit triple at b = 4:
  (4·m, 3·m, 4·m) means x = 4m, y = 3m, z = 4m, equation x + 4y = 4z:
    4m + 12m = 16m = 4·(4m) ✓.
  So self-loop forces χ(3m) ≠ χ(4m) when mono-free.
-/

/-- **χ(12) ≠ χ(16)** in mono-free 3-coloring of [1, n] (n ≥ 16) for `bAdicEquation 4`.
  Self-loop at b = 4, m = 4. -/
theorem bAdicEquation_4_chi_12_ne_chi_16_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    χ 12 ≠ χ 16 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
    (m := 4) (by omega) (by omega)
  -- h : χ ((4 - 1) * 4) ≠ χ (4 * 4), i.e., χ 12 ≠ χ 16.
  show χ ((4 - 1) * 4) ≠ χ (4 * 4)
  exact h

/-- **χ(24) ≠ χ(32)** in mono-free 3-coloring of [1, n] (n ≥ 32) for `bAdicEquation 4`.
  Self-loop at b = 4, m = 8. -/
theorem bAdicEquation_4_chi_24_ne_chi_32_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    χ 24 ≠ χ 32 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
    (m := 8) (by omega) (by omega)
  show χ ((4 - 1) * 8) ≠ χ (4 * 8)
  exact h

/-- **χ(36) ≠ χ(48)** in mono-free 3-coloring of [1, n] (n ≥ 48) for `bAdicEquation 4`.
  Self-loop at b = 4, m = 12. -/
theorem bAdicEquation_4_chi_36_ne_chi_48_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    χ 36 ≠ χ 48 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
    (m := 12) (by omega) (by omega)
  show χ ((4 - 1) * 12) ≠ χ (4 * 12)
  exact h

/-- **χ(48) ≠ χ(64)** in mono-free 3-coloring of [1, n] (n ≥ 64) for `bAdicEquation 4`.
  Self-loop at b = 4, m = 16. -/
theorem bAdicEquation_4_chi_48_ne_chi_64_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    χ 48 ≠ χ 64 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
    (m := 16) (by omega) (by omega)
  show χ ((4 - 1) * 16) ≠ χ (4 * 16)
  exact h

/-! ### §89. (b = 4, k = 3) structural exploration.

  **Multiples-of-4 layer at n = 64**: {4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48,
  52, 56, 60, 64} — 16 positions.

  **Self-loop backbone (b - 1, b) inequalities**: ALL m ∈ [1, 16] give
  χ(3m) ≠ χ(4m). The 4 specific theorems in §88 cover m ∈ {4, 8, 12, 16},
  which are the LAYER inequalities (both 3m and 4m are multiples of 4).

  **Other self-loop family** (b, b+1): χ(4m) ≠ χ(5m). For m ∈ {1,..., 12}:
  χ(4) ≠ χ(5), χ(8) ≠ χ(10), χ(12) ≠ χ(15),..., χ(48) ≠ χ(60). Connects
  multiples-of-4 to non-multiples.

  **Candidate first master forcing theorem** (analogue search):

  For b = 3, the first master forcing was χ(6) = χ(12) — derived from:
  - χ(6) ≠ χ(9) (self-loop m = 3 for b = 3).
  - χ(9) ≠ χ(12) (xy-self-loop m = 3 for b = 3).
  - "no all distinct" on (χ(6), χ(9), χ(12)): heavy case analysis.

  For b = 4, the natural analogue positions are (χ(8), χ(12), χ(16)):
  - χ(12) ≠ χ(16) (self-loop m = 4, §88 above).
  - χ(8) ≠ χ(12)? NOT given directly by self-loops.
  - χ(8) ≠ χ(16)? NOT given directly.

  The b = 3 analogue chain `χ(6) ≠ χ(9) ∧ χ(9) ≠ χ(12)` came from self-loop
  AT DIFFERENT m's (m = 3 for one, m = 4 for the other). For b = 4:
  - m = 2: χ(6) ≠ χ(8).
  - m = 3: χ(9) ≠ χ(12).
  - m = 4: χ(12) ≠ χ(16).

  So neighbouring inequalities at m, m + 1 give pairs like (χ(3m), χ(4m))
  and (χ(3(m+1)), χ(4(m+1))) — but they involve 4 different positions, not
  3. The b = 3 analogue worked because b - 1 = 2 and b = 3 form a step-1
  ratio: (b-1)·(m+1) = b·m gives the chain.

  Check b = 4 step ratio: (b-1)·(m+1) = 3(m+1) vs b·m = 4m. Equal iff
  3m + 3 = 4m iff m = 3. So at m = 3: 3·4 = 12 = 4·3. So χ(9) ≠ χ(12)
  (m=3 self-loop) and χ(12) ≠ χ(16) (m=4 self-loop) chain at position 12.

  **This gives the b = 4 analogue**: (χ(9), χ(12), χ(16)) — analogous to
  b = 3's (χ(6), χ(9), χ(12)).

  - χ(9) ≠ χ(12) (m = 3 self-loop, §88-style).
  - χ(12) ≠ χ(16) (m = 4 self-loop, §88).
  - For "no all distinct on (χ(9), χ(12), χ(16))" we need: extra constraint
    forcing one of these equal to another. NOT from self-loops alone.

  This matches the b = 3 pattern. The b = 3 proof for
  `bAdicEquation_3_no_chi_6_9_12_all_distinct` was a multi-round case analysis
  using triples (12, y, y+4), (9, y, y+3), (6, y, y+2). For b = 4, analogous
  would use (16, y, y+4), (12, y, y+3), (8, y, y+2) — but constraints differ.

  **Next round's concrete target** ():

  `bAdicEquation_4_chi_12_ne_chi_9_in_monoFree`
    — Self-loop at b = 4, m = 3. ALREADY DERIVABLE from
    `bAdicEquation_self_loop_chi_diff` instance. Trivial.

  After that, the first NON-TRIVIAL b=4 result would be the analogue of
  `bAdicEquation_3_no_chi_6_9_12_all_distinct` for the triple
  (χ(9), χ(12), χ(16)). This requires heavy case analysis similar in
  scope to b = 3 R+213.
-/

/-- **χ(9) ≠ χ(12)** in mono-free 3-coloring of [1, n] (n ≥ 12) for `bAdicEquation 4`.
  Self-loop at b = 4, m = 3. Identified in §89 as the third position in the
  candidate first master forcing triple (χ(9), χ(12), χ(16)).
-/
theorem bAdicEquation_4_chi_9_ne_chi_12_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    χ 9 ≠ χ 12 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
    (m := 3) (by omega) (by omega)
  show χ ((4 - 1) * 3) ≠ χ (4 * 3)
  exact h

/-! ### §90. (b = 4, k = 3) candidate master forcing — pressure test ().

  **Target**: `bAdicEquation_4_no_chi_9_12_16_all_distinct` — analogue of b=3's
  R+213 `bAdicEquation_3_no_chi_6_9_12_all_distinct`.

  **Setting**: A := χ(9), B := χ(12), C := χ(16) all pairwise distinct,
  mono-free 3-coloring at n ≥ 16 for `bAdicEquation 4`.

  **Structural finding**: full closure at n = 16 is NOT clean. Triples within
  [1, 16] that could give mono via 3 same-color positions exist, but the
  cascade requires sub-case analysis of comparable scope to b=3 R+213
  (~200-400 lines, multi-round work).

  **Partial closure (this round)**: subcase where additionally χ(8) = χ(9)
  AND χ(4) = χ(12). This subcase closes via a CLEAN cascade ending in mono
  triple (16, 7, 11), demonstrating that the (16, 7, 11) MONO is the right
  TERMINAL TRIPLE for the b=4 analogue of b=3's (6, 11, 13)-style closers.

  All Rado triples used verified at b=4 (x + 4y = 4z):
  - (12, 4, 7): 12+16=28=4·7 ✓
  - (4, 11, 12): 4+44=48=4·12 ✓
  - (8, 7, 9): 8+28=36=4·9 ✓
  - (8, 9, 11): 8+36=44=4·11 ✓
  - (16, 7, 11): 16+28=44=4·11 ✓ (MONO closer)

  **Negative finding for full closure**: the all-distinct hypothesis alone
  (no chi(4), chi(8) constraints) does NOT force chi(7), chi(11) to be the
  third color. They could be any of {A, B, C} a priori. The subcase pattern
  (chi(4) ∈ {A, B, C}, chi(8) ∈ {A, B, C}) generates 9 sub-cases, each
  requiring its own cascade. Full closure is multi-round work.

  **Next-round target**: continue the case enumeration. Specifically,
  bAdicEquation_4_no_chi_9_12_16_all_distinct_case_chi_8_eq_chi_9 — the
  full chi(8) = chi(9) case across all chi(4) values.
-/

/-- **TRIVIAL: chi(8) = chi(9) ∧ chi(4) = chi(9) → mono via (4, 8, 9)**.
  Direct application of the Rado triple (4, 8, 9): x+4y=4z → 4+32=36=4·9 ✓.
  All three positions have color = χ(9), so mono. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h8_eq_9 : χ 8 = χ 9)
    (h4_eq_9 : χ 4 = χ 9) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 1) = χ 8
    rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, ← h8_eq_9]
  · show χ 8 = χ (8 + 1)
    rw [show (8 + 1 : ℕ) = 9 by decide, h8_eq_9]

/-! ### §91. **NEGATIVE FINDING**: chi(4) = chi(16) subcase does NOT close at n = 16.

  **Pressure-test result ()**: the candidate master forcing theorem
  `bAdicEquation_4_no_chi_9_12_16_all_distinct_case_chi_8_eq_chi_9` is
  **FALSE at n = 16**.

  **Explicit witness coloring** (verified by enumeration of all 54 Rado triples
  in [1, 16]): χ : ℕ → ℕ defined by
  ```
    1 ↦ 1 (B) 9 ↦ 0 (A)
    2 ↦ 2 (C) 10 ↦ 1 (B)
    3 ↦ 0 (A) 11 ↦ 1 (B)
    4 ↦ 2 (C) 12 ↦ 1 (B)
    5 ↦ 1 (B) 13 ↦ 2 (C)
    6 ↦ 1 (B) 14 ↦ 0 (A)
    7 ↦ 2 (C) 15 ↦ 0 (A)
    8 ↦ 0 (A) 16 ↦ 2 (C)
  ```
  Satisfies: χ(9) = 0, χ(12) = 1, χ(16) = 2 (all distinct), χ(8) = χ(9) = 0,
  χ(4) = χ(16) = 2, AND mono-free for `bAdicEquation 4` on [1, 16] (all 54
  triples manually verified).

  **Structural cascade analysis** (under χ(8)=χ(9)=A, χ(4)=χ(16)=C):
  Forced equalities derivable from Rado triples within [1, 16]:
  - χ(15) = A (from (4, 15, 16) + self-loop (12, 12, 15)).
  - χ(13) ≠ A (from (8, 13, 15)).
  - χ(11) ≠ A (from (8, 9, 11)).
  - χ(7) ≠ A (from (8, 7, 9)).
  - χ(6) ≠ A (from self-loop (8, 6, 8)).
  - χ(10) ≠ A (from self-loop (8, 8, 10)).

  These leave χ(2), χ(3), χ(5), χ(6), χ(7), χ(10), χ(11), χ(13), χ(14) all
  with at least 2 color choices each. The all-distinct + χ(8)=χ(9) + χ(4)=χ(16)
  hypothesis does NOT force enough additional constraints to close at n = 16.

  **What this means structurally**:
  - At n = 16, the (b=4, k=3) all-distinct master forcing FAILS even
    restricted to χ(8) = χ(9). The "first master forcing" candidate identified
    in §89 needs LARGER n to close.
  - For b=3 analogue, n ≥ 26 was required (= 3^3 - 1). For b=4, likely n ≥ 63
    (= 4^3 - 1) or n = 64 (= 4^3).
  - Alternative: a different "first master forcing" structure for b=4 might
    close at smaller n. Candidates: (χ(8), χ(12), χ(16)), (χ(16), χ(32), χ(48)),
    or compression-style "multiples-of-4 use ≤ 2 colors" theorem.

  ** target**: lift the theorem to n ≥ 63 OR adopt a different master
  forcing candidate. The chi(8) = chi(9) case at n = 16 is OPEN (not False).

  **Closure status — chi(8) = chi(9) branch**:
  - chi(4) = chi(9): CLOSED (trivial mono (4, 8, 9), this round).
  - chi(4) = chi(12): CLOSED (, mono (16, 7, 11)).
  - chi(4) = chi(16): **OPEN at n = 16** (admits mono-free witness).
-/

/-- **PARTIAL: b=4 no all-distinct subcase** (chi(8) = chi(9) ∧ chi(4) = chi(12)).
  In any mono-free 3-coloring of [1, n] (n ≥ 16) for `bAdicEquation 4`, if
  χ(9), χ(12), χ(16) are pairwise distinct AND χ(8) = χ(9) AND χ(4) = χ(12),
  then False.

  Cascade: forces χ(7), χ(11) ≠ χ(9) and ≠ χ(12); third_color_eq ⟹
  χ(7) = χ(11) = χ(16). Mono (16, 7, 11).
-/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_12
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_9 : χ 8 = χ 9)
    (h4_eq_12 : χ 4 = χ 12) :
    False := by
  -- (12, 4, 7) forces χ(7) ≠ χ(12).
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 4
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h4_eq_12.symm
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h4_eq_12, h7_eq_12]
  -- (4, 11, 12) forces χ(11) ≠ χ(12).
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 11
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h11_eq_12]
    · show χ 11 = χ (11 + 1)
      rw [show (11 + 1 : ℕ) = 12 by decide, h11_eq_12]
  -- (8, 7, 9) forces χ(7) ≠ χ(9).
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 7
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_9, h7_eq_9]
    · show χ 7 = χ (7 + 2)
      rw [show (7 + 2 : ℕ) = 9 by decide, h7_eq_9]
  -- (8, 9, 11) forces χ(11) ≠ χ(9).
  have h11_ne_9 : χ 11 ≠ χ 9 := by
    intro h11_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 9
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_9
    · show χ 9 = χ (9 + 2)
      rw [show (9 + 2 : ℕ) = 11 by decide, h11_eq_9]
  -- χ values < 3.
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- third_color_eq: χ(7) ≠ χ(9), χ(7) ≠ χ(12) ⟹ χ(7) = χ(16) (the third color).
  have h7_eq_16 : χ 7 = χ 16 :=
    third_color_eq hχ7 hχ16 hχ9 hχ12 h9_ne_12 h7_ne_9 h7_ne_12
      (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- Similarly χ(11) = χ(16).
  have h11_eq_16 : χ 11 = χ 16 :=
    third_color_eq hχ11 hχ16 hχ9 hχ12 h9_ne_12 h11_ne_9 h11_ne_12
      (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- MONO (16, 7, 11): 16 + 28 = 44 = 4·11. All three = χ(16).
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 7
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h7_eq_16.symm
  · show χ 7 = χ (7 + 4)
    rw [show (7 + 4 : ℕ) = 11 by decide, h7_eq_16, h11_eq_16]

/-! ### §92. — witness branch THRESHOLD COLLAPSE at n ≥ 20.

  **Headline finding ()**: the witness branch (χ(8) = χ(9) ∧ χ(4) = χ(16),
  with χ(9), χ(12), χ(16) pairwise distinct) DIES at n ≥ 20, not n ≥ 64 as
   §91 conservatively suggested.

  Specifically, the §91 explicit witness coloring on [1, 16] CANNOT be extended
  to any coloring of [1, 20]: the positions χ(17) and χ(20) are forced to
  values that contradict hNoMono via Rado triples internal to [1, 20].

  **Implication for schema migration to (b,k)=(4,3)**:
  - The "negative finding" at n = 16 was a LOCAL OBSTRUCTION (existence
    of mono-free witness at small n), not a structural obstruction.
  - The surviving branch is killed by THRESHOLD TRIPLES at n = 17 (4,16,17),
    (8,15,17) + at n = 20 (12,17,20), (16,16,20), self-loop m=5.
  - **The threshold lift required is much smaller than expected**: n=20, not n=63.
  - This validates the (χ(9), χ(12), χ(16)) candidate as the b=4 first master
    forcing — it just requires more constraints than were available at n = 16.

  **Cascade structure** (8 Rado triples + 1 self-loop + 2 third_color_eq):

  Step 1 (force χ(15) = A):
    - (12, 12, 15): d=3, y=12 → χ(15) ≠ χ(12) = B
    - (4, 15, 16): d=1, y=15 → χ(15) ≠ χ(16) = C
    - third_color_eq → χ(15) = χ(9) = A

  Step 2 (force χ(17) = B):
    - (8, 15, 17): d=2, y=15 → χ(17) ≠ χ(15) = A
    - (4, 16, 17): d=1, y=16 → χ(17) ≠ χ(16) = C
    - third_color_eq → χ(17) = χ(12) = B

  Step 3 (χ(20) contradiction):
    - (12, 17, 20): d=3, y=17 → χ(20) ≠ χ(12) = B
    - (16, 16, 20): d=4, y=16 → χ(20) ≠ χ(16) = C ← key "n=20 closer"
    - self-loop m=5 b=4: χ(15) ≠ χ(20) → χ(20) ≠ A
    - third_color_eq forces χ(20) = χ(16) = C, contradicting (16, 16, 20).

  All Rado triples verified at b=4 (x + 4y = 4z):
  - (12, 12, 15): 12 + 48 = 60 = 4·15 ✓
  - (4, 15, 16): 4 + 60 = 64 = 4·16 ✓
  - (8, 15, 17): 8 + 60 = 68 = 4·17 ✓
  - (4, 16, 17): 4 + 64 = 68 = 4·17 ✓
  - (12, 17, 20): 12 + 68 = 80 = 4·20 ✓
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓ ← TERMINAL "anchor self-rado" at d=b
  - self-loop m=5 b=4: triple (20, 15, 20)

  **The terminal triple (16, 16, 20) is the b=4 analogue of "anchor self-rado"**:
  for any b, the Rado triple (b·m, b·m, (b+1)·m/1)... wait actually (b·m, b·m, ?) with
  b·m + 4·b·m = 5·b·m = 4·z gives z = 5·b·m/4 which is non-integer for b=4, m=4:
  16 + 64 = 80 = 4·20 ✓. So (16, 16, 20) = (b², b², b²+b) for b=4.
  Equivalently, (b·m, b·m, b·m + m) requires 4·(b·m + m) = b·m + 4·b·m = 5·b·m, so
  m = b·m/4. For b=4, m=4: m = b·m/4 = 4·4/4 = 4 ✓. So (16, 16, 20) is at (m=4, b=4).
-/

/-- ** main theorem**: the surviving witness branch (chi(8)=chi(9),
  chi(4)=chi(16), all distinct on (chi(9),chi(12),chi(16))) DIES at n ≥ 20.

  This is the b=4 analogue of b=3's R+213-style master forcing closure, but
  at the much smaller threshold n=20 (instead of the conservatively conjectured
  n=63). The proof uses 6 Rado triples + 1 self-loop + 2 third_color_eq.

  **Kernel-pure**: only Lean kernel axioms (propext, Quot.sound). -/
theorem bAdicEquation_4_R250_witness_branch_no_extend_to_20
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_9 : χ 8 = χ 9)
    (h4_eq_16 : χ 4 = χ 16) :
    False := by
  -- χ values < 3.
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  -- (12, 12, 15) forces χ(15) ≠ χ(12).
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  -- (4, 15, 16) forces χ(15) ≠ χ(16).
  have h15_ne_16 : χ 15 ≠ χ 16 := by
    intro h15_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 15
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_16, h15_eq_16]
    · show χ 15 = χ (15 + 1)
      rw [show (15 + 1 : ℕ) = 16 by decide, h15_eq_16]
  -- third_color_eq: χ(15) ≠ χ(12), χ(15) ≠ χ(16); χ(9) ≠ χ(12), χ(9) ≠ χ(16) ⟹ χ(15) = χ(9).
  have h15_eq_9 : χ 15 = χ 9 :=
    third_color_eq hχ15 hχ9 hχ12 hχ16 h12_ne_16 h15_ne_12 h15_ne_16 h9_ne_12 h9_ne_16
  -- (8, 15, 17) forces χ(17) ≠ χ(15) (since χ(8) = χ(9) = χ(15) = A).
  have h17_ne_15 : χ 17 ≠ χ 15 := by
    intro h17_eq_15
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 15
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_9, ← h15_eq_9]
    · show χ 15 = χ (15 + 2)
      rw [show (15 + 2 : ℕ) = 17 by decide, h17_eq_15]
  -- χ(17) ≠ χ(9): chain χ(17) ≠ χ(15) = χ(9).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    apply h17_ne_15
    rw [h17_eq_9, ← h15_eq_9]
  -- (4, 16, 17) forces χ(17) ≠ χ(16) (since χ(4) = χ(16) = C).
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 16
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16
    · show χ 16 = χ (16 + 1)
      rw [show (16 + 1 : ℕ) = 17 by decide, h17_eq_16]
  -- third_color_eq: χ(17) ≠ χ(9), χ(17) ≠ χ(16); χ(12) ≠ χ(9), χ(12) ≠ χ(16) ⟹ χ(17) = χ(12).
  have h17_eq_12 : χ 17 = χ 12 :=
    third_color_eq hχ17 hχ12 hχ9 hχ16 h9_ne_16 h17_ne_9 h17_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- (12, 17, 20) forces χ(20) ≠ χ(12) (since χ(12) = χ(17) = B).
  have h20_ne_12 : χ 20 ≠ χ 12 := by
    intro h20_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 17
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h17_eq_12.symm
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_12, h20_eq_12]
  -- (16, 16, 20) forces χ(20) ≠ χ(16) — terminal "anchor self-rado" closer.
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  -- Self-loop m=5 b=4: χ(15) ≠ χ(20).
  have h15_ne_20 : χ 15 ≠ χ 20 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 5) (by omega) (by omega)
  -- χ(20) ≠ χ(9): chain χ(20) ≠ χ(15) = χ(9).
  have h20_ne_9 : χ 20 ≠ χ 9 := by
    intro h20_eq_9
    apply h15_ne_20
    rw [h15_eq_9, h20_eq_9]
  -- third_color_eq: χ(20) ≠ χ(9), χ(20) ≠ χ(12); χ(16) ≠ χ(9), χ(16) ≠ χ(12) ⟹ χ(20) = χ(16).
  have h20_eq_16 : χ 20 = χ 16 :=
    third_color_eq hχ20 hχ16 hχ9 hχ12 h9_ne_12 h20_ne_9 h20_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- Contradicts h20_ne_16.
  exact h20_ne_16 h20_eq_16

/-- ** corollary at the n=64 threshold**: at n ≥ 64, the witness
  branch also dies. Immediate from `bAdicEquation_4_R250_witness_branch_no_extend_to_20`
  since 64 ≥ 20. -/
theorem bAdicEquation_4_R250_witness_branch_no_extend_to_64
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_9 : χ 8 = χ 9)
    (h4_eq_16 : χ 4 = χ 16) :
    False :=
  bAdicEquation_4_R250_witness_branch_no_extend_to_20 χ (by omega) hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_9 h4_eq_16

/-! ### §93. — b=4 all-distinct branch χ(8) = χ(12), χ(4) = χ(9) closure.

  **Strategic context ()**: continuing the case ledger of
  `bAdicEquation_4_no_chi_9_12_16_all_distinct`. Trichotomy on χ(8):
  - χ(8) = χ(9): CLOSED (//) for n ≥ 20.
  - **χ(8) = χ(12): this round, only χ(4) = χ(9) subcase CLOSED**.
  - χ(8) = χ(16): OPEN.

  Sub-trichotomy on χ(4) within χ(8) = χ(12):
  - **χ(4) = χ(9) (= A): CLOSED at n ≥ 20** (this round, §93).
  - χ(4) = χ(12) (= B): admits explicit witness at n=20; OPEN.
  - χ(4) = χ(16) (= C): admits explicit witness at n=20; OPEN.

  **§93 cascade structure** (9 forced positions + 1 terminal, all at n ≥ 20):

  Setup: A := χ(9) = χ(4), B := χ(12) = χ(8), C := χ(16), all distinct.

  | Step | Position forced | Triple(s) used |
  |------|-----------------|----------------|
  | 1 | χ(5) = C | (12, 5, 8) + (4, 4, 5) |
  | 2 | χ(10) = C | (8, 8, 10) + (4, 9, 10) |
  | 3 | χ(14) = A | (8, 12, 14) + (16, 10, 14) |
  | 4 | χ(15) = C | (12, 12, 15) + (4, 14, 15) |
  | 5 | χ(11) = A | (12, 8, 11) + (16, 11, 15) |
  | 6 | χ(20) = B | (20, 9, 14) + (16, 16, 20) |
  | 7 | χ(3) = C | (4, 3, 4) + (20, 3, 8) |
  | 8 | χ(7) = A | (20, 7, 12) + (16, 3, 7) |
  | 9 | χ(6) = C | (4, 6, 7) + (8, 6, 8) |
  | T | **MONO** | **(16, 6, 10): χ(16) = χ(6) = χ(10) = C** |

  All Rado triples verified for b=4 (x + 4y = 4z):
  - (12, 5, 8): 12 + 20 = 32 = 4·8 ✓ - (4, 9, 10): 4 + 36 = 40 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓ - (8, 12, 14): 8 + 48 = 56 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓ - (16, 10, 14): 16 + 40 = 56 ✓
  - (12, 12, 15): 12 + 48 = 60 ✓ - (4, 14, 15): 4 + 56 = 60 ✓
  - (12, 8, 11): 12 + 32 = 44 ✓ - (16, 11, 15): 16 + 44 = 60 ✓
  - (20, 9, 14): 20 + 36 = 56 ✓ - (16, 16, 20): 16 + 64 = 80 ✓
  - (4, 3, 4): 4 + 12 = 16 = 4·4 ✓ - (20, 3, 8): 20 + 12 = 32 ✓
  - (20, 7, 12): 20 + 28 = 48 ✓ - (16, 3, 7): 16 + 12 = 28 ✓
  - (4, 6, 7): 4 + 24 = 28 ✓ - (8, 6, 8): 8 + 24 = 32 ✓
  - **(16, 6, 10) TERMINAL: 16 + 24 = 40 ✓**

  **Terminal pattern**: NEITHER (16, 7, 11) NOR (16, 16, 20).
  Instead (16, 6, 10) — a NEW b=4 terminal triple of "C-anchored color
  matching" form (16, y, y+4) with χ(y) = χ(y+4) = C.

  **Negative findings for χ(4) ∈ {B, C} subcases** (documented for honesty,
  not encoded as Lean theorems; do not falsely close):

  χ(4) = B witness at n=20 (chi(8)=chi(12)=B, chi(4)=B, chi(16)=C):
    χ = (1→A 2→A 3→A 4→B 5→A 6→A 7→A 8→B 9→A 10→A
         11→A 12→B 13→A 14→A 15→A 16→C 17→A 18→A 19→A 20→B)
  Verified mono-free for bAdicEquation 4 on [1, 20].

  χ(4) = C witness at n=20 (chi(8)=chi(12)=B, chi(4)=C, chi(16)=C):
    χ = (1→A 2→A 3→A 4→C 5→A 6→A 7→A 8→B 9→A 10→A
         11→A 12→B 13→A 14→A 15→A 16→C 17→A 18→A 19→A 20→B)
  Verified mono-free for bAdicEquation 4 on [1, 20].

  **Killing the remaining subcases** requires either:
  - Lift to n ≥ 64 + use thm_k2 (R(4, 2) = 16) for multiples-of-4 substructure
    (since at n=64 the multiples {4, 8,..., 64} form a 2-coloring of [1, 16]
    in {B, C}, forcing mono via thm_k2).
  - OR a longer in-place cascade not yet found.
-/

/-- ** main subcase theorem** (Deliverable B — strongest complete subcase).
  In any mono-free 3-coloring for bAdicEquation 4 on [1, n] (n ≥ 20), if
  (χ(9), χ(12), χ(16)) are pairwise distinct AND χ(8) = χ(12) AND χ(4) = χ(9),
  then False.

  Cascade: 9 forced equalities + terminal mono (16, 6, 10).
  **Kernel-pure**: only Lean kernel axioms. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h4_eq_9 : χ 4 = χ 9) :
    False := by
  -- χ values < 3.
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  -- STEP 1: χ(5) = χ(16). (12, 5, 8) + (4, 4, 5) + third_color_eq.
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 5
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h5_eq_12.symm
    · show χ 5 = χ (5 + 3)
      rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_9, h5_eq_9]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 2: χ(10) = χ(16). (8, 8, 10) + (4, 9, 10).
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 9
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_9
    · show χ 9 = χ (9 + 1)
      rw [show (9 + 1 : ℕ) = 10 by decide, h10_eq_9]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 3: χ(14) = χ(9). (8, 12, 14) + (16, 10, 14).
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 10
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h10_eq_16.symm
    · show χ 10 = χ (10 + 4)
      rw [show (10 + 4 : ℕ) = 14 by decide, h10_eq_16, h14_eq_16]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ12 hχ16 h12_ne_16 h14_ne_12 h14_ne_16 h9_ne_12 h9_ne_16
  -- STEP 4: χ(15) = χ(16). (12, 12, 15) + (4, 14, 15).
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 14
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, ← h14_eq_9]
    · show χ 14 = χ (14 + 1)
      rw [show (14 + 1 : ℕ) = 15 by decide, h14_eq_9, h15_eq_9]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 5: χ(11) = χ(9). (12, 8, 11) + (16, 11, 15).
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- STEP 6: χ(20) = χ(12). (20, 9, 14) + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 := by
    intro h20_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 9
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_9
    · show χ 9 = χ (9 + 5)
      rw [show (9 + 5 : ℕ) = 14 by decide]; exact h14_eq_9.symm
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 7: χ(3) = χ(16). (4, 3, 4) + (20, 3, 8).
  have h3_ne_9 : χ 3 ≠ χ 9 := by
    intro h3_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, h3_eq_9]
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h4_eq_9, h3_eq_9]
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 3
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, h3_eq_12]
    · show χ 3 = χ (3 + 5)
      rw [show (3 + 5 : ℕ) = 8 by decide, h3_eq_12, ← h8_eq_12]
  have h3_eq_16 : χ 3 = χ 16 :=
    third_color_eq hχ3 hχ16 hχ9 hχ12 h9_ne_12 h3_ne_9 h3_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 8: χ(7) = χ(9). (20, 7, 12) + (16, 3, 7).
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 7
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, h7_eq_12]
    · show χ 7 = χ (7 + 5)
      rw [show (7 + 5 : ℕ) = 12 by decide, h7_eq_12]
  have h7_ne_16 : χ 7 ≠ χ 16 := by
    intro h7_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 3
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h3_eq_16.symm
    · show χ 3 = χ (3 + 4)
      rw [show (3 + 4 : ℕ) = 7 by decide, h3_eq_16, h7_eq_16]
  have h7_eq_9 : χ 7 = χ 9 :=
    third_color_eq hχ7 hχ9 hχ12 hχ16 h12_ne_16 h7_ne_12 h7_ne_16 h9_ne_12 h9_ne_16
  -- STEP 9: χ(6) = χ(16). (4, 6, 7) + (8, 6, 8).
  have h6_ne_9 : χ 6 ≠ χ 9 := by
    intro h6_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 6
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, h6_eq_9]
    · show χ 6 = χ (6 + 1)
      rw [show (6 + 1 : ℕ) = 7 by decide, h6_eq_9, ← h7_eq_9]
  have h6_ne_12 : χ 6 ≠ χ 12 := by
    intro h6_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 6
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_12, h6_eq_12]
    · show χ 6 = χ (6 + 2)
      rw [show (6 + 2 : ℕ) = 8 by decide, h6_eq_12, ← h8_eq_12]
  have h6_eq_16 : χ 6 = χ 16 :=
    third_color_eq hχ6 hχ16 hχ9 hχ12 h9_ne_12 h6_ne_9 h6_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (16, 6, 10). χ(16) = χ(6) = χ(10) = C. MONO!
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 6
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h6_eq_16.symm
  · show χ 6 = χ (6 + 4)
    rw [show (6 + 4 : ℕ) = 10 by decide, h6_eq_16, ← h10_eq_16]

/-- corollary at the n = 64 threshold: immediate from
  `bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9` since 64 ≥ 20. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9_at_64
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h4_eq_9 : χ 4 = χ 9) :
    False :=
  bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9 χ (by omega) hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_12 h4_eq_9

/-! ### §94. — b=4 all-distinct branch χ(8) = χ(16), trichotomy on χ(4).

  **Strategic context ()**: orthogonal third trichotomy branch on χ(8).
  - χ(8) = χ(9): CLOSED for n ≥ 20 (//).
  - χ(8) = χ(12): PARTIAL — only χ(4) = A subcase CLOSED (); χ(4) ∈ {B, C}
    admit n=20 witnesses (documented in §93).
  - **χ(8) = χ(16): this round.**

  Sub-trichotomy on χ(4) within χ(8) = χ(16):
  - **χ(4) = χ(9) (= A): CLOSED at n ≥ 20** via terminal (4, 3, 4).
  - χ(4) = χ(12) (= B): admits explicit witness at n=20; OPEN.
  - **χ(4) = χ(16) (= C): TRIVIAL at n ≥ 16** via terminal (16, 4, 8).

  **§94 cascade structure** (subcase χ(4) = A, 6 forced positions + 1 terminal):

  Setup: A := χ(9) = χ(4), B := χ(12), C := χ(16) = χ(8), all distinct.

  | Step | Position forced | Triple(s) used |
  |------|-----------------|----------------|
  | 1 | χ(20) = B | (16, 16, 20) + (20, 4, 9) |
  | 2 | χ(10) = B | (8, 8, 10) + (4, 9, 10) |
  | 3 | χ(5) = C | (4, 4, 5) + (20, 5, 10) |
  | 4 | χ(7) = A | (8, 5, 7) + (12, 7, 10) |
  | 5 | χ(6) = B | (8, 6, 8) + (4, 6, 7) |
  | 6 | χ(3) = A | (8, 3, 5) + (12, 3, 6) |
  | T | **MONO** | **(4, 3, 4): χ(4) = χ(3) = A — "anchor self-equality"** |

  **NEW terminal pattern**: (4, 3, 4) is a "degenerate self-equality" Rado triple,
  where mono iff χ(3) = χ(4). This is the FOURTH distinct terminal pattern in
  the b=4 all-distinct branch closures:
  - (chi(8)=chi(9), chi(4)=chi(12)): terminal (16, 7, 11)
  - (chi(8)=chi(9), chi(4)=chi(16)): terminal (16, 16, 20) — anchor self-rado
  - (chi(8)=chi(12), chi(4)=chi(9)): terminal (16, 6, 10) — C-anchored match
  - ** (chi(8)=chi(16), chi(4)=chi(9)): terminal (4, 3, 4) — anchor self-equality**

  All Rado triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (20, 4, 9): 20 + 16 = 36 = 4·9 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (4, 9, 10): 4 + 36 = 40 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (20, 5, 10): 20 + 20 = 40 ✓
  - (8, 5, 7): 8 + 20 = 28 = 4·7 ✓
  - (12, 7, 10): 12 + 28 = 40 ✓
  - (8, 6, 8): 8 + 24 = 32 = 4·8 ✓
  - (4, 6, 7): 4 + 24 = 28 ✓
  - (8, 3, 5): 8 + 12 = 20 ✓
  - (12, 3, 6): 12 + 12 = 24 = 4·6 ✓
  - **(4, 3, 4) TERMINAL: 4 + 12 = 16 = 4·4 ✓**

  **Subcase χ(4) = C (trivial)**: (16, 4, 8) Rado triple with χ(16) = χ(4) = χ(8)
  = C → MONO. Closes at n ≥ 16 in a single triple.

  **Subcase χ(4) = B (OPEN, witness at n=20)** — explicit mono-free witness:
    χ = (1→A 2→A 3→A 4→B 5→A 6→A 7→A 8→C 9→A 10→A
         11→A 12→B 13→A 14→A 15→A 16→C 17→A 18→A 19→A 20→B)
  Verified mono-free for all 85 bAdicEquation 4 Rado triples on [1, 20].

  Killing the χ(4) = B subcase at n ≥ 64 requires thm_k2 (R(4, 2) = 16) +
  scale-by-4 reduction: in this subcase, mults of 4 in [4, 64] are forced into
  {B, C} (by self-loops + anchor self-rados), yielding 16 positions 2-colored,
  hence a mono triple via thm_k2. Building this infrastructure is deferred to.
-/

/-- ** subcase 1**: χ(8) = χ(16), χ(4) = χ(9). CLOSED at n ≥ 20 via cascade
  ending in terminal (4, 3, 4) — "anchor self-equality" pattern (mono iff χ(3) = χ(4)).
  **Kernel-pure**: only Lean kernel axioms. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_16 : χ 8 = χ 16)
    (h4_eq_9 : χ 4 = χ 9) :
    False := by
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  -- STEP 1: χ(20) = χ(12). (16, 16, 20) + (20, 4, 9).
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_ne_9 : χ 20 ≠ χ 9 := by
    intro h20_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 4
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h4_eq_9]
    · show χ 4 = χ (4 + 5)
      rw [show (4 + 5 : ℕ) = 9 by decide]; exact h4_eq_9
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 2: χ(10) = χ(12). (8, 8, 10) + (4, 9, 10).
  have h10_ne_16 : χ 10 ≠ χ 16 := by
    intro h10_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_16, h10_eq_16]
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 9
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_9
    · show χ 9 = χ (9 + 1)
      rw [show (9 + 1 : ℕ) = 10 by decide, h10_eq_9]
  have h10_eq_12 : χ 10 = χ 12 :=
    third_color_eq hχ10 hχ12 hχ9 hχ16 h9_ne_16 h10_ne_9 h10_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 3: χ(5) = χ(16). (4, 4, 5) + (20, 5, 10).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_9, h5_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 5
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, h5_eq_12]
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_12, ← h10_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 4: χ(7) = χ(9). (8, 5, 7) + (12, 7, 10).
  have h7_ne_16 : χ 7 ≠ χ 16 := by
    intro h7_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 5
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h5_eq_16]
    · show χ 5 = χ (5 + 2)
      rw [show (5 + 2 : ℕ) = 7 by decide, h5_eq_16, h7_eq_16]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 7
      rw [show (4 * 3 : ℕ) = 12 by decide, h7_eq_12]
    · show χ 7 = χ (7 + 3)
      rw [show (7 + 3 : ℕ) = 10 by decide, h7_eq_12, ← h10_eq_12]
  have h7_eq_9 : χ 7 = χ 9 :=
    third_color_eq hχ7 hχ9 hχ12 hχ16 h12_ne_16 h7_ne_12 h7_ne_16 h9_ne_12 h9_ne_16
  -- STEP 5: χ(6) = χ(12). (8, 6, 8) + (4, 6, 7).
  have h6_ne_16 : χ 6 ≠ χ 16 := by
    intro h6_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 6
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, h6_eq_16]
    · show χ 6 = χ (6 + 2)
      rw [show (6 + 2 : ℕ) = 8 by decide, h6_eq_16, ← h8_eq_16]
  have h6_ne_9 : χ 6 ≠ χ 9 := by
    intro h6_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 6
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, h6_eq_9]
    · show χ 6 = χ (6 + 1)
      rw [show (6 + 1 : ℕ) = 7 by decide, h6_eq_9, ← h7_eq_9]
  have h6_eq_12 : χ 6 = χ 12 :=
    third_color_eq hχ6 hχ12 hχ9 hχ16 h9_ne_16 h6_ne_9 h6_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 6: χ(3) = χ(9). (8, 3, 5) + (12, 3, 6).
  have h3_ne_16 : χ 3 ≠ χ 16 := by
    intro h3_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 3
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, h3_eq_16]
    · show χ 3 = χ (3 + 2)
      rw [show (3 + 2 : ℕ) = 5 by decide, h3_eq_16, ← h5_eq_16]
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 3
      rw [show (4 * 3 : ℕ) = 12 by decide, h3_eq_12]
    · show χ 3 = χ (3 + 3)
      rw [show (3 + 3 : ℕ) = 6 by decide, h3_eq_12, ← h6_eq_12]
  have h3_eq_9 : χ 3 = χ 9 :=
    third_color_eq hχ3 hχ9 hχ12 hχ16 h12_ne_16 h3_ne_12 h3_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (4, 3, 4). χ(4) = χ(3), χ(3) = χ(4). Both iff χ(3) = χ(4) = χ(9). MONO!
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 1) = χ 3
    rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, ← h3_eq_9]
  · show χ 3 = χ (3 + 1)
    rw [show (3 + 1 : ℕ) = 4 by decide, h4_eq_9, ← h3_eq_9]

/-- ** subcase 3** (trivial): χ(8) = χ(16), χ(4) = χ(16). CLOSED at n ≥ 16
  via single Rado triple (16, 4, 8) where χ(16) = χ(4) = χ(8) = C → MONO.
  **Kernel-pure**: only Lean kernel axioms. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_16
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_16 : χ 8 = χ 16)
    (h4_eq_16 : χ 4 = χ 16) :
    False := by
  -- Direct mono via (16, 4, 8): χ(16) = χ(4) = χ(8) = C.
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 4) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 4
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h4_eq_16.symm
  · show χ 4 = χ (4 + 4)
    rw [show (4 + 4 : ℕ) = 8 by decide, h4_eq_16, ← h8_eq_16]

/-- subcase 1 corollary at n = 64 threshold. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9_at_64
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h8_eq_16 : χ 8 = χ 16)
    (h4_eq_9 : χ 4 = χ 9) :
    False :=
  bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9 χ (by omega) hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_16 h4_eq_9

/-! ### §96. — residual cell (1) layer compression cascade (initial prefix).

  **Strategic context ()**: with the scale-by-4 bridge in place, the
  remaining work is to PROVE layer compression (χ(4d) ∈ {χ(12), χ(16)} for
  d ∈ [1, 16]) for each of the 3 surviving residual cells. attacks the
  FIRST nontrivial layer-compression value for cell (1): χ(20) ∈ {χ(12), χ(16)},
  equivalently χ(20) ≠ χ(9).

  **§96 strategy (from §95 documentation)**: assume for contradiction
  χ(20) = χ(9) = A. Derive a long forced cascade culminating in χ(40) excluded
  from all 3 colors at n ≥ 40.

  **§96 cascade structure** (clean prefix, n ≥ 20):

  Setup: A := χ(9), B := χ(12), C := χ(16), all distinct. Cell (1):
  χ(4) = χ(8) = B. Additional hypothesis: χ(20) = χ(9) = A.

  | Step | Position forced | Triple(s) used |
  |------|-----------------|----------------|
  | 1 | χ(14) = χ(16) | (8, 12, 14) [d=2,y=12] + (20, 9, 14) [d=5,y=9] |
  | 2 | χ(10) = χ(9) | (8, 8, 10) [d=2,y=8] + (16, 10, 14) [d=4,y=10] |
  | 3 | χ(15) = χ(16) | (12, 12, 15) [d=3,y=12] + self-loop m=5 [(20,15,20)] |
  | 4 | χ(11) = χ(9) | (12, 8, 11) [d=3,y=8] + (16, 11, 15) [d=4,y=11] |

  All Rado triples verified for b=4 (x + 4y = 4z):
  - (8, 12, 14): 8 + 48 = 56 = 4·14 ✓
  - (20, 9, 14): 20 + 36 = 56 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (16, 10, 14): 16 + 40 = 56 ✓
  - (12, 12, 15): 12 + 48 = 60 = 4·15 ✓
  - self-loop m=5 b=4: (20, 15, 20)
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓
  - (16, 11, 15): 16 + 44 = 60 ✓

  **Extended cascade (clean continuation, +)**:
  - Step 5 (χ(5) = χ(16)): (4, 4, 5) [d=1] + (20, 5, 10) [d=5,y=5] using
    χ(10) = χ(9) from Step 2.
  - Step 6 (χ(6) = χ(16)): self-loop m=2 [(8, 6, 8)] + (20, 6, 11) [d=5,y=6]
    using χ(11) = χ(9) from Step 4.
  - Step 7 (χ(2) = χ(9)): (8, 2, 4) [d=2,y=2] + (16, 2, 6) [d=4,y=2] using
    χ(6) = χ(16) from Step 6.
  - Step 8 (χ(7) = χ(16)): (4, 7, 8) [d=1,y=7] + (20, 2, 7) [d=5,y=2] using
    χ(2) = χ(9) from Step 7.
  - Step 9 (χ(3) = χ(9)): (4, 3, 4) [d=1,y=3] + (16, 3, 7) [d=4,y=3] using
    χ(7) = χ(16) from Step 8.
  - Step 10 (χ(1) = χ(9)): (12, 1, 4) [d=3,y=1] + (16, 1, 5) [d=4,y=1] using
    χ(5) = χ(16) from Step 5.

  After Steps 1-10, A positions: 1, 2, 3, 9, 10, 11, 20. B: 4, 8, 12. C: 5, 6,
  7, 14, 15, 16. Unforced: 13, 17, 18, 19.

  **n ≤ 20 OBSERVATION**: at n = 20, no mono triple exists among the forced
  positions, regardless of the unforced 13/17/18/19 values. Hence χ(20) = χ(9)
  is CONSISTENT with cell (1) at n = 20. Closing layer compression at d = 5
  requires reaching n ≥ 40 and forcing χ(28), χ(30), χ(32), χ(36) to derive
  the χ(40) ∉ {A, B, C} contradiction.

  **Open obstruction for full d = 5 closure (+)**: the chain involves
  CASE SPLITS on χ(13) ∈ {A, C} (since (4,12,13) → χ(13) ≠ B but no further
  unconditional constraint). In Case χ(13) = A, χ(18) = B and χ(19) = A are
  forced, then χ(24) = C, χ(28) = B, χ(32) = B, χ(36) = C, then χ(40) ∉ {A, B, C}.
  In Case χ(13) = C, sub-cases on χ(17), χ(18), χ(19) require deeper analysis.
  + should formalize Case χ(13) = A first (cleaner cascade), then handle
  Case χ(13) = C as a separate theorem.

  **DELIVERABLE B for **: the clean Steps 1-4 prefix below. Steps 5-10
  follow the same pattern but are deferred to keep this theorem focused.
-/

/-- ** partial cascade** (Deliverable B): residual cell (1) + χ(20) = χ(9)
  forces χ(14) = χ(16), χ(10) = χ(9), χ(15) = χ(16), χ(11) = χ(9).

  Strongest contiguous prefix of the §96 cascade toward d = 5 layer
  compression. Each step uses 2 Rado-triple obstructions + 1 third_color_eq.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_forces_chi14_10_15_11
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9) :
    χ 14 = χ 16 ∧ χ 10 = χ 9 ∧ χ 15 = χ 16 ∧ χ 11 = χ 9 := by
  -- IsKColoring instantiations.
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- STEP 1: χ(14) = χ(16). (8, 12, 14) + (20, 9, 14).
  -- (8, 12, 14): d=2, y=12. Mono iff χ(8) = χ(12) (true by h8_eq_12) ∧ χ(12) = χ(14).
  -- So mono iff χ(14) = χ(12). → χ(14) ≠ χ(12).
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  -- (20, 9, 14): d=5, y=9. Mono iff χ(20) = χ(9) (true by h20_eq_9) ∧ χ(9) = χ(14).
  -- So mono iff χ(14) = χ(9). → χ(14) ≠ χ(9).
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 9
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_9
    · show χ 9 = χ (9 + 5)
      rw [show (9 + 5 : ℕ) = 14 by decide, h14_eq_9]
  -- third_color_eq: χ(14) ≠ χ(9), χ(14) ≠ χ(12) ⟹ χ(14) = χ(16).
  have h14_eq_16 : χ 14 = χ 16 :=
    third_color_eq hχ14 hχ16 hχ9 hχ12 h9_ne_12 h14_ne_9 h14_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 2: χ(10) = χ(9). (8, 8, 10) + (16, 10, 14).
  -- (8, 8, 10): d=2, y=8. Mono iff χ(8) = χ(8) (trivial) ∧ χ(8) = χ(10).
  -- So mono iff χ(10) = χ(8) = χ(12). → χ(10) ≠ χ(12).
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  -- (16, 10, 14): d=4, y=10. Mono iff χ(16) = χ(10) ∧ χ(10) = χ(14).
  -- χ(14) = χ(16). So mono iff χ(10) = χ(16). → χ(10) ≠ χ(16).
  have h10_ne_16 : χ 10 ≠ χ 16 := by
    intro h10_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 10
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h10_eq_16.symm
    · show χ 10 = χ (10 + 4)
      rw [show (10 + 4 : ℕ) = 14 by decide, h10_eq_16, ← h14_eq_16]
  -- third_color_eq: χ(10) ≠ χ(12), χ(10) ≠ χ(16) ⟹ χ(10) = χ(9).
  have h10_eq_9 : χ 10 = χ 9 :=
    third_color_eq hχ10 hχ9 hχ12 hχ16 h12_ne_16 h10_ne_12 h10_ne_16 h9_ne_12 h9_ne_16
  -- STEP 3: χ(15) = χ(16). (12, 12, 15) + self-loop m=5.
  -- (12, 12, 15): d=3, y=12. Mono iff χ(15) = χ(12). → χ(15) ≠ χ(12).
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  -- Self-loop m=5: χ(15) ≠ χ(20) = χ(9). → χ(15) ≠ χ(9).
  have h15_ne_20 : χ 15 ≠ χ 20 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 5) (by omega) (by omega)
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    apply h15_ne_20
    rw [h15_eq_9, ← h20_eq_9]
  -- third_color_eq: χ(15) = χ(16).
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 4: χ(11) = χ(9). (12, 8, 11) + (16, 11, 15).
  -- (12, 8, 11): d=3, y=8. Mono iff χ(12) = χ(8) (true) ∧ χ(8) = χ(11).
  -- So mono iff χ(11) = χ(12). → χ(11) ≠ χ(12).
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  -- (16, 11, 15): d=4, y=11. Mono iff χ(11) = χ(15) = χ(16). → χ(11) ≠ χ(16).
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  -- third_color_eq: χ(11) = χ(9).
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  exact ⟨h14_eq_16, h10_eq_9, h15_eq_16, h11_eq_9⟩

/-! ### §97. — residual cell (1) cascade prefix Steps 5-10 (no χ(13) split).

  **Strategic context ()**: continuing prefix, extend the clean
  no-case-split cascade to force the remaining LOW positions (1, 2, 3, 5, 6, 7).
  After, the only unforced positions in [1, 20] are {13, 17, 18, 19}.
  The χ(13) case split (+) will reduce these to the χ(40) contradiction
  cascade documented in §95/§96.

  **§97 cascade structure** (Steps 5-10, all clean — no case splits):

  Setup unchanged from §96. Given the prefix
  (χ(14)=C, χ(10)=A, χ(15)=C, χ(11)=A) under χ(20)=A:

  | Step | Position forced | Triple(s) used |
  |------|-----------------|----------------|
  | 5 | χ(5) = χ(16) | (4, 4, 5) [d=1,y=4] + (20, 5, 10) [d=5,y=5] |
  | 6 | χ(6) = χ(16) | self-loop m=2 [(8, 6, 8)] + (20, 6, 11) [d=5,y=6] |
  | 7 | χ(2) = χ(9) | (8, 2, 4) [d=2,y=2] + (16, 2, 6) [d=4,y=2] |
  | 8 | χ(7) = χ(16) | (4, 7, 8) [d=1,y=7] + (20, 2, 7) [d=5,y=2] |
  | 9 | χ(3) = χ(9) | (4, 3, 4) [d=1,y=3] + (16, 3, 7) [d=4,y=3] |
  | 10 | χ(1) = χ(9) | (12, 1, 4) [d=3,y=1] + (16, 1, 5) [d=4,y=1] |

  All Rado triples verified for b=4 (x + 4y = 4z):
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (20, 5, 10): 20 + 20 = 40 = 4·10 ✓
  - self-loop m=2: (8, 6, 8)
  - (20, 6, 11): 20 + 24 = 44 = 4·11 ✓
  - (8, 2, 4): 8 + 8 = 16 = 4·4 ✓
  - (16, 2, 6): 16 + 8 = 24 = 4·6 ✓
  - (4, 7, 8): 4 + 28 = 32 = 4·8 ✓
  - (20, 2, 7): 20 + 8 = 28 = 4·7 ✓
  - (4, 3, 4): 4 + 12 = 16 = 4·4 ✓
  - (16, 3, 7): 16 + 12 = 28 = 4·7 ✓
  - (12, 1, 4): 12 + 4 = 16 = 4·4 ✓
  - (16, 1, 5): 16 + 4 = 20 = 4·5 ✓

  **After + **: forced positions are
  - χ(9) (= A): positions 1, 2, 3, 9, 10, 11, 20.
  - χ(12) (= B): positions 4, 8, 12.
  - χ(16) (= C): positions 5, 6, 7, 14, 15, 16.

  **Remaining unknown set: {13, 17, 18, 19}**.

  **Mono-free verification at n = 20**: no Rado triple (x + 4y = 4z, x ∈ {4, 8, 12,
  16, 20}, y, z ∈ [1, 20]) gives mono among forced positions — verified by
  exhaustive enumeration in §95/§96 §93 notes. Hence χ(20) = χ(9) remains
  CONSISTENT at n = 20 even after Steps 1-10. + must push to higher n.

  ** target** (next round): case split on χ(13). The cleaner sub-case is
  χ(13) = χ(9), which forces χ(18) = χ(12) (via (4, 17, 18) + …), χ(19) = χ(9)
  (via (16, 15, 19) + (4, 18, 19)), then χ(24) = χ(16) at n ≥ 24, etc., toward
  the χ(40) ∉ {A, B, C} contradiction at n ≥ 40.
-/

/-- ** cascade extension** (Deliverable B continuation): given prefix
  (χ(14)=χ(16), χ(10)=χ(9), χ(15)=χ(16), χ(11)=χ(9)) under residual cell (1)
  + χ(20)=χ(9), force the remaining LOW positions:
    χ(5) = χ(16), χ(6) = χ(16), χ(2) = χ(9),
    χ(7) = χ(16), χ(3) = χ(9), χ(1) = χ(9).

  Takes prefix as explicit hypotheses for composability in. Each
  step: 2 Rado-triple obstructions + 1 third_color_eq.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_forces_chi5_6_2_7_3_1
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9)
    (h14_eq_16 : χ 14 = χ 16)
    (h10_eq_9 : χ 10 = χ 9)
    (h15_eq_16 : χ 15 = χ 16)
    (h11_eq_9 : χ 11 = χ 9) :
    χ 5 = χ 16 ∧ χ 6 = χ 16 ∧ χ 2 = χ 9 ∧ χ 7 = χ 16 ∧ χ 3 = χ 9 ∧ χ 1 = χ 9 := by
  -- IsKColoring instantiations.
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- STEP 5: χ(5) = χ(16). (4, 4, 5) + (20, 5, 10).
  -- (4, 4, 5): d=1, y=4. Mono iff χ(4) = χ(4) ∧ χ(4) = χ(5). Both iff χ(5) = χ(4) = χ(12).
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  -- (20, 5, 10): d=5, y=5. Mono iff χ(20) = χ(5) ∧ χ(5) = χ(10). Both iff χ(5) = χ(9).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 5
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, h5_eq_9]
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_9, ← h10_eq_9]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 6: χ(6) = χ(16). self-loop m=2 (8, 6, 8) + (20, 6, 11).
  -- self-loop m=2: χ(6) ≠ χ(8) = χ(12). → χ(6) ≠ χ(12).
  have h6_ne_8 : χ 6 ≠ χ 8 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 2) (by omega) (by omega)
  have h6_ne_12 : χ 6 ≠ χ 12 := by
    intro h6_eq_12
    apply h6_ne_8
    rw [h6_eq_12, ← h8_eq_12]
  -- (20, 6, 11): d=5, y=6. Mono iff χ(20) = χ(6) ∧ χ(6) = χ(11). Both iff χ(6) = χ(9).
  have h6_ne_9 : χ 6 ≠ χ 9 := by
    intro h6_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 6
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, h6_eq_9]
    · show χ 6 = χ (6 + 5)
      rw [show (6 + 5 : ℕ) = 11 by decide, h6_eq_9, ← h11_eq_9]
  have h6_eq_16 : χ 6 = χ 16 :=
    third_color_eq hχ6 hχ16 hχ9 hχ12 h9_ne_12 h6_ne_9 h6_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 7: χ(2) = χ(9). (8, 2, 4) + (16, 2, 6).
  -- (8, 2, 4): d=2, y=2. Mono iff χ(8) = χ(2) ∧ χ(2) = χ(4). Both iff χ(2) = χ(12).
  have h2_ne_12 : χ 2 ≠ χ 12 := by
    intro h2_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 2
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_12, h2_eq_12]
    · show χ 2 = χ (2 + 2)
      rw [show (2 + 2 : ℕ) = 4 by decide, h4_eq_12, h2_eq_12]
  -- (16, 2, 6): d=4, y=2. Mono iff χ(16) = χ(2) ∧ χ(2) = χ(6). χ(6) = χ(16). Mono iff χ(2) = χ(16).
  have h2_ne_16 : χ 2 ≠ χ 16 := by
    intro h2_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 2
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h2_eq_16.symm
    · show χ 2 = χ (2 + 4)
      rw [show (2 + 4 : ℕ) = 6 by decide, h2_eq_16, ← h6_eq_16]
  have h2_eq_9 : χ 2 = χ 9 :=
    third_color_eq hχ2 hχ9 hχ12 hχ16 h12_ne_16 h2_ne_12 h2_ne_16 h9_ne_12 h9_ne_16
  -- STEP 8: χ(7) = χ(16). (4, 7, 8) + (20, 2, 7).
  -- (4, 7, 8): d=1, y=7. Mono iff χ(4) = χ(7) ∧ χ(7) = χ(8). Both iff χ(7) = χ(12).
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 7
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h7_eq_12]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h7_eq_12, ← h8_eq_12]
  -- (20, 2, 7): d=5, y=2. Mono iff χ(20) = χ(2) ∧ χ(2) = χ(7). χ(20) = χ(2) = χ(9). Mono iff χ(7) = χ(9).
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 2
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h2_eq_9]
    · show χ 2 = χ (2 + 5)
      rw [show (2 + 5 : ℕ) = 7 by decide, h2_eq_9, h7_eq_9]
  have h7_eq_16 : χ 7 = χ 16 :=
    third_color_eq hχ7 hχ16 hχ9 hχ12 h9_ne_12 h7_ne_9 h7_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 9: χ(3) = χ(9). (4, 3, 4) + (16, 3, 7).
  -- (4, 3, 4): d=1, y=3. Mono iff χ(4) = χ(3) ∧ χ(3) = χ(4). Both iff χ(3) = χ(4) = χ(12).
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h3_eq_12]
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h4_eq_12, h3_eq_12]
  -- (16, 3, 7): d=4, y=3. Mono iff χ(16) = χ(3) ∧ χ(3) = χ(7). χ(7) = χ(16). Mono iff χ(3) = χ(16).
  have h3_ne_16 : χ 3 ≠ χ 16 := by
    intro h3_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 3
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h3_eq_16.symm
    · show χ 3 = χ (3 + 4)
      rw [show (3 + 4 : ℕ) = 7 by decide, h3_eq_16, ← h7_eq_16]
  have h3_eq_9 : χ 3 = χ 9 :=
    third_color_eq hχ3 hχ9 hχ12 hχ16 h12_ne_16 h3_ne_12 h3_ne_16 h9_ne_12 h9_ne_16
  -- STEP 10: χ(1) = χ(9). (12, 1, 4) + (16, 1, 5).
  -- (12, 1, 4): d=3, y=1. Mono iff χ(12) = χ(1) ∧ χ(1) = χ(4). χ(4) = χ(12). Mono iff χ(1) = χ(12).
  have h1_ne_12 : χ 1 ≠ χ 12 := by
    intro h1_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 1
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h1_eq_12.symm
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_12, h1_eq_12]
  -- (16, 1, 5): d=4, y=1. Mono iff χ(16) = χ(1) ∧ χ(1) = χ(5). χ(5) = χ(16). Mono iff χ(1) = χ(16).
  have h1_ne_16 : χ 1 ≠ χ 16 := by
    intro h1_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 1
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h1_eq_16.symm
    · show χ 1 = χ (1 + 4)
      rw [show (1 + 4 : ℕ) = 5 by decide, h1_eq_16, ← h5_eq_16]
  have h1_eq_9 : χ 1 = χ 9 :=
    third_color_eq hχ1 hχ9 hχ12 hχ16 h12_ne_16 h1_ne_12 h1_ne_16 h9_ne_12 h9_ne_16
  exact ⟨h5_eq_16, h6_eq_16, h2_eq_9, h7_eq_16, h3_eq_9, h1_eq_9⟩

/-! ### §98. — residual cell (1), χ(13) = χ(9) branch forces χ(18), χ(19).

  **Strategic context ()**: with + forcing 10 positions in [1, 20]
  under residual cell (1) + χ(20) = χ(9), the remaining unforced set was
  {χ(13), χ(17), χ(18), χ(19)}. begins the χ(13) case split. Under the
  branch hypothesis χ(13) = χ(9), force χ(18) = χ(12), χ(19) = χ(9) cleanly
  (no χ(17) split required).

  **§98 forcing structure** (Case χ(13) = χ(9) = A, n ≥ 20):

  | Step | Position forced | Triple(s) used |
  |------|-----------------|----------------|
  | 1 | χ(18) = χ(12) | (20, 13, 18) [d=5,y=13] + (16, 14, 18) [d=4,y=14] |
  | 2 | χ(19) = χ(9) | (16, 15, 19) [d=4,y=15] + (4, 18, 19) [d=1,y=18] |

  Arithmetic verification (b=4, x + 4y = 4z):
  - (20, 13, 18): 20 + 52 = 72 = 4·18 ✓
  - (16, 14, 18): 16 + 56 = 72 = 4·18 ✓
  - (16, 15, 19): 16 + 60 = 76 = 4·19 ✓
  - (4, 18, 19): 4 + 72 = 76 = 4·19 ✓

  **After + + **: forced positions in [1, 20] = {1..16, 18, 19, 20}.
  Remaining unknown: {χ(17)} only.

  **n ≤ 20 mono-free check** (case χ(13) = A): even with χ(17) free, no
  mono triple in [1, 20]. To close, must push to n ≥ 24 cascade for χ(24),
  χ(28), χ(32), χ(36), χ(40) leading to χ(40) ∉ {A, B, C} contradiction.

  ** target**: extend cascade to high positions {24, 28, 32, 36} and
  derive χ(40) contradiction. The χ(17) value remains free in [1, 20] but
  may be forced incidentally at high-position step.
-/

/-- ** χ(13) = χ(9) branch forcing** (residual cell (1)).
  Given residual cell (1) hypotheses + χ(20) = χ(9) + / prefix (10
  forced positions) + the branch hypothesis χ(13) = χ(9), force
    χ(18) = χ(12) ∧ χ(19) = χ(9).

  Uses 4 Rado triples + 2 third_color_eq. Closes cleanly with NO dependence
  on χ(17). After, only χ(17) remains unforced in [1, 20] for this case.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi9_forces_chi18_19
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (_h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9)
    -- prefix:
    (h14_eq_16 : χ 14 = χ 16)
    (_h10_eq_9 : χ 10 = χ 9)
    (h15_eq_16 : χ 15 = χ 16)
    (_h11_eq_9 : χ 11 = χ 9)
    -- prefix (unused in this short step; kept for composition with ):
    (_h5_eq_16 : χ 5 = χ 16)
    (_h6_eq_16 : χ 6 = χ 16)
    (_h2_eq_9 : χ 2 = χ 9)
    (_h7_eq_16 : χ 7 = χ 16)
    (_h3_eq_9 : χ 3 = χ 9)
    (_h1_eq_9 : χ 1 = χ 9)
    -- branch:
    (h13_eq_9 : χ 13 = χ 9) :
    χ 18 = χ 12 ∧ χ 19 = χ 9 := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  -- STEP 1: χ(18) = χ(12). (20, 13, 18) + (16, 14, 18).
  -- (20, 13, 18): d=5, y=13. χ(20) = χ(13) (both = χ(9)). Mono iff χ(18) = χ(13) = χ(9).
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 13
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 5)
      rw [show (13 + 5 : ℕ) = 18 by decide, h13_eq_9, h18_eq_9]
  -- (16, 14, 18): d=4, y=14. χ(16) = χ(14) (both = χ(16)). Mono iff χ(18) = χ(16).
  have h18_ne_16 : χ 18 ≠ χ 16 := by
    intro h18_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 14
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h14_eq_16.symm
    · show χ 14 = χ (14 + 4)
      rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, h18_eq_16]
  -- third_color_eq: χ(18) = χ(12).
  have h18_eq_12 : χ 18 = χ 12 :=
    third_color_eq hχ18 hχ12 hχ9 hχ16 h9_ne_16 h18_ne_9 h18_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 2: χ(19) = χ(9). (16, 15, 19) + (4, 18, 19).
  -- (16, 15, 19): d=4, y=15. χ(16) = χ(15). Mono iff χ(19) = χ(15) = χ(16).
  have h19_ne_16 : χ 19 ≠ χ 16 := by
    intro h19_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 15
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h15_eq_16.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_16, h19_eq_16]
  -- (4, 18, 19): d=1, y=18. χ(4) = χ(12), χ(18) = χ(12) (from STEP 1). Mono iff χ(19) = χ(12).
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 18
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, ← h18_eq_12]
    · show χ 18 = χ (18 + 1)
      rw [show (18 + 1 : ℕ) = 19 by decide, h18_eq_12, h19_eq_12]
  -- third_color_eq: χ(19) = χ(9).
  have h19_eq_9 : χ 19 = χ 9 :=
    third_color_eq hχ19 hχ9 hχ12 hχ16 h12_ne_16 h19_ne_12 h19_ne_16 h9_ne_12 h9_ne_16
  exact ⟨h18_eq_12, h19_eq_9⟩

/-! ### §99. — residual cell (1), χ(13)=χ(9) high-position cascade to χ(40) MONO.

  **Strategic context ()**: under residual cell (1) + χ(20)=χ(9) + χ(13)=χ(9)
  (the cleanest branch from ), extend the cascade past n=20 to derive a MONO
  Rado triple at n ≥ 40. **Closes the Case χ(13)=χ(9) layer-compression d=5
  contradiction.**

  **§99 cascade structure** (12 forced positions + 1 terminal mono, n ≥ 40):

  Setup: A := χ(9), B := χ(12), C := χ(16), all distinct. ++ prefix
  gives 14 of 16 forced positions in [1, 20] under this branch.

  | Step | Position | Forced | Key triple(s) |
  |------|----------|--------|---------------|
  | 1 | χ(24) | C | self-loop m=6 + (20, 19, 24) |
  | 2 | χ(21) | A | (12, 18, 21) + (24, 15, 21) |
  | 3 | χ(28) | B | self-loop m=7 + (16, 24, 28) |
  | 4 | χ(25) | C | anchor self-rado m=5 (20,20,25) + (28, 18, 25) |
  | 5 | χ(29) | A | (16, 25, 29) + (4, 28, 29) |
  | 6 | χ(30) | A | anchor self-rado m=6 (24,24,30) + (8, 28, 30) |
  | 7 | χ(31) | A | (12, 28, 31) + (24, 25, 31) |
  | 8 | χ(32) | A | self-loop m=8 + **(32, 4, 12)** ← key triple |
  | 9 | χ(35) | C | anchor self-rado m=7 (28,28,35) + (20, 30, 35) |
  | 10 | χ(39) | B | (16, 35, 39) + (32, 31, 39) |
  | 11 | χ(36) | C | (20, 31, 36) + (12, 36, 39) |
  | 12 | χ(40) | B | self-loop m=10 + (16, 36, 40) |
  | T | **MONO** | — | **(4, 39, 40): χ(4) = χ(39) = χ(40) = B** |

  **KEY INSIGHT**: triple (32, 4, 12) forces χ(32) ≠ B because χ(4) = χ(12) = B
  in residual cell (1). Combined with self-loop m=8 (χ(32) ≠ C), this forces
  χ(32) = A — surprisingly different from the §95 witness conjecture χ(32) = B.
  The cascade then propagates through χ(35)=C, χ(39)=B, χ(36)=C, χ(40)=B, and
  the terminal mono (4, 39, 40) is at d=1 anchor (NOT a d=4 (16, 36, 40) auto-
  non-mono as one might guess).

  Arithmetic verification (b=4, x + 4y = 4z):
  - (20, 19, 24): 20 + 76 = 96 = 4·24 ✓
  - self-loop m=6 b=4: χ(18) ≠ χ(24)
  - (12, 18, 21): 12 + 72 = 84 = 4·21 ✓
  - (24, 15, 21): 24 + 60 = 84 ✓
  - (16, 24, 28): 16 + 96 = 112 = 4·28 ✓
  - self-loop m=7: χ(21) ≠ χ(28)
  - (20, 20, 25): 20 + 80 = 100 = 4·25 ✓ (anchor self-rado m=5)
  - (28, 18, 25): 28 + 72 = 100 ✓
  - (16, 25, 29): 16 + 100 = 116 = 4·29 ✓
  - (4, 28, 29): 4 + 112 = 116 ✓
  - (24, 24, 30): 24 + 96 = 120 = 4·30 ✓ (anchor self-rado m=6)
  - (8, 28, 30): 8 + 112 = 120 ✓
  - (12, 28, 31): 12 + 112 = 124 = 4·31 ✓
  - (24, 25, 31): 24 + 100 = 124 ✓
  - self-loop m=8: χ(24) ≠ χ(32)
  - **(32, 4, 12): 32 + 16 = 48 = 4·12 ✓** (key triple)
  - (28, 28, 35): 28 + 112 = 140 = 4·35 ✓ (anchor self-rado m=7)
  - (20, 30, 35): 20 + 120 = 140 ✓
  - (16, 35, 39): 16 + 140 = 156 = 4·39 ✓
  - (32, 31, 39): 32 + 124 = 156 ✓
  - (20, 31, 36): 20 + 124 = 144 = 4·36 ✓
  - (12, 36, 39): 12 + 144 = 156 ✓
  - (16, 36, 40): 16 + 144 = 160 = 4·40 ✓
  - self-loop m=10: χ(30) ≠ χ(40)
  - **(4, 39, 40): 4 + 156 = 160 ✓** (TERMINAL MONO)
-/

set_option maxHeartbeats 800000 in
/-- ** main theorem** (Deliverable A): residual cell (1), χ(20) = χ(9),
  χ(13) = χ(9), // prefix ⟹ False at n ≥ 40.

  Closes the layer-compression d=5 contradiction for the χ(13) = χ(9) branch
  of residual cell (1) via a 12-step high-position cascade + terminal mono
  (4, 39, 40). Key new triple: (32, 4, 12) forces χ(32) ≠ χ(12) using
  χ(4) = χ(12) (residual cell hypothesis).

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi9_high_positions
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9)
    -- prefix:
    (_h14_eq_16 : χ 14 = χ 16)
    (_h10_eq_9 : χ 10 = χ 9)
    (h15_eq_16 : χ 15 = χ 16)
    (_h11_eq_9 : χ 11 = χ 9)
    -- prefix (all unused in high-position cascade; kept for composition):
    (_h5_eq_16 : χ 5 = χ 16)
    (_h6_eq_16 : χ 6 = χ 16)
    (_h2_eq_9 : χ 2 = χ 9)
    (_h7_eq_16 : χ 7 = χ 16)
    (_h3_eq_9 : χ 3 = χ 9)
    (_h1_eq_9 : χ 1 = χ 9)
    -- branch:
    (h13_eq_9 : χ 13 = χ 9)
    (h18_eq_12 : χ 18 = χ 12)
    (h19_eq_9 : χ 19 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  have hχ29 : χ 29 < 3 := hχk 29 (by omega) (by omega)
  have hχ30 : χ 30 < 3 := hχk 30 (by omega) (by omega)
  have hχ31 : χ 31 < 3 := hχk 31 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  have hχ35 : χ 35 < 3 := hχk 35 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  have hχ39 : χ 39 < 3 := hχk 39 (by omega) (by omega)
  have hχ40 : χ 40 < 3 := hχk 40 (by omega) (by omega)
  -- ============================================================
  -- STEP 1: χ(24) = χ(16) (C). self-loop m=6 + (20, 19, 24).
  -- ============================================================
  have h24_ne_18 : χ 24 ≠ χ 18 :=
    Ne.symm (bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 6) (by omega) (by omega))
  have h24_ne_12 : χ 24 ≠ χ 12 := by
    intro h24_eq_12
    apply h24_ne_18
    rw [h24_eq_12, ← h18_eq_12]
  have h24_ne_9 : χ 24 ≠ χ 9 := by
    intro h24_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 19
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h19_eq_9]
    · show χ 19 = χ (19 + 5)
      rw [show (19 + 5 : ℕ) = 24 by decide, h19_eq_9, h24_eq_9]
  have h24_eq_16 : χ 24 = χ 16 :=
    third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h24_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- ============================================================
  -- STEP 2: χ(21) = χ(9) (A). (12, 18, 21) + (24, 15, 21).
  -- ============================================================
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 18
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h18_eq_12]
    · show χ 18 = χ (18 + 3)
      rw [show (18 + 3 : ℕ) = 21 by decide, h18_eq_12, h21_eq_12]
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 15
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_16, ← h15_eq_16]
    · show χ 15 = χ (15 + 6)
      rw [show (15 + 6 : ℕ) = 21 by decide, h15_eq_16, h21_eq_16]
  have h21_eq_9 : χ 21 = χ 9 :=
    third_color_eq hχ21 hχ9 hχ12 hχ16 h12_ne_16 h21_ne_12 h21_ne_16 h9_ne_12 h9_ne_16
  -- ============================================================
  -- STEP 3: χ(28) = χ(12) (B). (16, 24, 28) + self-loop m=7.
  -- ============================================================
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 24
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h24_eq_16.symm
    · show χ 24 = χ (24 + 4)
      rw [show (24 + 4 : ℕ) = 28 by decide, h24_eq_16, h28_eq_16]
  have h28_ne_21 : χ 28 ≠ χ 21 :=
    Ne.symm (bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 7) (by omega) (by omega))
  have h28_ne_9 : χ 28 ≠ χ 9 := by
    intro h28_eq_9
    apply h28_ne_21
    rw [h28_eq_9, ← h21_eq_9]
  have h28_eq_12 : χ 28 = χ 12 :=
    third_color_eq hχ28 hχ12 hχ9 hχ16 h9_ne_16 h28_ne_9 h28_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- ============================================================
  -- STEP 4: χ(25) = χ(16) (C). anchor self-rado m=5 (20, 20, 25) + (28, 18, 25).
  -- ============================================================
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 20
      rw [show (4 * 5 : ℕ) = 20 by decide]
    · show χ 20 = χ (20 + 5)
      rw [show (20 + 5 : ℕ) = 25 by decide, h20_eq_9, h25_eq_9]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 18
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_12, ← h18_eq_12]
    · show χ 18 = χ (18 + 7)
      rw [show (18 + 7 : ℕ) = 25 by decide, h18_eq_12, h25_eq_12]
  have h25_eq_16 : χ 25 = χ 16 :=
    third_color_eq hχ25 hχ16 hχ9 hχ12 h9_ne_12 h25_ne_9 h25_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- ============================================================
  -- STEP 5: χ(29) = χ(9) (A). (16, 25, 29) + (4, 28, 29).
  -- ============================================================
  have h29_ne_16 : χ 29 ≠ χ 16 := by
    intro h29_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 25) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 25
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h25_eq_16.symm
    · show χ 25 = χ (25 + 4)
      rw [show (25 + 4 : ℕ) = 29 by decide, h25_eq_16, h29_eq_16]
  have h29_ne_12 : χ 29 ≠ χ 12 := by
    intro h29_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 28
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, ← h28_eq_12]
    · show χ 28 = χ (28 + 1)
      rw [show (28 + 1 : ℕ) = 29 by decide, h28_eq_12, h29_eq_12]
  have h29_eq_9 : χ 29 = χ 9 :=
    third_color_eq hχ29 hχ9 hχ12 hχ16 h12_ne_16 h29_ne_12 h29_ne_16 h9_ne_12 h9_ne_16
  -- ============================================================
  -- STEP 6: χ(30) = χ(9) (A). anchor self-rado m=6 (24, 24, 30) + (8, 28, 30).
  -- ============================================================
  have h30_ne_16 : χ 30 ≠ χ 16 := by
    intro h30_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 24
      rw [show (4 * 6 : ℕ) = 24 by decide]
    · show χ 24 = χ (24 + 6)
      rw [show (24 + 6 : ℕ) = 30 by decide, h24_eq_16, h30_eq_16]
  have h30_ne_12 : χ 30 ≠ χ 12 := by
    intro h30_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 28
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_12, ← h28_eq_12]
    · show χ 28 = χ (28 + 2)
      rw [show (28 + 2 : ℕ) = 30 by decide, h28_eq_12, h30_eq_12]
  have h30_eq_9 : χ 30 = χ 9 :=
    third_color_eq hχ30 hχ9 hχ12 hχ16 h12_ne_16 h30_ne_12 h30_ne_16 h9_ne_12 h9_ne_16
  -- ============================================================
  -- STEP 7: χ(31) = χ(9) (A). (12, 28, 31) + (24, 25, 31).
  -- ============================================================
  have h31_ne_12 : χ 31 ≠ χ 12 := by
    intro h31_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 28
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h28_eq_12.symm
    · show χ 28 = χ (28 + 3)
      rw [show (28 + 3 : ℕ) = 31 by decide, h28_eq_12, h31_eq_12]
  have h31_ne_16 : χ 31 ≠ χ 16 := by
    intro h31_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 25) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 25
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_16, ← h25_eq_16]
    · show χ 25 = χ (25 + 6)
      rw [show (25 + 6 : ℕ) = 31 by decide, h25_eq_16, h31_eq_16]
  have h31_eq_9 : χ 31 = χ 9 :=
    third_color_eq hχ31 hχ9 hχ12 hχ16 h12_ne_16 h31_ne_12 h31_ne_16 h9_ne_12 h9_ne_16
  -- ============================================================
  -- STEP 8: χ(32) = χ(9) (A). self-loop m=8 + **(32, 4, 12) KEY TRIPLE**.
  -- ============================================================
  have h32_ne_24 : χ 32 ≠ χ 24 :=
    Ne.symm (bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega))
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    apply h32_ne_24
    rw [h32_eq_16, ← h24_eq_16]
  -- (32, 4, 12): χ(32) = χ(4) ∧ χ(4) = χ(12). Both auto from h4_eq_12. Mono iff χ(32) = χ(12).
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 1 * 8 - 1 * 8 + 8)
      show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_9 : χ 32 = χ 9 :=
    third_color_eq hχ32 hχ9 hχ12 hχ16 h12_ne_16 h32_ne_12 h32_ne_16 h9_ne_12 h9_ne_16
  -- ============================================================
  -- STEP 9: χ(35) = χ(16) (C). anchor self-rado m=7 (28, 28, 35) + (20, 30, 35).
  -- ============================================================
  have h35_ne_12 : χ 35 ≠ χ 12 := by
    intro h35_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 28
      rw [show (4 * 7 : ℕ) = 28 by decide]
    · show χ 28 = χ (28 + 7)
      rw [show (28 + 7 : ℕ) = 35 by decide, h28_eq_12, h35_eq_12]
  have h35_ne_9 : χ 35 ≠ χ 9 := by
    intro h35_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 30) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 30
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h30_eq_9]
    · show χ 30 = χ (30 + 5)
      rw [show (30 + 5 : ℕ) = 35 by decide, h30_eq_9, h35_eq_9]
  have h35_eq_16 : χ 35 = χ 16 :=
    third_color_eq hχ35 hχ16 hχ9 hχ12 h9_ne_12 h35_ne_9 h35_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- ============================================================
  -- STEP 10: χ(39) = χ(12) (B). (16, 35, 39) + (32, 31, 39).
  -- ============================================================
  have h39_ne_16 : χ 39 ≠ χ 16 := by
    intro h39_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 35) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 35
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h35_eq_16.symm
    · show χ 35 = χ (35 + 4)
      rw [show (35 + 4 : ℕ) = 39 by decide, h35_eq_16, h39_eq_16]
  have h39_ne_9 : χ 39 ≠ χ 9 := by
    intro h39_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 31) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 31
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h31_eq_9]
    · show χ 31 = χ (31 + 8)
      rw [show (31 + 8 : ℕ) = 39 by decide, h31_eq_9, h39_eq_9]
  have h39_eq_12 : χ 39 = χ 12 :=
    third_color_eq hχ39 hχ12 hχ9 hχ16 h9_ne_16 h39_ne_9 h39_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- ============================================================
  -- STEP 11: χ(36) = χ(16) (C). (20, 31, 36) + (12, 36, 39).
  -- ============================================================
  have h36_ne_9 : χ 36 ≠ χ 9 := by
    intro h36_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 31) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 31
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h31_eq_9]
    · show χ 31 = χ (31 + 5)
      rw [show (31 + 5 : ℕ) = 36 by decide, h31_eq_9, h36_eq_9]
  have h36_ne_12 : χ 36 ≠ χ 12 := by
    intro h36_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 36) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 36
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h36_eq_12.symm
    · show χ 36 = χ (36 + 3)
      rw [show (36 + 3 : ℕ) = 39 by decide, h36_eq_12, ← h39_eq_12]
  have h36_eq_16 : χ 36 = χ 16 :=
    third_color_eq hχ36 hχ16 hχ9 hχ12 h9_ne_12 h36_ne_9 h36_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- ============================================================
  -- STEP 12: χ(40) = χ(12) (B). self-loop m=10 + (16, 36, 40).
  -- ============================================================
  have h40_ne_30 : χ 40 ≠ χ 30 :=
    Ne.symm (bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 10) (by omega) (by omega))
  have h40_ne_9 : χ 40 ≠ χ 9 := by
    intro h40_eq_9
    apply h40_ne_30
    rw [h40_eq_9, ← h30_eq_9]
  have h40_ne_16 : χ 40 ≠ χ 16 := by
    intro h40_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 36) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 36
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h36_eq_16.symm
    · show χ 36 = χ (36 + 4)
      rw [show (36 + 4 : ℕ) = 40 by decide, h36_eq_16, h40_eq_16]
  have h40_eq_12 : χ 40 = χ 12 :=
    third_color_eq hχ40 hχ12 hχ9 hχ16 h9_ne_16 h40_ne_9 h40_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- ============================================================
  -- TERMINAL: (4, 39, 40). χ(4) = χ(39) = χ(40) = χ(12). MONO!
  -- ============================================================
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 39) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 1) = χ 39
    rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, ← h39_eq_12]
  · show χ 39 = χ (39 + 1)
    rw [show (39 + 1 : ℕ) = 40 by decide, h39_eq_12, ← h40_eq_12]

/-! ### §100. — residual cell (1), χ(13) = χ(16) branch closure.

  **Strategic context ()**: complete the hLayer d=5 proof for residual
  cell (1) by closing the sibling branch χ(13) = χ(16).

  **MAJOR DISCOVERY**: while used a 12-step high-position cascade for
  Case χ(13) = χ(9), the actual proof needs only **4 steps** and closes
  BOTH branches simultaneously — without any χ(13) hypothesis. was
  over-engineered.

  **§100 cascade structure** (4 steps + 1 terminal mono):

  Setup: A := χ(9), B := χ(12), C := χ(16). Residual cell (1) + /
  prefix gives the forced positions χ(1) = A, χ(4) = B, χ(7) = C, χ(12) = B,
  χ(15) = C (used as cell hypotheses).

  | Step | Position | Forced | Key triple |
  |------|----------|--------|------------|
  | 1 | χ(32) ≠ B | (32, 4, 12) |
  | 2 | χ(32) ≠ C | (32, 7, 15) |
  | 3 | χ(32) = A | third_color_eq |
  | T | **MONO** | **(32, 1, 9): χ(32) = χ(1) = χ(9) = A** |

  Arithmetic verification:
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓ (uses χ(4) = χ(12) = B from residual cell)
  - (32, 7, 15): 32 + 28 = 60 = 4·15 ✓ (uses χ(7) = χ(15) = C from /)
  - **(32, 1, 9): 32 + 4 = 36 = 4·9 ✓ TERMINAL MONO** (uses χ(1) = χ(9) = A from )

  **Significance**: this discovery means:
  - The χ(13) ∈ {χ(9), χ(16)} case split is UNNECESSARY for hLayer d=5
    closure on residual cell (1).
  - closure works but used a much longer chain than necessary.
  - This shorter chain closes at n ≥ 32 (not n ≥ 40).
  - For consistency with the user-requested theorem name and signature,
    the theorem below accepts h13_eq_16 as a hypothesis but does NOT
    use it in the proof.
-/

set_option maxHeartbeats 400000 in
/-- ** χ(13) = χ(16) branch closure**: residual cell (1) + χ(20) = χ(9) +
  / prefix + χ(13) = χ(16) ⟹ False at n ≥ 40.

  Surprisingly, the proof does NOT use the χ(13) = χ(16) hypothesis. The
  4-step cascade (32, 4, 12) + (32, 7, 15) + third_color_eq + (32, 1, 9) closes
  the contradiction directly via χ(32) = χ(1) = χ(9) = A mono. This means
  hLayer d=5 for residual cell (1) closes WITHOUT requiring the χ(13) case
  split that used.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi16_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (_h8_eq_12 : χ 8 = χ 12)
    (_h20_eq_9 : χ 20 = χ 9)
    -- prefix:
    (_h14_eq_16 : χ 14 = χ 16)
    (_h10_eq_9 : χ 10 = χ 9)
    (h15_eq_16 : χ 15 = χ 16)
    (_h11_eq_9 : χ 11 = χ 9)
    -- prefix:
    (_h5_eq_16 : χ 5 = χ 16)
    (_h6_eq_16 : χ 6 = χ 16)
    (_h2_eq_9 : χ 2 = χ 9)
    (h7_eq_16 : χ 7 = χ 16)
    (_h3_eq_9 : χ 3 = χ 9)
    (h1_eq_9 : χ 1 = χ 9)
    -- branch (UNUSED in proof — kept for signature compatibility):
    (_h13_eq_16 : χ 13 = χ 16) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- STEP 1: χ(32) ≠ χ(12). (32, 4, 12) uses χ(4) = χ(12) = B from residual cell.
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  -- STEP 2: χ(32) ≠ χ(16). (32, 7, 15) uses χ(7) = χ(15) = C from /.
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 7
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h7_eq_16]
    · show χ 7 = χ (7 + 8)
      rw [show (7 + 8 : ℕ) = 15 by decide, h7_eq_16, ← h15_eq_16]
  -- STEP 3: χ(32) = χ(9) by third_color_eq.
  have h32_eq_9 : χ 32 = χ 9 :=
    third_color_eq hχ32 hχ9 hχ12 hχ16 h12_ne_16 h32_ne_12 h32_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (32, 1, 9). χ(32) = χ(1) = χ(9) = A. MONO!
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 1) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 1
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h1_eq_9]
  · show χ 1 = χ (1 + 8)
    rw [show (1 + 8 : ℕ) = 9 by decide]; exact h1_eq_9

/-! ### §101. — hLayer d=5 extraction for residual cell (1).

  **Strategic context ()**: extract the actual hLayer d=5 fact from
   + + 's discovery. Three theorems:

  1. `…_forces_False_short` — composes + internally + inlines
     's 4-step cascade. No χ(13) hypothesis. Closes at n ≥ 32.
  2. `…_chi20_ne_chi9` — contrapositive: χ(20) ≠ χ(9) under cell (1).
  3. `…_layer_compression_d5` — trichotomy form: χ(20) = χ(12) ∨ χ(20) = χ(16).

  **Feeds bridge directly**: the third theorem above is exactly the
  d=5 case of the hLayer hypothesis for residual cell (1).

  ** is now subsumed by `…_forces_False_short`**: the 12-step cascade
  was unnecessary; the actual minimal cascade is 4 steps via (32, 4, 12),
  (32, 7, 15), and (32, 1, 9) terminal mono.
-/

set_option maxHeartbeats 400000 in
/-- ** short closure** (Type B latent pattern): residual cell (1) +
  χ(20) = χ(9) ⟹ False at n ≥ 32. No χ(13) hypothesis required.

  Composes + internally to derive the forced-color prefix, then
  applies the 4-step cascade: (32, 4, 12) + (32, 7, 15) + third_color_eq
  + (32, 1, 9) terminal mono.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9) :
    False := by
  -- Compose prefix.
  obtain ⟨h14_eq_16, h10_eq_9, h15_eq_16, h11_eq_9⟩ :=
    residual_cell_1_chi20_eq_chi9_forces_chi14_10_15_11 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h20_eq_9
  -- Compose prefix.
  obtain ⟨_h5_eq_16, _h6_eq_16, _h2_eq_9, h7_eq_16, _h3_eq_9, h1_eq_9⟩ :=
    residual_cell_1_chi20_eq_chi9_forces_chi5_6_2_7_3_1 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h20_eq_9
      h14_eq_16 h10_eq_9 h15_eq_16 h11_eq_9
  -- Inline 's 4-step cascade.
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- STEP 1: χ(32) ≠ χ(12) via (32, 4, 12).
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  -- STEP 2: χ(32) ≠ χ(16) via (32, 7, 15).
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 7
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h7_eq_16]
    · show χ 7 = χ (7 + 8)
      rw [show (7 + 8 : ℕ) = 15 by decide, h7_eq_16, ← h15_eq_16]
  -- STEP 3: χ(32) = χ(9).
  have h32_eq_9 : χ 32 = χ 9 :=
    third_color_eq hχ32 hχ9 hχ12 hχ16 h12_ne_16 h32_ne_12 h32_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (32, 1, 9) — χ(32) = χ(1) = χ(9) = A.
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 1) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 1
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h1_eq_9]
  · show χ 1 = χ (1 + 8)
    rw [show (1 + 8 : ℕ) = 9 by decide]; exact h1_eq_9

/-- ** contrapositive hLayer d=5 fact**: under residual cell (1)
  hypotheses, χ(20) ≠ χ(9). Immediate from the short closure.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_chi20_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 20 ≠ χ 9 := by
  intro h20_eq_9
  exact residual_cell_1_chi20_eq_chi9_forces_False_short χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h20_eq_9

/-- ** layer-compression d=5 fact**: under residual cell (1) hypotheses,
  χ(20) ∈ {χ(12), χ(16)}. This is the d=5 case of the hLayer hypothesis
  for the scale-by-4 bridge.

  Proof: χ(20) ≠ χ(9) (above) + by_cases on χ(20) = χ(12) + third_color_eq.

  **Kernel-pure**: only Lean kernel axioms. -/
theorem residual_cell_1_layer_compression_d5
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 20 = χ 12 ∨ χ 20 = χ 16 := by
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  by_cases h_eq_12 : χ 20 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ20 hχ16 hχ9 hχ12 h9_ne_12 h20_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §102. — hLayer d=6 extraction for residual cell (1).

  **Strategic context ()**: extend the layer-compression chain from d=5
  () to d=6. Under cell (1) hypotheses, prove χ(24) = χ(12) ∨ χ(24) = χ(16).

  **§102 cascade structure** (6-step closure, n ≥ 24):

  Setup: A := χ(9), B := χ(12), C := χ(16), all distinct. Assume χ(24) = A
  for contradiction.

  | Step | Position | Forced | Key triple(s) |
  |------|----------|--------|---------------|
  | 1 | χ(15) = C | (24, 9, 15) + (12, 12, 15) |
  | 2 | χ(11) = A | (16, 11, 15) + (12, 8, 11) |
  | 3 | χ(5) = C | (24, 5, 11) + (4, 4, 5) |
  | 4 | χ(1) = A | (16, 1, 5) + (12, 1, 4) |
  | 5 | χ(7) = C | (24, 1, 7) + (4, 7, 8) |
  | 6 | **χ(3) excluded from {A, B, C}** | (24, 3, 9) + (4, 3, 4) + (16, 3, 7) → third_color_eq → χ(3) = χ(16) ≠ χ(3). ⊥ |

  All triples in the proof have x + 4y = 4z arithmetic:
  - (24, 9, 15): 24 + 36 = 60 = 4·15 ✓
  - (12, 12, 15): 12 + 48 = 60 ✓
  - (16, 11, 15): 16 + 44 = 60 ✓
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓
  - (24, 5, 11): 24 + 20 = 44 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (16, 1, 5): 16 + 4 = 20 ✓
  - (12, 1, 4): 12 + 4 = 16 = 4·4 ✓
  - (24, 1, 7): 24 + 4 = 28 = 4·7 ✓
  - (4, 7, 8): 4 + 28 = 32 = 4·8 ✓
  - (24, 3, 9): 24 + 12 = 36 = 4·9 ✓
  - (4, 3, 4): 4 + 12 = 16 ✓
  - (16, 3, 7): 16 + 12 = 28 ✓

  **Type B latent pattern**: this cascade is structurally similar to +
  (which derived a prefix of forced colors and then closed). closes at
  n ≥ 24 via the χ(3) "no-color-left" contradiction. The cascade does NOT
  require (chi(20) value) — only cell (1) hypotheses + chi(24) = chi(9).

  Three composed theorems (analogous to ):
  1. `..._chi24_eq_chi9_forces_False_short` — direct contradiction, n ≥ 24.
  2. `..._chi24_ne_chi9` — contrapositive.
  3. `..._layer_compression_d6` — trichotomy form, feeds.
-/

set_option maxHeartbeats 400000 in
/-- ** chi(24) = chi(9) closure**: residual cell (1) + χ(24) = χ(9) ⟹ False
  at n ≥ 24. 6-step cascade ending in χ(3) excluded from all 3 colors. -/
theorem residual_cell_1_chi24_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h24_eq_9 : χ 24 = χ 9) :
    False := by
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- STEP 1: χ(15) = χ(16) (C). (12, 12, 15) + (24, 9, 15).
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 9
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_9
    · show χ 9 = χ (9 + 6)
      rw [show (9 + 6 : ℕ) = 15 by decide, h15_eq_9]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 2: χ(11) = χ(9) (A). (16, 11, 15) + (12, 8, 11).
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- STEP 3: χ(5) = χ(16) (C). (24, 5, 11) + (4, 4, 5).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 5
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 6)
      rw [show (5 + 6 : ℕ) = 11 by decide, h5_eq_9, ← h11_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 4: χ(1) = χ(9) (A). (16, 1, 5) + (12, 1, 4).
  have h1_ne_16 : χ 1 ≠ χ 16 := by
    intro h1_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 1
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h1_eq_16.symm
    · show χ 1 = χ (1 + 4)
      rw [show (1 + 4 : ℕ) = 5 by decide, h1_eq_16, ← h5_eq_16]
  have h1_ne_12 : χ 1 ≠ χ 12 := by
    intro h1_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 1
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h1_eq_12.symm
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_12, h1_eq_12]
  have h1_eq_9 : χ 1 = χ 9 :=
    third_color_eq hχ1 hχ9 hχ12 hχ16 h12_ne_16 h1_ne_12 h1_ne_16 h9_ne_12 h9_ne_16
  -- STEP 5: χ(7) = χ(16) (C). (24, 1, 7) + (4, 7, 8).
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 1
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h1_eq_9]
    · show χ 1 = χ (1 + 6)
      rw [show (1 + 6 : ℕ) = 7 by decide, h1_eq_9, h7_eq_9]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 7
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h7_eq_12]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h7_eq_12, ← h8_eq_12]
  have h7_eq_16 : χ 7 = χ 16 :=
    third_color_eq hχ7 hχ16 hχ9 hχ12 h9_ne_12 h7_ne_9 h7_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 6: χ(3) excluded from {A, B, C} → third_color_eq contradiction.
  have h3_ne_9 : χ 3 ≠ χ 9 := by
    intro h3_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 3
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h3_eq_9]
    · show χ 3 = χ (3 + 6)
      rw [show (3 + 6 : ℕ) = 9 by decide]; exact h3_eq_9
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h3_eq_12]
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h4_eq_12, h3_eq_12]
  have h3_ne_16 : χ 3 ≠ χ 16 := by
    intro h3_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 3
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h3_eq_16.symm
    · show χ 3 = χ (3 + 4)
      rw [show (3 + 4 : ℕ) = 7 by decide, h3_eq_16, ← h7_eq_16]
  -- third_color_eq: χ(3) ≠ χ(9), χ(3) ≠ χ(12) ⟹ χ(3) = χ(16). Contradicts h3_ne_16.
  have h3_eq_16 : χ 3 = χ 16 :=
    third_color_eq hχ3 hχ16 hχ9 hχ12 h9_ne_12 h3_ne_9 h3_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h3_ne_16 h3_eq_16

/-- ** contrapositive**: χ(24) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi24_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 24 ≠ χ 9 := by
  intro h24_eq_9
  exact residual_cell_1_chi24_eq_chi9_forces_False_short χ h24 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h24_eq_9

/-- ** layer compression d=6**: χ(24) ∈ {χ(12), χ(16)} under cell (1).
  This is the d=6 case of the hLayer hypothesis for the bridge. -/
theorem residual_cell_1_layer_compression_d6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 24 = χ 12 ∨ χ 24 = χ 16 := by
  have h24_ne_9 : χ 24 ≠ χ 9 :=
    residual_cell_1_chi24_ne_chi9 χ h24 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  by_cases h_eq_12 : χ 24 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §103. — hLayer d=7 extraction for residual cell (1).

  **Strategic context ()**: extend the layer-compression chain from d=6
  () to d=7. Under cell (1) hypotheses + (chi(20) = B), prove
  χ(28) = χ(12) ∨ χ(28) = χ(16).

  **§103 cascade structure** (7 forced positions + 1 terminal mono, n ≥ 32):

  Setup: A := χ(9), B := χ(12), C := χ(16). Assume χ(28) = A for contradiction.

  | Step | Position | Forced | Key triple(s) |
  |------|----------|--------|---------------|
  | 0 | χ(20) = B | (chi(20) ≠ A) + (16, 16, 20) (chi(20) ≠ C) |
  | 1 | χ(2) = C | (8, 2, 4) + (28, 2, 9) |
  | 2 | χ(6) = A | (8, 6, 8) self-loop + (16, 2, 6) |
  | 3 | χ(13) = C | (4, 12, 13) + (28, 6, 13) |
  | 4 | χ(17) = A | (16, 13, 17) + (20, 12, 17) |
  | 5 | χ(10) = C | (8, 8, 10) + (28, 10, 17) |
  | 6 | χ(32) = A | (32, 4, 12) + (32, 2, 10) |
  | T | **MONO** | **(32, 9, 17): χ(32) = χ(9) = χ(17) = A** |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (8, 2, 4): 8 + 8 = 16 = 4·4 ✓
  - (28, 2, 9): 28 + 8 = 36 = 4·9 ✓
  - (8, 6, 8) self-loop b=4 m=2
  - (16, 2, 6): 16 + 8 = 24 = 4·6 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (28, 6, 13): 28 + 24 = 52 ✓
  - (16, 13, 17): 16 + 52 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (28, 10, 17): 28 + 40 = 68 = 4·17 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (32, 2, 10): 32 + 8 = 40 = 4·10 ✓
  - **(32, 9, 17): 32 + 36 = 68 = 4·17 ✓** TERMINAL MONO

  **Closes at n ≥ 32** via terminal mono (32, 9, 17). Calls internally.
-/

set_option maxHeartbeats 400000 in
/-- ** chi(28) = chi(9) closure**: residual cell (1) + χ(28) = χ(9) ⟹
  False at n ≥ 32. 7-step cascade ending in mono (32, 9, 17). Calls 
  to get chi(20) = chi(12). -/
theorem residual_cell_1_chi28_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h28_eq_9 : χ 28 = χ 9) :
    False := by
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- STEP 0: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- STEP 1: χ(2) = χ(16). (8, 2, 4) + (28, 2, 9).
  have h2_ne_12 : χ 2 ≠ χ 12 := by
    intro h2_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 2
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_12, h2_eq_12]
    · show χ 2 = χ (2 + 2)
      rw [show (2 + 2 : ℕ) = 4 by decide, h4_eq_12, h2_eq_12]
  have h2_ne_9 : χ 2 ≠ χ 9 := by
    intro h2_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 2
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h2_eq_9]
    · show χ 2 = χ (2 + 7)
      rw [show (2 + 7 : ℕ) = 9 by decide]; exact h2_eq_9
  have h2_eq_16 : χ 2 = χ 16 :=
    third_color_eq hχ2 hχ16 hχ9 hχ12 h9_ne_12 h2_ne_9 h2_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 2: χ(6) = χ(9). (8, 6, 8) + (16, 2, 6).
  have h6_ne_8 : χ 6 ≠ χ 8 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 2) (by omega) (by omega)
  have h6_ne_12 : χ 6 ≠ χ 12 := by
    intro h6_eq_12
    apply h6_ne_8
    rw [h6_eq_12, ← h8_eq_12]
  have h6_ne_16 : χ 6 ≠ χ 16 := by
    intro h6_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 2
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h2_eq_16.symm
    · show χ 2 = χ (2 + 4)
      rw [show (2 + 4 : ℕ) = 6 by decide, h2_eq_16, h6_eq_16]
  have h6_eq_9 : χ 6 = χ 9 :=
    third_color_eq hχ6 hχ9 hχ12 hχ16 h12_ne_16 h6_ne_12 h6_ne_16 h9_ne_12 h9_ne_16
  -- STEP 3: χ(13) = χ(16). (4, 12, 13) + (28, 6, 13).
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 6
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h6_eq_9]
    · show χ 6 = χ (6 + 7)
      rw [show (6 + 7 : ℕ) = 13 by decide, h6_eq_9, h13_eq_9]
  have h13_eq_16 : χ 13 = χ 16 :=
    third_color_eq hχ13 hχ16 hχ9 hχ12 h9_ne_12 h13_ne_9 h13_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 4: χ(17) = χ(9). (16, 13, 17) + (20, 12, 17).
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 13
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, h17_eq_16]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
  -- STEP 5: χ(10) = χ(16). (8, 8, 10) + (28, 10, 17).
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 10
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h10_eq_9]
    · show χ 10 = χ (10 + 7)
      rw [show (10 + 7 : ℕ) = 17 by decide, h10_eq_9, ← h17_eq_9]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- STEP 6: χ(32) = χ(9). (32, 4, 12) + (32, 2, 10).
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 2
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h2_eq_16]
    · show χ 2 = χ (2 + 8)
      rw [show (2 + 8 : ℕ) = 10 by decide, h2_eq_16, ← h10_eq_16]
  have h32_eq_9 : χ 32 = χ 9 :=
    third_color_eq hχ32 hχ9 hχ12 hχ16 h12_ne_16 h32_ne_12 h32_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (32, 9, 17). χ(32) = χ(9) = χ(17) = A. MONO!
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 9
    rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
  · show χ 9 = χ (9 + 8)
    rw [show (9 + 8 : ℕ) = 17 by decide]; exact h17_eq_9.symm

/-- ** contrapositive**: χ(28) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi28_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 28 ≠ χ 9 := by
  intro h28_eq_9
  exact residual_cell_1_chi28_eq_chi9_forces_False_short χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h28_eq_9

/-- ** layer compression d=7**: χ(28) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=7 hLayer case. -/
theorem residual_cell_1_layer_compression_d7
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 28 = χ 12 ∨ χ 28 = χ 16 := by
  have h28_ne_9 : χ 28 ≠ χ 9 :=
    residual_cell_1_chi28_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  by_cases h_eq_12 : χ 28 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ28 hχ16 hχ9 hχ12 h9_ne_12 h28_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §104. — hLayer d=8 extraction for residual cell (1).

  **Strategic context ()**: extend the layer-compression chain to d=8.
  Under cell (1) hypotheses + (chi(20) = B), prove
  χ(32) = χ(12) ∨ χ(32) = χ(16).

  **§104 cascade structure** (case split on χ(13), each case closes via
  terminal mono):

  Setup: A := χ(9), B := χ(12), C := χ(16). Assume χ(32) = A for contradiction.

  Preamble:
  - Step 0: χ(20) = χ(12) via + (16, 16, 20).
  - chi(13) ≠ chi(12) from (4, 12, 13) [general].

  Case A: χ(13) = χ(16) (= C).
  | Step | Position | Triple |
  |------|----------|--------|
  | A1 | χ(17) ≠ χ(12) | (20, 12, 17) |
  | A2 | χ(17) ≠ χ(16) | (16, 13, 17) (uses chi(13) = chi(16)) |
  | A3 | χ(17) = χ(9) | third_color_eq |
  | AT | **MONO** | **(32, 9, 17): chi(32) = chi(9) = chi(17) = A** |

  Case B: χ(13) ≠ χ(16). chi(13) ≠ chi(12) (general). third_color_eq → chi(13) = chi(9).
  | Step | Position | Triple |
  |------|----------|--------|
  | B1 | χ(13) = χ(9) | third_color_eq |
  | B2 | χ(5) ≠ χ(9) | (32, 5, 13) (uses chi(32) = chi(13) = chi(9)) |
  | B3 | χ(5) ≠ χ(12) | (4, 4, 5) [general] |
  | B4 | χ(5) = χ(16) | third_color_eq |
  | B5 | χ(1) ≠ χ(16) | (16, 1, 5) (uses chi(5) = chi(16)) |
  | B6 | χ(1) ≠ χ(12) | (12, 1, 4) [general] |
  | B7 | χ(1) = χ(9) | third_color_eq |
  | BT | **MONO** | **(32, 1, 9): chi(32) = chi(1) = chi(9) = A** |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (20, 12, 17): 20 + 48 = 68 = 4·17 ✓
  - (16, 13, 17): 16 + 52 = 68 ✓
  - **(32, 9, 17): 32 + 36 = 68 ✓ — Case A TERMINAL**
  - (32, 5, 13): 32 + 20 = 52 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (16, 1, 5): 16 + 4 = 20 ✓
  - (12, 1, 4): 12 + 4 = 16 = 4·4 ✓
  - **(32, 1, 9): 32 + 4 = 36 = 4·9 ✓ — Case B TERMINAL**

  **Closes at n ≥ 32** via two distinct terminal mono triples depending on χ(13).
-/

set_option maxHeartbeats 400000 in
/-- ** chi(32) = chi(9) closure**: residual cell (1) + χ(32) = χ(9) ⟹
  False at n ≥ 32. Case split on χ(13):
  - Case χ(13) = χ(16): mono via (32, 9, 17).
  - Case χ(13) ≠ χ(16): cascade to mono via (32, 1, 9).
  Calls internally for chi(20) = chi(12). -/
theorem residual_cell_1_chi32_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h32_eq_9 : χ 32 = χ 9) :
    False := by
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  -- PREAMBLE STEP 0: chi(20) = chi(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- chi(13) ≠ chi(12) general from (4, 12, 13).
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  -- CASE SPLIT on χ(13) = χ(16).
  by_cases h13_eq_16 : χ 13 = χ 16
  · -- CASE A: chi(13) = chi(16). Force chi(17) = chi(9), then mono (32, 9, 17).
    have h17_ne_12 : χ 17 ≠ χ 12 := by
      intro h17_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 12
        rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
      · show χ 12 = χ (12 + 5)
        rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
    have h17_ne_16 : χ 17 ≠ χ 16 := by
      intro h17_eq_16
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 13
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
      · show χ 13 = χ (13 + 4)
        rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, h17_eq_16]
    have h17_eq_9 : χ 17 = χ 9 :=
      third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
    -- CASE A TERMINAL: (32, 9, 17). chi(32) = chi(9), chi(17) = chi(9). MONO.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 9
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
    · show χ 9 = χ (9 + 8)
      rw [show (9 + 8 : ℕ) = 17 by decide]; exact h17_eq_9.symm
  · -- CASE B: chi(13) ≠ chi(16). Force chi(1) = chi(9), then mono (32, 1, 9).
    -- B1: chi(13) = chi(9).
    have h13_eq_9 : χ 13 = χ 9 :=
      third_color_eq hχ13 hχ9 hχ12 hχ16 h12_ne_16 h13_ne_12 h13_eq_16 h9_ne_12 h9_ne_16
    -- B2: chi(5) ≠ chi(9). (32, 5, 13).
    have h5_ne_9 : χ 5 ≠ χ 9 := by
      intro h5_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 5
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h5_eq_9]
      · show χ 5 = χ (5 + 8)
        rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_9, ← h13_eq_9]
    -- B3: chi(5) ≠ chi(12). (4, 4, 5).
    have h5_ne_12 : χ 5 ≠ χ 12 := by
      intro h5_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 1) = χ 4
        rw [show (4 * 1 : ℕ) = 4 by decide]
      · show χ 4 = χ (4 + 1)
        rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
    -- B4: chi(5) = chi(16).
    have h5_eq_16 : χ 5 = χ 16 :=
      third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
    -- B5: chi(1) ≠ chi(16). (16, 1, 5).
    have h1_ne_16 : χ 1 ≠ χ 16 := by
      intro h1_eq_16
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 1
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h1_eq_16.symm
      · show χ 1 = χ (1 + 4)
        rw [show (1 + 4 : ℕ) = 5 by decide, h1_eq_16, ← h5_eq_16]
    -- B6: chi(1) ≠ chi(12). (12, 1, 4).
    have h1_ne_12 : χ 1 ≠ χ 12 := by
      intro h1_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 3) = χ 1
        rw [show (4 * 3 : ℕ) = 12 by decide]; exact h1_eq_12.symm
      · show χ 1 = χ (1 + 3)
        rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_12, h1_eq_12]
    -- B7: chi(1) = chi(9).
    have h1_eq_9 : χ 1 = χ 9 :=
      third_color_eq hχ1 hχ9 hχ12 hχ16 h12_ne_16 h1_ne_12 h1_ne_16 h9_ne_12 h9_ne_16
    -- CASE B TERMINAL: (32, 1, 9). chi(32) = chi(9), chi(1) = chi(9). MONO.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 1
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h1_eq_9]
    · show χ 1 = χ (1 + 8)
      rw [show (1 + 8 : ℕ) = 9 by decide]; exact h1_eq_9

/-- ** contrapositive**: χ(32) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi32_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 32 ≠ χ 9 := by
  intro h32_eq_9
  exact residual_cell_1_chi32_eq_chi9_forces_False_short χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h32_eq_9

/-- ** layer compression d=8**: χ(32) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=8 hLayer case. -/
theorem residual_cell_1_layer_compression_d8
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 32 = χ 12 ∨ χ 32 = χ 16 := by
  have h32_ne_9 : χ 32 ≠ χ 9 :=
    residual_cell_1_chi32_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  by_cases h_eq_12 : χ 32 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ32 hχ16 hχ9 hχ12 h9_ne_12 h32_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §105. — hLayer d=9 extraction for residual cell (1).

  **Strategic context ()**: extend the layer-compression chain to d=9.

  **Key insight**: under cell (1) hypotheses + (chi(24) ∈ {B, C}) +
   (chi(32) ∈ {B, C}), both chi(24) and chi(32) are FORCED to specific
  values WITHOUT additional case split:
    - chi(32) ≠ B from (32, 4, 12) + → chi(32) = C.
    - chi(24) ≠ C from self-loop m=8 (chi(24) ≠ chi(32) = C) + → chi(24) = B.

  This unlocks a no-case-split 9-step cascade under chi(36) = A, terminating
  in mono (32, 2, 10) with chi(32) = chi(2) = chi(10) = C.

  **§105 cascade structure** (3 preamble + 9 main + 1 terminal mono):

  Preamble:
  - P1: chi(20) = chi(12). + (16, 16, 20).
  - P2: chi(32) = chi(16). + (32, 4, 12).
  - P3: chi(24) = chi(12). + self-loop m=8.

  Main cascade (forced under chi(36) = A and preamble):
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | chi(18) = C | self-loop m=6 + (36, 9, 18) |
  | 2 | chi(14) = A | (16, 14, 18) + (8, 12, 14) |
  | 3 | chi(5) = C | (36, 5, 14) + (4, 4, 5) |
  | 4 | chi(1) = A | (16, 1, 5) + (12, 1, 4) |
  | 5 | chi(10) = C | (36, 1, 10) + (8, 8, 10) |
  | 6 | chi(6) = A | (16, 6, 10) + (8, 6, 8) self-loop |
  | 7 | chi(15) = C | (36, 6, 15) + (12, 12, 15) |
  | 8 | chi(11) = A | (16, 11, 15) + (12, 8, 11) |
  | 9 | chi(2) = C | (36, 2, 11) + (8, 2, 4) |
  | T | **MONO** | **(32, 2, 10): chi(32) = chi(2) = chi(10) = C** |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - self-loop m=8: chi(24) ≠ chi(32)
  - self-loop m=6: chi(18) ≠ chi(24)
  - (36, 9, 18): 36 + 36 = 72 = 4·18 ✓
  - (16, 14, 18): 16 + 56 = 72 ✓
  - (8, 12, 14): 8 + 48 = 56 = 4·14 ✓
  - (36, 5, 14): 36 + 20 = 56 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (16, 1, 5): 16 + 4 = 20 ✓
  - (12, 1, 4): 12 + 4 = 16 = 4·4 ✓
  - (36, 1, 10): 36 + 4 = 40 = 4·10 ✓
  - (8, 8, 10): 8 + 32 = 40 ✓
  - (16, 6, 10): 16 + 24 = 40 ✓
  - self-loop m=2: chi(6) ≠ chi(8)
  - (36, 6, 15): 36 + 24 = 60 = 4·15 ✓
  - (12, 12, 15): 12 + 48 = 60 ✓
  - (16, 11, 15): 16 + 44 = 60 ✓
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓
  - (36, 2, 11): 36 + 8 = 44 ✓
  - (8, 2, 4): 8 + 8 = 16 = 4·4 ✓
  - **(32, 2, 10): 32 + 8 = 40 = 4·10 ✓** TERMINAL MONO
-/

set_option maxHeartbeats 800000 in
/-- ** chi(36) = chi(9) closure**: residual cell (1) + χ(36) = χ(9) ⟹
  False at n ≥ 36. 9-step cascade ending in mono (32, 2, 10). Calls,
, internally for preamble. NO case split needed. -/
theorem residual_cell_1_chi36_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h36_eq_9 : χ 36 = χ 9) :
    False := by
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  -- PREAMBLE P1: chi(20) = chi(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: chi(32) = chi(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: chi(24) = chi(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_32 : χ 24 ≠ χ 32 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    apply h24_ne_32
    rw [h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- MAIN CASCADE.
  -- S1: chi(18) = chi(16). self-loop m=6 + (36, 9, 18).
  have h18_ne_24 : χ 18 ≠ χ 24 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 6) (by omega) (by omega)
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    apply h18_ne_24
    rw [h18_eq_12, ← h24_eq_12]
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 9
      rw [show (4 * 9 : ℕ) = 36 by decide]; exact h36_eq_9
    · show χ 9 = χ (9 + 9)
      rw [show (9 + 9 : ℕ) = 18 by decide, h18_eq_9]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: chi(14) = chi(9). (16, 14, 18) + (8, 12, 14).
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 14
      rw [show (4 * 4 : ℕ) = 16 by decide, h14_eq_16]
    · show χ 14 = χ (14 + 4)
      rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, ← h18_eq_16]
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ12 hχ16 h12_ne_16 h14_ne_12 h14_ne_16 h9_ne_12 h9_ne_16
  -- S3: chi(5) = chi(16). (36, 5, 14) + (4, 4, 5).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 5
      rw [show (4 * 9 : ℕ) = 36 by decide, h36_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 9)
      rw [show (5 + 9 : ℕ) = 14 by decide, h5_eq_9, ← h14_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: chi(1) = chi(9). (16, 1, 5) + (12, 1, 4).
  have h1_ne_16 : χ 1 ≠ χ 16 := by
    intro h1_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 1
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h1_eq_16.symm
    · show χ 1 = χ (1 + 4)
      rw [show (1 + 4 : ℕ) = 5 by decide, h1_eq_16, ← h5_eq_16]
  have h1_ne_12 : χ 1 ≠ χ 12 := by
    intro h1_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 1
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h1_eq_12.symm
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_12, h1_eq_12]
  have h1_eq_9 : χ 1 = χ 9 :=
    third_color_eq hχ1 hχ9 hχ12 hχ16 h12_ne_16 h1_ne_12 h1_ne_16 h9_ne_12 h9_ne_16
  -- S5: chi(10) = chi(16). (36, 1, 10) + (8, 8, 10).
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 1
      rw [show (4 * 9 : ℕ) = 36 by decide, h36_eq_9, ← h1_eq_9]
    · show χ 1 = χ (1 + 9)
      rw [show (1 + 9 : ℕ) = 10 by decide, h1_eq_9, h10_eq_9]
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S6: chi(6) = chi(9). (16, 6, 10) + (8, 6, 8) self-loop.
  have h6_ne_16 : χ 6 ≠ χ 16 := by
    intro h6_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 6
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h6_eq_16.symm
    · show χ 6 = χ (6 + 4)
      rw [show (6 + 4 : ℕ) = 10 by decide, h6_eq_16, ← h10_eq_16]
  have h6_ne_8 : χ 6 ≠ χ 8 :=
    bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 2) (by omega) (by omega)
  have h6_ne_12 : χ 6 ≠ χ 12 := by
    intro h6_eq_12
    apply h6_ne_8
    rw [h6_eq_12, ← h8_eq_12]
  have h6_eq_9 : χ 6 = χ 9 :=
    third_color_eq hχ6 hχ9 hχ12 hχ16 h12_ne_16 h6_ne_12 h6_ne_16 h9_ne_12 h9_ne_16
  -- S7: chi(15) = chi(16). (36, 6, 15) + (12, 12, 15).
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 6
      rw [show (4 * 9 : ℕ) = 36 by decide, h36_eq_9, ← h6_eq_9]
    · show χ 6 = χ (6 + 9)
      rw [show (6 + 9 : ℕ) = 15 by decide, h6_eq_9, h15_eq_9]
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S8: chi(11) = chi(9). (16, 11, 15) + (12, 8, 11).
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S9: chi(2) = chi(16). (36, 2, 11) + (8, 2, 4).
  have h2_ne_9 : χ 2 ≠ χ 9 := by
    intro h2_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 2
      rw [show (4 * 9 : ℕ) = 36 by decide, h36_eq_9, ← h2_eq_9]
    · show χ 2 = χ (2 + 9)
      rw [show (2 + 9 : ℕ) = 11 by decide, h2_eq_9, ← h11_eq_9]
  have h2_ne_12 : χ 2 ≠ χ 12 := by
    intro h2_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 2
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_12, h2_eq_12]
    · show χ 2 = χ (2 + 2)
      rw [show (2 + 2 : ℕ) = 4 by decide, h4_eq_12, h2_eq_12]
  have h2_eq_16 : χ 2 = χ 16 :=
    third_color_eq hχ2 hχ16 hχ9 hχ12 h9_ne_12 h2_ne_9 h2_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (32, 2, 10). chi(32) = chi(2) = chi(10) = chi(16). MONO!
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 2) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 2
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h2_eq_16]
  · show χ 2 = χ (2 + 8)
    rw [show (2 + 8 : ℕ) = 10 by decide, h2_eq_16, ← h10_eq_16]

/-- ** contrapositive**: χ(36) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi36_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 36 ≠ χ 9 := by
  intro h36_eq_9
  exact residual_cell_1_chi36_eq_chi9_forces_False_short χ h36 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h36_eq_9

/-- ** layer compression d=9**: χ(36) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=9 hLayer case. -/
theorem residual_cell_1_layer_compression_d9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 36 = χ 12 ∨ χ 36 = χ 16 := by
  have h36_ne_9 : χ 36 ≠ χ 9 :=
    residual_cell_1_chi36_ne_chi9 χ h36 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  by_cases h_eq_12 : χ 36 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ36 hχ16 hχ9 hχ12 h9_ne_12 h36_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §106. — hLayer d=10 extraction for residual cell (1).

  **Strategic context ()**: extend chain to d=10 (anchor χ(40)).

  **Sharpened preamble**: under cell (1) + //:
  - χ(20) = χ(12) (B) via + (16, 16, 20).
  - χ(32) = χ(16) (C) via + (32, 4, 12).
  - χ(28) = χ(12) (B) via + (16, 28, 32) — uses sharpened χ(32).

  **§106 cascade structure** (8 forced + 1 no-color-left terminal, n ≥ 40):

  Under χ(40) = A and sharpened preamble (no case split):

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(19) = C | (28, 12, 19) + (40, 9, 19) |
  | 2 | χ(15) = A | (16, 15, 19) + (12, 12, 15) |
  | 3 | χ(5) = C | (40, 5, 15) + (4, 4, 5) |
  | 4 | χ(1) = A | (16, 1, 5) + (12, 1, 4) |
  | 5 | χ(11) = C | (40, 1, 11) + (12, 8, 11) |
  | 6 | χ(7) = A | (16, 7, 11) + (4, 7, 8) |
  | 7 | χ(17) = C | (40, 7, 17) + (20, 12, 17) |
  | 8 | χ(13) = A | (16, 13, 17) + (4, 12, 13) |
  | T | **χ(23) ∉ {A, B, C}** | (40, 13, 23) + (12, 20, 23) + (16, 19, 23) |

  Terminal contradiction via third_color_eq: χ(23) ≠ χ(9), χ(23) ≠ χ(12)
  forces χ(23) = χ(16), but χ(23) ≠ χ(16). ⊥

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 80 = 4·20 ✓
  - (32, 4, 12): 48 = 4·12 ✓
  - (16, 28, 32): 128 = 4·32 ✓
  - (28, 12, 19): 76 = 4·19 ✓
  - (40, 9, 19): 76 ✓
  - (16, 15, 19): 76 ✓
  - (12, 12, 15): 60 = 4·15 ✓
  - (40, 5, 15): 60 ✓
  - (4, 4, 5): 20 = 4·5 ✓
  - (16, 1, 5): 20 ✓
  - (12, 1, 4): 16 = 4·4 ✓
  - (40, 1, 11): 44 = 4·11 ✓
  - (12, 8, 11): 44 ✓
  - (16, 7, 11): 44 ✓
  - (4, 7, 8): 32 = 4·8 ✓
  - (40, 7, 17): 68 = 4·17 ✓
  - (20, 12, 17): 68 ✓
  - (16, 13, 17): 68 ✓
  - (4, 12, 13): 52 = 4·13 ✓
  - (40, 13, 23): 92 = 4·23 ✓
  - (12, 20, 23): 92 ✓
  - (16, 19, 23): 92 ✓
-/

set_option maxHeartbeats 800000 in
/-- ** chi(40) = chi(9) closure**: residual cell (1) + χ(40) = χ(9) ⟹
  False at n ≥ 40. 8-step cascade ending in no-color-left contradiction on
  χ(23). Calls,, internally for sharpened preamble. -/
theorem residual_cell_1_chi40_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h40_eq_9 : χ 40 = χ 9) :
    False := by
  have hχ1 : χ 1 < 3 := hχk 1 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(28) = χ(12). + (16, 28, 32).
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 28
      rw [show (4 * 4 : ℕ) = 16 by decide, h28_eq_16]
    · show χ 28 = χ (28 + 4)
      rw [show (28 + 4 : ℕ) = 32 by decide, h28_eq_16, ← h32_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- MAIN CASCADE.
  -- S1: χ(19) = χ(16) (C).
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 12
      rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_12
    · show χ 12 = χ (12 + 7)
      rw [show (12 + 7 : ℕ) = 19 by decide, h19_eq_12]
  have h19_ne_9 : χ 19 ≠ χ 9 := by
    intro h19_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 9
      rw [show (4 * 10 : ℕ) = 40 by decide]; exact h40_eq_9
    · show χ 9 = χ (9 + 10)
      rw [show (9 + 10 : ℕ) = 19 by decide, h19_eq_9]
  have h19_eq_16 : χ 19 = χ 16 :=
    third_color_eq hχ19 hχ16 hχ9 hχ12 h9_ne_12 h19_ne_9 h19_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(15) = χ(9) (A).
  have h15_ne_16 : χ 15 ≠ χ 16 := by
    intro h15_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 15
      rw [show (4 * 4 : ℕ) = 16 by decide, h15_eq_16]
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_16, ← h19_eq_16]
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_eq_9 : χ 15 = χ 9 :=
    third_color_eq hχ15 hχ9 hχ12 hχ16 h12_ne_16 h15_ne_12 h15_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(5) = χ(16) (C).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 5
      rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 10)
      rw [show (5 + 10 : ℕ) = 15 by decide, h5_eq_9, ← h15_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(1) = χ(9) (A).
  have h1_ne_16 : χ 1 ≠ χ 16 := by
    intro h1_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 1
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h1_eq_16.symm
    · show χ 1 = χ (1 + 4)
      rw [show (1 + 4 : ℕ) = 5 by decide, h1_eq_16, ← h5_eq_16]
  have h1_ne_12 : χ 1 ≠ χ 12 := by
    intro h1_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 1
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h1_eq_12.symm
    · show χ 1 = χ (1 + 3)
      rw [show (1 + 3 : ℕ) = 4 by decide, h4_eq_12, h1_eq_12]
  have h1_eq_9 : χ 1 = χ 9 :=
    third_color_eq hχ1 hχ9 hχ12 hχ16 h12_ne_16 h1_ne_12 h1_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(11) = χ(16) (C).
  have h11_ne_9 : χ 11 ≠ χ 9 := by
    intro h11_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 1) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 1
      rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h1_eq_9]
    · show χ 1 = χ (1 + 10)
      rw [show (1 + 10 : ℕ) = 11 by decide, h1_eq_9, h11_eq_9]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_16 : χ 11 = χ 16 :=
    third_color_eq hχ11 hχ16 hχ9 hχ12 h9_ne_12 h11_ne_9 h11_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S6: χ(7) = χ(9) (A).
  have h7_ne_16 : χ 7 ≠ χ 16 := by
    intro h7_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 7
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h7_eq_16.symm
    · show χ 7 = χ (7 + 4)
      rw [show (7 + 4 : ℕ) = 11 by decide, h7_eq_16, ← h11_eq_16]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 7
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h7_eq_12]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h7_eq_12, ← h8_eq_12]
  have h7_eq_9 : χ 7 = χ 9 :=
    third_color_eq hχ7 hχ9 hχ12 hχ16 h12_ne_16 h7_ne_12 h7_ne_16 h9_ne_12 h9_ne_16
  -- S7: χ(17) = χ(16) (C).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 7
      rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h7_eq_9]
    · show χ 7 = χ (7 + 10)
      rw [show (7 + 10 : ℕ) = 17 by decide, h7_eq_9, h17_eq_9]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_16 : χ 17 = χ 16 :=
    third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S8: χ(13) = χ(9) (A).
  have h13_ne_16 : χ 13 ≠ χ 16 := by
    intro h13_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 13
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, ← h17_eq_16]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_9 : χ 13 = χ 9 :=
    third_color_eq hχ13 hχ9 hχ12 hχ16 h12_ne_16 h13_ne_12 h13_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: χ(23) ∉ {A, B, C}.
  have h23_ne_9 : χ 23 ≠ χ 9 := by
    intro h23_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 13
      rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 10)
      rw [show (13 + 10 : ℕ) = 23 by decide, h13_eq_9, h23_eq_9]
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 20
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h20_eq_12.symm
    · show χ 20 = χ (20 + 3)
      rw [show (20 + 3 : ℕ) = 23 by decide, h20_eq_12, h23_eq_12]
  have h23_ne_16 : χ 23 ≠ χ 16 := by
    intro h23_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 19
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h19_eq_16.symm
    · show χ 19 = χ (19 + 4)
      rw [show (19 + 4 : ℕ) = 23 by decide, h19_eq_16, h23_eq_16]
  have h23_eq_16 : χ 23 = χ 16 :=
    third_color_eq hχ23 hχ16 hχ9 hχ12 h9_ne_12 h23_ne_9 h23_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h23_ne_16 h23_eq_16

/-- ** contrapositive**: χ(40) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi40_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 40 ≠ χ 9 := by
  intro h40_eq_9
  exact residual_cell_1_chi40_eq_chi9_forces_False_short χ h40 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h40_eq_9

/-- ** layer compression d=10**: χ(40) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=10 hLayer case. -/
theorem residual_cell_1_layer_compression_d10
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 40 = χ 12 ∨ χ 40 = χ 16 := by
  have h40_ne_9 : χ 40 ≠ χ 9 :=
    residual_cell_1_chi40_ne_chi9 χ h40 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ40 : χ 40 < 3 := hχk 40 (by omega) (by omega)
  by_cases h_eq_12 : χ 40 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ40 hχ16 hχ9 hχ12 h9_ne_12 h40_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §107. — d = 11 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses (χ(4) = χ(8) = χ(12) and
  χ(9)/χ(12)/χ(16) pairwise distinct in a 3-coloring), and mono-free
  `bAdicEquation 4` at n ≥ 44, prove χ(44) ∈ {χ(12), χ(16)}. Equivalently,
  rule out χ(44) = χ(9).

  **Type B latent pattern ( / / / reuse).**
  Sharpened preamble + alternating cascade + concrete mono terminal.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = χ(12) | + (16, 16, 20) |
  | P2 | χ(32) = χ(16) | + (32, 4, 12) |
  | P3 | χ(28) = χ(12) | + (16, 28, 32) |
  | P4 | χ(24) = χ(12) | + self-loop m=8 |
  | 1 | χ(33) = χ(16) | self-loop m=11 + (20, 28, 33) |
  | 2 | χ(29) = χ(9) | (16, 29, 33) + (4, 28, 29) |
  | 3 | χ(18) = χ(16) | (44, 18, 29) + (24, 12, 18) |
  | 4 | χ(14) = χ(9) | (16, 14, 18) + (8, 12, 14) |
  | 5 | χ(3) = χ(16) | (44, 3, 14) + (4, 3, 4) |
  | 6 | χ(7) = χ(9) | (16, 3, 7) + (4, 7, 8) |
  | 7 | χ(25) = χ(16) | (44, 14, 25) + (4, 24, 25) |
  | 8 | χ(21) = χ(9) | (16, 21, 25) + (4, 20, 21) |
  | 9 | χ(10) = χ(16) | (44, 10, 21) + (8, 8, 10) |
  | 10 | χ(6) = χ(9) | (16, 6, 10) + self-loop m=2 |
  | 11 | χ(17) = χ(16) | (44, 6, 17) + (20, 12, 17) |
  | 12 | χ(13) = χ(9) | (16, 13, 17) + (4, 12, 13) |
  | 13 | χ(2) = χ(16) | (44, 2, 13) + (8, 2, 4) |
  | T | **(32, 2, 10) mono** | χ(32) = χ(2) = χ(10) = χ(16) |

  Terminal contradiction: mono triple (32, 2, 10) — 32 + 4·2 = 4·10 = 40. ✓

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (16, 28, 32): 16 + 112 = 128 = 4·32 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - self-loop m=11: χ(33) ≠ χ(44) ✓
  - (20, 28, 33): 20 + 112 = 132 = 4·33 ✓
  - (16, 29, 33): 16 + 116 = 132 ✓
  - (4, 28, 29): 4 + 112 = 116 = 4·29 ✓
  - (44, 18, 29): 44 + 72 = 116 ✓
  - (24, 12, 18): 24 + 48 = 72 = 4·18 ✓
  - (16, 14, 18): 16 + 56 = 72 ✓
  - (8, 12, 14): 8 + 48 = 56 = 4·14 ✓
  - (44, 3, 14): 44 + 12 = 56 ✓
  - (4, 3, 4): 4 + 12 = 16 = 4·4 ✓
  - (16, 3, 7): 16 + 12 = 28 = 4·7 ✓
  - (4, 7, 8): 4 + 28 = 32 = 4·8 ✓
  - (44, 14, 25): 44 + 56 = 100 = 4·25 ✓
  - (4, 24, 25): 4 + 96 = 100 ✓
  - (16, 21, 25): 16 + 84 = 100 ✓
  - (4, 20, 21): 4 + 80 = 84 = 4·21 ✓
  - (44, 10, 21): 44 + 40 = 84 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (16, 6, 10): 16 + 24 = 40 ✓
  - self-loop m=2: χ(6) ≠ χ(8) ✓
  - (44, 6, 17): 44 + 24 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (16, 13, 17): 16 + 52 = 68 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (44, 2, 13): 44 + 8 = 52 ✓
  - (8, 2, 4): 8 + 8 = 16 = 4·4 ✓
  - (32, 2, 10): 32 + 8 = 40 = 4·10 ✓ (TERMINAL MONO)
-/

set_option maxHeartbeats 800000 in
/-- ** chi(44) = chi(9) closure**: residual cell (1) + χ(44) = χ(9) ⟹
  False at n ≥ 44. 13-step cascade ending in concrete mono triple
  (32, 2, 10) under common color χ(16). Calls / / / 
  internally for sharpened preamble. -/
theorem residual_cell_1_chi44_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h44_eq_9 : χ 44 = χ 9) :
    False := by
  have hχ2 : χ 2 < 3 := hχk 2 (by omega) (by omega)
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have hχ29 : χ 29 < 3 := hχk 29 (by omega) (by omega)
  have hχ33 : χ 33 < 3 := hχk 33 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(28) = χ(12). + (16, 28, 32).
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 28
      rw [show (4 * 4 : ℕ) = 16 by decide, h28_eq_16]
    · show χ 28 = χ (28 + 4)
      rw [show (28 + 4 : ℕ) = 32 by decide, h28_eq_16, ← h32_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- PREAMBLE P4: χ(24) = χ(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    -- h_self : χ ((4 - 1) * 8) ≠ χ (4 * 8), i.e., χ 24 ≠ χ 32.
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- MAIN CASCADE.
  -- S1: χ(33) = χ(16) (C).
  have h33_ne_9 : χ 33 ≠ χ 9 := by
    intro h33_eq_9
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 11) (by omega) (by omega)
    -- h_self : χ 33 ≠ χ 44.
    apply h_self
    show χ ((4 - 1) * 11) = χ (4 * 11)
    rw [show ((4 - 1) * 11 : ℕ) = 33 by decide,
        show ((4 : ℕ) * 11) = 44 by decide, h33_eq_9, ← h44_eq_9]
  have h33_ne_12 : χ 33 ≠ χ 12 := by
    intro h33_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 28
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12.trans h28_eq_12.symm
    · show χ 28 = χ (28 + 5)
      rw [show (28 + 5 : ℕ) = 33 by decide, h28_eq_12, h33_eq_12]
  have h33_eq_16 : χ 33 = χ 16 :=
    third_color_eq hχ33 hχ16 hχ9 hχ12 h9_ne_12 h33_ne_9 h33_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(29) = χ(9) (A).
  have h29_ne_16 : χ 29 ≠ χ 16 := by
    intro h29_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 29) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 29
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h29_eq_16.symm
    · show χ 29 = χ (29 + 4)
      rw [show (29 + 4 : ℕ) = 33 by decide, h29_eq_16, ← h33_eq_16]
  have h29_ne_12 : χ 29 ≠ χ 12 := by
    intro h29_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 28
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h28_eq_12.symm
    · show χ 28 = χ (28 + 1)
      rw [show (28 + 1 : ℕ) = 29 by decide, h28_eq_12, h29_eq_12]
  have h29_eq_9 : χ 29 = χ 9 :=
    third_color_eq hχ29 hχ9 hχ12 hχ16 h12_ne_16 h29_ne_12 h29_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(18) = χ(16) (C).
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 18
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h18_eq_9]
    · show χ 18 = χ (18 + 11)
      rw [show (18 + 11 : ℕ) = 29 by decide, h18_eq_9, ← h29_eq_9]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 12
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_12
    · show χ 12 = χ (12 + 6)
      rw [show (12 + 6 : ℕ) = 18 by decide, h18_eq_12]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(14) = χ(9) (A).
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 14
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h14_eq_16.symm
    · show χ 14 = χ (14 + 4)
      rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, ← h18_eq_16]
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ12 hχ16 h12_ne_16 h14_ne_12 h14_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(3) = χ(16) (C).
  have h3_ne_9 : χ 3 ≠ χ 9 := by
    intro h3_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 3
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h3_eq_9]
    · show χ 3 = χ (3 + 11)
      rw [show (3 + 11 : ℕ) = 14 by decide, h3_eq_9, ← h14_eq_9]
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h3_eq_12.symm
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h3_eq_12, h4_eq_12]
  have h3_eq_16 : χ 3 = χ 16 :=
    third_color_eq hχ3 hχ16 hχ9 hχ12 h9_ne_12 h3_ne_9 h3_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S6: χ(7) = χ(9) (A).
  have h7_ne_16 : χ 7 ≠ χ 16 := by
    intro h7_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 3
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h3_eq_16.symm
    · show χ 3 = χ (3 + 4)
      rw [show (3 + 4 : ℕ) = 7 by decide, h3_eq_16, h7_eq_16]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 7
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, h7_eq_12]
    · show χ 7 = χ (7 + 1)
      rw [show (7 + 1 : ℕ) = 8 by decide, h7_eq_12, ← h8_eq_12]
  have h7_eq_9 : χ 7 = χ 9 :=
    third_color_eq hχ7 hχ9 hχ12 hχ16 h12_ne_16 h7_ne_12 h7_ne_16 h9_ne_12 h9_ne_16
  -- S7: χ(25) = χ(16) (C).
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 14
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h14_eq_9]
    · show χ 14 = χ (14 + 11)
      rw [show (14 + 11 : ℕ) = 25 by decide, h14_eq_9, h25_eq_9]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 24
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 1)
      rw [show (24 + 1 : ℕ) = 25 by decide, h24_eq_12, h25_eq_12]
  have h25_eq_16 : χ 25 = χ 16 :=
    third_color_eq hχ25 hχ16 hχ9 hχ12 h9_ne_12 h25_ne_9 h25_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S8: χ(21) = χ(9) (A).
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 21
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h21_eq_16.symm
    · show χ 21 = χ (21 + 4)
      rw [show (21 + 4 : ℕ) = 25 by decide, h21_eq_16, ← h25_eq_16]
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  have h21_eq_9 : χ 21 = χ 9 :=
    third_color_eq hχ21 hχ9 hχ12 hχ16 h12_ne_16 h21_ne_12 h21_ne_16 h9_ne_12 h9_ne_16
  -- S9: χ(10) = χ(16) (C).
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 10
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h10_eq_9]
    · show χ 10 = χ (10 + 11)
      rw [show (10 + 11 : ℕ) = 21 by decide, h10_eq_9, ← h21_eq_9]
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S10: χ(6) = χ(9) (A).
  have h6_ne_16 : χ 6 ≠ χ 16 := by
    intro h6_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 6
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h6_eq_16.symm
    · show χ 6 = χ (6 + 4)
      rw [show (6 + 4 : ℕ) = 10 by decide, h6_eq_16, ← h10_eq_16]
  have h6_ne_12 : χ 6 ≠ χ 12 := by
    intro h6_eq_12
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 2) (by omega) (by omega)
    -- h_self : χ 6 ≠ χ 8.
    apply h_self
    show χ ((4 - 1) * 2) = χ (4 * 2)
    rw [show ((4 - 1) * 2 : ℕ) = 6 by decide,
        show ((4 : ℕ) * 2) = 8 by decide, h6_eq_12, ← h8_eq_12]
  have h6_eq_9 : χ 6 = χ 9 :=
    third_color_eq hχ6 hχ9 hχ12 hχ16 h12_ne_16 h6_ne_12 h6_ne_16 h9_ne_12 h9_ne_16
  -- S11: χ(17) = χ(16) (C).
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 6
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h6_eq_9]
    · show χ 6 = χ (6 + 11)
      rw [show (6 + 11 : ℕ) = 17 by decide, h6_eq_9, h17_eq_9]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_16 : χ 17 = χ 16 :=
    third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S12: χ(13) = χ(9) (A).
  have h13_ne_16 : χ 13 ≠ χ 16 := by
    intro h13_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 13
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, ← h17_eq_16]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_9 : χ 13 = χ 9 :=
    third_color_eq hχ13 hχ9 hχ12 hχ16 h12_ne_16 h13_ne_12 h13_ne_16 h9_ne_12 h9_ne_16
  -- S13: χ(2) = χ(16) (C).
  have h2_ne_9 : χ 2 ≠ χ 9 := by
    intro h2_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 2
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h2_eq_9]
    · show χ 2 = χ (2 + 11)
      rw [show (2 + 11 : ℕ) = 13 by decide, h2_eq_9, ← h13_eq_9]
  have h2_ne_12 : χ 2 ≠ χ 12 := by
    intro h2_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 2) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 2
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h2_eq_12.symm
    · show χ 2 = χ (2 + 2)
      rw [show (2 + 2 : ℕ) = 4 by decide, h2_eq_12, h4_eq_12]
  have h2_eq_16 : χ 2 = χ 16 :=
    third_color_eq hχ2 hχ16 hχ9 hχ12 h9_ne_12 h2_ne_9 h2_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (32, 2, 10) mono with χ(32) = χ(2) = χ(10) = χ(16).
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 2) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 2
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h2_eq_16]
  · show χ 2 = χ (2 + 8)
    rw [show (2 + 8 : ℕ) = 10 by decide, h2_eq_16, ← h10_eq_16]

/-- ** contrapositive**: χ(44) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi44_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 44 ≠ χ 9 := by
  intro h44_eq_9
  exact residual_cell_1_chi44_eq_chi9_forces_False_short χ h44 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h44_eq_9

/-- ** layer compression d=11**: χ(44) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=11 hLayer case. -/
theorem residual_cell_1_layer_compression_d11
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 44 = χ 12 ∨ χ 44 = χ 16 := by
  have h44_ne_9 : χ 44 ≠ χ 9 :=
    residual_cell_1_chi44_ne_chi9 χ h44 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ44 : χ 44 < 3 := hχk 44 (by omega) (by omega)
  by_cases h_eq_12 : χ 44 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ44 hχ16 hχ9 hχ12 h9_ne_12 h44_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §108. — d = 12 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses (χ(4) = χ(8) = χ(12) and
  χ(9)/χ(12)/χ(16) pairwise distinct in a 3-coloring), and mono-free
  `bAdicEquation 4` at n ≥ 48, prove χ(48) ∈ {χ(12), χ(16)}. Equivalently,
  rule out χ(48) = χ(9).

  **Surprise compression.** The d = 12 case is *strictly shorter* than
   because (48, 9, 21) directly couples the two A anchors χ(48), χ(9)
  via a single d-step jump (jump = 12 = (b − 1) · 4 = 21 − 9), eliminating
  most of the propagation chain. The full proof needs only a 5-step
  cascade plus the standard preamble.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = χ(12) | + (16, 16, 20) |
  | P2 | χ(32) = χ(16) | + (32, 4, 12) |
  | P3 | χ(24) = χ(12) | + self-loop m=8 |
  | 1 | χ(21) = χ(16) | (48, 9, 21) + (4, 20, 21) |
  | 2 | χ(25) = χ(9) | (16, 21, 25) + (4, 24, 25) |
  | 3 | χ(13) = χ(16) | (48, 13, 25) + (4, 12, 13) |
  | 4 | χ(17) = χ(9) | (16, 13, 17) + (20, 12, 17) |
  | 5 | χ(5) = χ(16) | (48, 5, 17) + (4, 4, 5) |
  | T | **(32, 5, 13) mono** | χ(32) = χ(5) = χ(13) = χ(16) |

  Terminal contradiction: mono triple (32, 5, 13) — 32 + 4·5 = 4·13 = 52. ✓
  All three colours collapse to χ(16) via P2 + S3 + S5.

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - (48, 9, 21): 48 + 36 = 84 = 4·21 ✓
  - (4, 20, 21): 4 + 80 = 84 ✓
  - (16, 21, 25): 16 + 84 = 100 = 4·25 ✓
  - (4, 24, 25): 4 + 96 = 100 ✓
  - (48, 13, 25): 48 + 52 = 100 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (16, 13, 17): 16 + 52 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (48, 5, 17): 48 + 20 = 68 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (32, 5, 13): 32 + 20 = 52 = 4·13 ✓ (TERMINAL MONO)
-/

set_option maxHeartbeats 800000 in
/-- ** chi(48) = chi(9) closure**: residual cell (1) + χ(48) = χ(9) ⟹
  False at n ≥ 48. 5-step cascade ending in concrete mono triple
  (32, 5, 13) under common color χ(16). Significantly shorter than
   because (48, 9, 21) couples both A anchors in one step. -/
theorem residual_cell_1_chi48_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h48_eq_9 : χ 48 = χ 9) :
    False := by
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(24) = χ(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- MAIN CASCADE.
  -- S1: χ(21) = χ(16) (C).
  have h21_ne_9 : χ 21 ≠ χ 9 := by
    intro h21_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 9
      rw [show (4 * 12 : ℕ) = 48 by decide]; exact h48_eq_9
    · show χ 9 = χ (9 + 12)
      rw [show (9 + 12 : ℕ) = 21 by decide, h21_eq_9]
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  have h21_eq_16 : χ 21 = χ 16 :=
    third_color_eq hχ21 hχ16 hχ9 hχ12 h9_ne_12 h21_ne_9 h21_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(25) = χ(9) (A).
  have h25_ne_16 : χ 25 ≠ χ 16 := by
    intro h25_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 21
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h21_eq_16.symm
    · show χ 21 = χ (21 + 4)
      rw [show (21 + 4 : ℕ) = 25 by decide, h21_eq_16, h25_eq_16]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 24
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 1)
      rw [show (24 + 1 : ℕ) = 25 by decide, h24_eq_12, h25_eq_12]
  have h25_eq_9 : χ 25 = χ 9 :=
    third_color_eq hχ25 hχ9 hχ12 hχ16 h12_ne_16 h25_ne_12 h25_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(13) = χ(16) (C).
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 13
      rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 12)
      rw [show (13 + 12 : ℕ) = 25 by decide, h13_eq_9, ← h25_eq_9]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_16 : χ 13 = χ 16 :=
    third_color_eq hχ13 hχ16 hχ9 hχ12 h9_ne_12 h13_ne_9 h13_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(17) = χ(9) (A).
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 13
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
    · show χ 13 = χ (13 + 4)
      rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, h17_eq_16]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(5) = χ(16) (C).
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 5
      rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 12)
      rw [show (5 + 12 : ℕ) = 17 by decide, h5_eq_9, ← h17_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (32, 5, 13) mono with χ(32) = χ(5) = χ(13) = χ(16).
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 5
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h5_eq_16]
  · show χ 5 = χ (5 + 8)
    rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_16, ← h13_eq_16]

/-- ** contrapositive**: χ(48) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi48_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 48 ≠ χ 9 := by
  intro h48_eq_9
  exact residual_cell_1_chi48_eq_chi9_forces_False_short χ h48 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h48_eq_9

/-- ** layer compression d=12**: χ(48) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=12 hLayer case. -/
theorem residual_cell_1_layer_compression_d12
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 48 = χ 12 ∨ χ 48 = χ 16 := by
  have h48_ne_9 : χ 48 ≠ χ 9 :=
    residual_cell_1_chi48_ne_chi9 χ h48 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ48 : χ 48 < 3 := hχk 48 (by omega) (by omega)
  by_cases h_eq_12 : χ 48 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ48 hχ16 hχ9 hχ12 h9_ne_12 h48_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §109. — d = 13 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses (χ(4) = χ(8) = χ(12) and
  χ(9)/χ(12)/χ(16) pairwise distinct in a 3-coloring), and mono-free
  `bAdicEquation 4` at n ≥ 52, prove χ(52) ∈ {χ(12), χ(16)}.

  **Geometry.** The d = 13 jump couples χ(52) = A with χ(9) directly via
  (52, 9, 22), forcing χ(22) = C. From there, alternating d = 8 + d = 2
  propagation (anchored at χ(32) = C, χ(28) = B, χ(24) = B, χ(20) = B)
  produces three A positions (30, 26) and three C positions (22, 17, 13).
  Terminal: the simplest possible — (16, 13, 17), all χ(16) = C.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = χ(12) | + (16, 16, 20) |
  | P2 | χ(32) = χ(16) | + (32, 4, 12) |
  | P3 | χ(28) = χ(12) | + (16, 28, 32) |
  | P4 | χ(24) = χ(12) | + self-loop m=8 |
  | 1 | χ(22) = χ(16) | (52, 9, 22) + (8, 20, 22) |
  | 2 | χ(30) = χ(9) | (32, 22, 30) + (8, 28, 30) |
  | 3 | χ(17) = χ(16) | (52, 17, 30) + (20, 12, 17) |
  | 4 | χ(26) = χ(9) | (16, 22, 26) + (8, 24, 26) |
  | 5 | χ(13) = χ(16) | (52, 13, 26) + (4, 12, 13) |
  | T | **(16, 13, 17) mono** | χ(16) = χ(13) = χ(17) = χ(16) |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (16, 28, 32): 16 + 112 = 128 = 4·32 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - (52, 9, 22): 52 + 36 = 88 = 4·22 ✓
  - (8, 20, 22): 8 + 80 = 88 ✓
  - (32, 22, 30): 32 + 88 = 120 = 4·30 ✓
  - (8, 28, 30): 8 + 112 = 120 ✓
  - (52, 17, 30): 52 + 68 = 120 ✓
  - (20, 12, 17): 20 + 48 = 68 = 4·17 ✓
  - (16, 22, 26): 16 + 88 = 104 = 4·26 ✓
  - (8, 24, 26): 8 + 96 = 104 ✓
  - (52, 13, 26): 52 + 52 = 104 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (16, 13, 17): 16 + 52 = 68 = 4·17 ✓ (TERMINAL MONO with all C)
-/

set_option maxHeartbeats 800000 in
/-- ** chi(52) = chi(9) closure**: residual cell (1) + χ(52) = χ(9) ⟹
  False at n ≥ 52. 5-step cascade ending in terminal mono triple
  (16, 13, 17) under common colour χ(16). -/
theorem residual_cell_1_chi52_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h52_eq_9 : χ 52 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ26 : χ 26 < 3 := hχk 26 (by omega) (by omega)
  have hχ30 : χ 30 < 3 := hχk 30 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(28) = χ(12). + (16, 28, 32).
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 28
      rw [show (4 * 4 : ℕ) = 16 by decide, h28_eq_16]
    · show χ 28 = χ (28 + 4)
      rw [show (28 + 4 : ℕ) = 32 by decide, h28_eq_16, ← h32_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- PREAMBLE P4: χ(24) = χ(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- MAIN CASCADE.
  -- S1: χ(22) = χ(16) (C). Via (52, 9, 22) ≠ A + (8, 20, 22) ≠ B.
  have h22_ne_9 : χ 22 ≠ χ 9 := by
    intro h22_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 13) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 13) = χ 9
      rw [show (4 * 13 : ℕ) = 52 by decide]; exact h52_eq_9
    · show χ 9 = χ (9 + 13)
      rw [show (9 + 13 : ℕ) = 22 by decide, h22_eq_9]
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 20
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_12, h22_eq_12]
  have h22_eq_16 : χ 22 = χ 16 :=
    third_color_eq hχ22 hχ16 hχ9 hχ12 h9_ne_12 h22_ne_9 h22_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(30) = χ(9) (A). Via (32, 22, 30) ≠ C + (8, 28, 30) ≠ B.
  have h30_ne_16 : χ 30 ≠ χ 16 := by
    intro h30_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 22
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h22_eq_16]
    · show χ 22 = χ (22 + 8)
      rw [show (22 + 8 : ℕ) = 30 by decide, h22_eq_16, h30_eq_16]
  have h30_ne_12 : χ 30 ≠ χ 12 := by
    intro h30_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 28
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h28_eq_12.symm
    · show χ 28 = χ (28 + 2)
      rw [show (28 + 2 : ℕ) = 30 by decide, h28_eq_12, h30_eq_12]
  have h30_eq_9 : χ 30 = χ 9 :=
    third_color_eq hχ30 hχ9 hχ12 hχ16 h12_ne_16 h30_ne_12 h30_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(17) = χ(16) (C). Via (52, 17, 30) ≠ A + (20, 12, 17) ≠ B.
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 13) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 13) = χ 17
      rw [show (4 * 13 : ℕ) = 52 by decide, h52_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 13)
      rw [show (17 + 13 : ℕ) = 30 by decide, h17_eq_9, ← h30_eq_9]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_16 : χ 17 = χ 16 :=
    third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(26) = χ(9) (A). Via (16, 22, 26) ≠ C + (8, 24, 26) ≠ B.
  have h26_ne_16 : χ 26 ≠ χ 16 := by
    intro h26_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 22
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h22_eq_16.symm
    · show χ 22 = χ (22 + 4)
      rw [show (22 + 4 : ℕ) = 26 by decide, h22_eq_16, h26_eq_16]
  have h26_ne_12 : χ 26 ≠ χ 12 := by
    intro h26_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 24
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 2)
      rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_12, h26_eq_12]
  have h26_eq_9 : χ 26 = χ 9 :=
    third_color_eq hχ26 hχ9 hχ12 hχ16 h12_ne_16 h26_ne_12 h26_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(13) = χ(16) (C). Via (52, 13, 26) ≠ A + (4, 12, 13) ≠ B.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 13) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 13) = χ 13
      rw [show (4 * 13 : ℕ) = 52 by decide, h52_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 13)
      rw [show (13 + 13 : ℕ) = 26 by decide, h13_eq_9, ← h26_eq_9]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_16 : χ 13 = χ 16 :=
    third_color_eq hχ13 hχ16 hχ9 hχ12 h9_ne_12 h13_ne_9 h13_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (16, 13, 17) mono with χ(16) = χ(13) = χ(17) = χ(16).
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 13
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
  · show χ 13 = χ (13 + 4)
    rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, ← h17_eq_16]

/-- ** contrapositive**: χ(52) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi52_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 52 ≠ χ 9 := by
  intro h52_eq_9
  exact residual_cell_1_chi52_eq_chi9_forces_False_short χ h52 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h52_eq_9

/-- ** layer compression d=13**: χ(52) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=13 hLayer case. -/
theorem residual_cell_1_layer_compression_d13
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 52 = χ 12 ∨ χ 52 = χ 16 := by
  have h52_ne_9 : χ 52 ≠ χ 9 :=
    residual_cell_1_chi52_ne_chi9 χ h52 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ52 : χ 52 < 3 := hχk 52 (by omega) (by omega)
  by_cases h_eq_12 : χ 52 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ52 hχ16 hχ9 hχ12 h9_ne_12 h52_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §110. — d = 14 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses (χ(4) = χ(8) = χ(12) and
  χ(9)/χ(12)/χ(16) pairwise distinct in a 3-coloring), and mono-free
  `bAdicEquation 4` at n ≥ 56, prove χ(56) ∈ {χ(12), χ(16)}.

  **Geometry.** d = 14 couples χ(56) = A with χ(9) via (56, 9, 23), and
  switches B-exclusions from d = 2 jumps ( style) to d = 3 jumps
  ((12, 20, 23), (12, 28, 31)) plus d = 7 ((28, 20, 27)). This avoids
  needing χ(24), so only a **3-anchor preamble** suffices.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = χ(12) | + (16, 16, 20) |
  | P2 | χ(32) = χ(16) | + (32, 4, 12) |
  | P3 | χ(28) = χ(12) | + (16, 28, 32) |
  | 1 | χ(23) = χ(16) | (56, 9, 23) + (12, 20, 23) |
  | 2 | χ(31) = χ(9) | (32, 23, 31) + (12, 28, 31) |
  | 3 | χ(17) = χ(16) | (56, 17, 31) + (20, 12, 17) |
  | 4 | χ(27) = χ(9) | (16, 23, 27) + (28, 20, 27) |
  | 5 | χ(13) = χ(16) | (56, 13, 27) + (4, 12, 13) |
  | T | **(16, 13, 17) mono** | χ(16) = χ(13) = χ(17) = χ(16) |

  Same terminal as; only intermediate positions and B-exclusion
  triples differ. Cascade structurally identical: A-anchor → C → A → C → A → C.

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (16, 28, 32): 16 + 112 = 128 = 4·32 ✓
  - (56, 9, 23): 56 + 36 = 92 = 4·23 ✓
  - (12, 20, 23): 12 + 80 = 92 ✓
  - (32, 23, 31): 32 + 92 = 124 = 4·31 ✓
  - (12, 28, 31): 12 + 112 = 124 ✓
  - (56, 17, 31): 56 + 68 = 124 ✓
  - (20, 12, 17): 20 + 48 = 68 = 4·17 ✓
  - (16, 23, 27): 16 + 92 = 108 = 4·27 ✓
  - (28, 20, 27): 28 + 80 = 108 ✓
  - (56, 13, 27): 56 + 52 = 108 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (16, 13, 17): 16 + 52 = 68 = 4·17 ✓ (TERMINAL MONO with all C)
-/

set_option maxHeartbeats 800000 in
/-- ** chi(56) = chi(9) closure**: residual cell (1) + χ(56) = χ(9) ⟹
  False at n ≥ 56. 5-step cascade with 3-anchor preamble (avoiding χ(24)),
  ending in terminal mono triple (16, 13, 17) under colour χ(16). -/
theorem residual_cell_1_chi56_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h56_eq_9 : χ 56 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  have hχ27 : χ 27 < 3 := hχk 27 (by omega) (by omega)
  have hχ31 : χ 31 < 3 := hχk 31 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(28) = χ(12). + (16, 28, 32).
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 28
      rw [show (4 * 4 : ℕ) = 16 by decide, h28_eq_16]
    · show χ 28 = χ (28 + 4)
      rw [show (28 + 4 : ℕ) = 32 by decide, h28_eq_16, ← h32_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- MAIN CASCADE.
  -- S1: χ(23) = χ(16) (C). Via (56, 9, 23) ≠ A + (12, 20, 23) ≠ B.
  have h23_ne_9 : χ 23 ≠ χ 9 := by
    intro h23_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 14) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 14) = χ 9
      rw [show (4 * 14 : ℕ) = 56 by decide]; exact h56_eq_9
    · show χ 9 = χ (9 + 14)
      rw [show (9 + 14 : ℕ) = 23 by decide, h23_eq_9]
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 20
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h20_eq_12.symm
    · show χ 20 = χ (20 + 3)
      rw [show (20 + 3 : ℕ) = 23 by decide, h20_eq_12, h23_eq_12]
  have h23_eq_16 : χ 23 = χ 16 :=
    third_color_eq hχ23 hχ16 hχ9 hχ12 h9_ne_12 h23_ne_9 h23_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(31) = χ(9) (A). Via (32, 23, 31) ≠ C + (12, 28, 31) ≠ B.
  have h31_ne_16 : χ 31 ≠ χ 16 := by
    intro h31_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 23
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h23_eq_16]
    · show χ 23 = χ (23 + 8)
      rw [show (23 + 8 : ℕ) = 31 by decide, h23_eq_16, h31_eq_16]
  have h31_ne_12 : χ 31 ≠ χ 12 := by
    intro h31_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 28
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h28_eq_12.symm
    · show χ 28 = χ (28 + 3)
      rw [show (28 + 3 : ℕ) = 31 by decide, h28_eq_12, h31_eq_12]
  have h31_eq_9 : χ 31 = χ 9 :=
    third_color_eq hχ31 hχ9 hχ12 hχ16 h12_ne_16 h31_ne_12 h31_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(17) = χ(16) (C). Via (56, 17, 31) ≠ A + (20, 12, 17) ≠ B.
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 14) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 14) = χ 17
      rw [show (4 * 14 : ℕ) = 56 by decide, h56_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 14)
      rw [show (17 + 14 : ℕ) = 31 by decide, h17_eq_9, ← h31_eq_9]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_16 : χ 17 = χ 16 :=
    third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(27) = χ(9) (A). Via (16, 23, 27) ≠ C + (28, 20, 27) ≠ B.
  have h27_ne_16 : χ 27 ≠ χ 16 := by
    intro h27_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 23
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h23_eq_16.symm
    · show χ 23 = χ (23 + 4)
      rw [show (23 + 4 : ℕ) = 27 by decide, h23_eq_16, h27_eq_16]
  have h27_ne_12 : χ 27 ≠ χ 12 := by
    intro h27_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 20
      rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 7)
      rw [show (20 + 7 : ℕ) = 27 by decide, h20_eq_12, h27_eq_12]
  have h27_eq_9 : χ 27 = χ 9 :=
    third_color_eq hχ27 hχ9 hχ12 hχ16 h12_ne_16 h27_ne_12 h27_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(13) = χ(16) (C). Via (56, 13, 27) ≠ A + (4, 12, 13) ≠ B.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 14) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 14) = χ 13
      rw [show (4 * 14 : ℕ) = 56 by decide, h56_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 14)
      rw [show (13 + 14 : ℕ) = 27 by decide, h13_eq_9, ← h27_eq_9]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_16 : χ 13 = χ 16 :=
    third_color_eq hχ13 hχ16 hχ9 hχ12 h9_ne_12 h13_ne_9 h13_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (16, 13, 17) mono with χ(16) = χ(13) = χ(17) = χ(16).
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 13
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
  · show χ 13 = χ (13 + 4)
    rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, ← h17_eq_16]

/-- ** contrapositive**: χ(56) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi56_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 56 ≠ χ 9 := by
  intro h56_eq_9
  exact residual_cell_1_chi56_eq_chi9_forces_False_short χ h56 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h56_eq_9

/-- ** layer compression d=14**: χ(56) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=14 hLayer case. -/
theorem residual_cell_1_layer_compression_d14
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 56 = χ 12 ∨ χ 56 = χ 16 := by
  have h56_ne_9 : χ 56 ≠ χ 9 :=
    residual_cell_1_chi56_ne_chi9 χ h56 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ56 : χ 56 < 3 := hχk 56 (by omega) (by omega)
  by_cases h_eq_12 : χ 56 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ56 hχ16 hχ9 hχ12 h9_ne_12 h56_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §111. — d = 15 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses, mono-free `bAdicEquation 4`
  at n ≥ 60, prove χ(60) ∈ {χ(12), χ(16)}.

  **First-strike obstruction.** The d = 13/14 trick — pairing χ(60) = A with
  χ(9) via (4·d, 9, 9+d) — fails for d = 15 because (60, 9, 24) lands on
  χ(24) = B. We must instead derive new high anchors first.

  **Sharpened anchors discovered (unconditional under preamble).**
  - χ(36) = B via + (16, 32, 36) [χ(16) = χ(32) = C anchor pair].
  - χ(40) = B via + (32, 32, 40) [d = 8 self-anchor at C].

  **Conditional anchor (under χ(60) = χ(9)).**
  - χ(45) = C via (36, 36, 45) [χ(45) ≠ B] + self-loop m = 15 [χ(45) ≠ A].

  **4-step cascade** (terminal directly uses d = 15 anchor):

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(32) = χ(16) | + (32, 4, 12) |
  | P2 | χ(28) = χ(12) | + (16, 28, 32) |
  | P3 | χ(24) = χ(12) | + self-loop m = 8 |
  | P4 | χ(36) = χ(12) | + (16, 32, 36) |
  | P5 | χ(40) = χ(12) | + (32, 32, 40) |
  | P6 | χ(45) = χ(16) | self-loop m = 15 + (36, 36, 45) |
  | 1 | χ(41) = χ(9) | (16, 41, 45) + (4, 40, 41) |
  | 2 | χ(26) = χ(16) | (60, 26, 41) + (8, 24, 26) |
  | 3 | χ(34) = χ(9) | (32, 26, 34) + (24, 28, 34) |
  | 4 | χ(49) = χ(9) | (16, 45, 49) + (36, 40, 49) |
  | T | **(60, 34, 49) mono** | χ(60) = χ(34) = χ(49) = χ(9) (all A) |

  Terminal uses the d = 15 anchor directly: 60 + 4·34 = 196 = 4·49.
  All three positions = A.

  All triples verified for b=4 (x + 4y = 4z):
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (16, 28, 32): 16 + 112 = 128 = 4·32 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - (16, 32, 36): 16 + 128 = 144 = 4·36 ✓
  - (32, 32, 40): 32 + 128 = 160 = 4·40 ✓
  - self-loop m=15: χ(45) ≠ χ(60) ✓
  - (36, 36, 45): 36 + 144 = 180 = 4·45 ✓
  - (16, 41, 45): 16 + 164 = 180 = 4·45 ✓
  - (4, 40, 41): 4 + 160 = 164 = 4·41 ✓
  - (60, 26, 41): 60 + 104 = 164 = 4·41 ✓
  - (8, 24, 26): 8 + 96 = 104 = 4·26 ✓
  - (32, 26, 34): 32 + 104 = 136 = 4·34 ✓
  - (24, 28, 34): 24 + 112 = 136 = 4·34 ✓
  - (16, 45, 49): 16 + 180 = 196 = 4·49 ✓
  - (36, 40, 49): 36 + 160 = 196 = 4·49 ✓
  - (60, 34, 49): 60 + 136 = 196 = 4·49 ✓ (TERMINAL MONO with all A)
-/

set_option maxHeartbeats 1600000 in
/-- ** chi(60) = chi(9) closure**: residual cell (1) + χ(60) = χ(9) ⟹
  False at n ≥ 60. Extended preamble (sharpening χ(36) = B, χ(40) = B,
  χ(45) = C), 4-step cascade ending in terminal mono triple (60, 34, 49)
  with all three positions = A. -/
theorem residual_cell_1_chi60_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h60_eq_9 : χ 60 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ26 : χ 26 < 3 := hχk 26 (by omega) (by omega)
  have hχ34 : χ 34 < 3 := hχk 34 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  have hχ40 : χ 40 < 3 := hχk 40 (by omega) (by omega)
  have hχ41 : χ 41 < 3 := hχk 41 (by omega) (by omega)
  have hχ45 : χ 45 < 3 := hχk 45 (by omega) (by omega)
  have hχ49 : χ 49 < 3 := hχk 49 (by omega) (by omega)
  -- PREAMBLE P1: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P2: χ(28) = χ(12). + (16, 28, 32).
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 28
      rw [show (4 * 4 : ℕ) = 16 by decide, h28_eq_16]
    · show χ 28 = χ (28 + 4)
      rw [show (28 + 4 : ℕ) = 32 by decide, h28_eq_16, ← h32_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- PREAMBLE P3: χ(24) = χ(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- PREAMBLE P4: χ(36) = χ(12). + (16, 32, 36).
  have h36_disj : χ 36 = χ 12 ∨ χ 36 = χ 16 :=
    residual_cell_1_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h36_ne_16 : χ 36 ≠ χ 16 := by
    intro h36_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 32
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h32_eq_16.symm
    · show χ 32 = χ (32 + 4)
      rw [show (32 + 4 : ℕ) = 36 by decide, h32_eq_16, ← h36_eq_16]
  have h36_eq_12 : χ 36 = χ 12 := h36_disj.resolve_right h36_ne_16
  -- PREAMBLE P5: χ(40) = χ(12). + (32, 32, 40).
  have h40_disj : χ 40 = χ 12 ∨ χ 40 = χ 16 :=
    residual_cell_1_layer_compression_d10 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h40_ne_16 : χ 40 ≠ χ 16 := by
    intro h40_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 32
      rw [show (4 * 8 : ℕ) = 32 by decide]
    · show χ 32 = χ (32 + 8)
      rw [show (32 + 8 : ℕ) = 40 by decide, h32_eq_16, ← h40_eq_16]
  have h40_eq_12 : χ 40 = χ 12 := h40_disj.resolve_right h40_ne_16
  -- PREAMBLE P6: χ(45) = χ(16). Self-loop m=15 + (36, 36, 45).
  have h45_ne_9 : χ 45 ≠ χ 9 := by
    intro h45_eq_9
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 15) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 15) = χ (4 * 15)
    rw [show ((4 - 1) * 15 : ℕ) = 45 by decide,
        show ((4 : ℕ) * 15) = 60 by decide, h45_eq_9, ← h60_eq_9]
  have h45_ne_12 : χ 45 ≠ χ 12 := by
    intro h45_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 36) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 36
      rw [show (4 * 9 : ℕ) = 36 by decide]
    · show χ 36 = χ (36 + 9)
      rw [show (36 + 9 : ℕ) = 45 by decide, h36_eq_12, h45_eq_12]
  have h45_eq_16 : χ 45 = χ 16 :=
    third_color_eq hχ45 hχ16 hχ9 hχ12 h9_ne_12 h45_ne_9 h45_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- MAIN CASCADE.
  -- S1: χ(41) = χ(9) (A). Via (16, 41, 45) ≠ C + (4, 40, 41) ≠ B.
  have h41_ne_16 : χ 41 ≠ χ 16 := by
    intro h41_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 41) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 41
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h41_eq_16.symm
    · show χ 41 = χ (41 + 4)
      rw [show (41 + 4 : ℕ) = 45 by decide, h41_eq_16, ← h45_eq_16]
  have h41_ne_12 : χ 41 ≠ χ 12 := by
    intro h41_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 40) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 40
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h40_eq_12.symm
    · show χ 40 = χ (40 + 1)
      rw [show (40 + 1 : ℕ) = 41 by decide, h40_eq_12, h41_eq_12]
  have h41_eq_9 : χ 41 = χ 9 :=
    third_color_eq hχ41 hχ9 hχ12 hχ16 h12_ne_16 h41_ne_12 h41_ne_16 h9_ne_12 h9_ne_16
  -- S2: χ(26) = χ(16) (C). Via (60, 26, 41) ≠ A + (8, 24, 26) ≠ B.
  have h26_ne_9 : χ 26 ≠ χ 9 := by
    intro h26_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 15) (y := 26) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 15) = χ 26
      rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h26_eq_9]
    · show χ 26 = χ (26 + 15)
      rw [show (26 + 15 : ℕ) = 41 by decide, h26_eq_9, ← h41_eq_9]
  have h26_ne_12 : χ 26 ≠ χ 12 := by
    intro h26_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 24
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 2)
      rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_12, h26_eq_12]
  have h26_eq_16 : χ 26 = χ 16 :=
    third_color_eq hχ26 hχ16 hχ9 hχ12 h9_ne_12 h26_ne_9 h26_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S3: χ(34) = χ(9) (A). Via (32, 26, 34) ≠ C + (24, 28, 34) ≠ B.
  have h34_ne_16 : χ 34 ≠ χ 16 := by
    intro h34_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 26) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 26
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h26_eq_16]
    · show χ 26 = χ (26 + 8)
      rw [show (26 + 8 : ℕ) = 34 by decide, h26_eq_16, h34_eq_16]
  have h34_ne_12 : χ 34 ≠ χ 12 := by
    intro h34_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 28
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_12.trans h28_eq_12.symm
    · show χ 28 = χ (28 + 6)
      rw [show (28 + 6 : ℕ) = 34 by decide, h28_eq_12, h34_eq_12]
  have h34_eq_9 : χ 34 = χ 9 :=
    third_color_eq hχ34 hχ9 hχ12 hχ16 h12_ne_16 h34_ne_12 h34_ne_16 h9_ne_12 h9_ne_16
  -- S4: χ(49) = χ(9) (A). Via (16, 45, 49) ≠ C + (36, 40, 49) ≠ B.
  have h49_ne_16 : χ 49 ≠ χ 16 := by
    intro h49_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 45) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 45
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h45_eq_16.symm
    · show χ 45 = χ (45 + 4)
      rw [show (45 + 4 : ℕ) = 49 by decide, h45_eq_16, h49_eq_16]
  have h49_ne_12 : χ 49 ≠ χ 12 := by
    intro h49_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 40) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 40
      rw [show (4 * 9 : ℕ) = 36 by decide]; exact h36_eq_12.trans h40_eq_12.symm
    · show χ 40 = χ (40 + 9)
      rw [show (40 + 9 : ℕ) = 49 by decide, h40_eq_12, h49_eq_12]
  have h49_eq_9 : χ 49 = χ 9 :=
    third_color_eq hχ49 hχ9 hχ12 hχ16 h12_ne_16 h49_ne_12 h49_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (60, 34, 49) mono with χ(60) = χ(34) = χ(49) = χ(9) (all A).
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 15) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 15) = χ 34
    rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h34_eq_9]
  · show χ 34 = χ (34 + 15)
    rw [show (34 + 15 : ℕ) = 49 by decide, h34_eq_9, ← h49_eq_9]

/-- ** contrapositive**: χ(60) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi60_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 60 ≠ χ 9 := by
  intro h60_eq_9
  exact residual_cell_1_chi60_eq_chi9_forces_False_short χ h60 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h60_eq_9

/-- ** layer compression d=15**: χ(60) ∈ {χ(12), χ(16)} under cell (1).
  Feeds bridge as the d=15 hLayer case. -/
theorem residual_cell_1_layer_compression_d15
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 60 = χ 12 ∨ χ 60 = χ 16 := by
  have h60_ne_9 : χ 60 ≠ χ 9 :=
    residual_cell_1_chi60_ne_chi9 χ h60 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ60 : χ 60 < 3 := hχk 60 (by omega) (by omega)
  by_cases h_eq_12 : χ 60 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ60 hχ16 hχ9 hχ12 h9_ne_12 h60_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §112. — d = 16 closure for residual cell (1).

  **Target.** Under residual cell (1) hypotheses, mono-free `bAdicEquation 4`
  at n ≥ 64, prove χ(64) ∈ {χ(12), χ(16)}. Closes the final piece of the
  cell (1) hLayer table — all 16 layers now sealed.

  **Geometry.** Unlike d = 15, (64, 9, 25) is *usable* because χ(25) is not
  pinned. The trick: (64, 9, 25) under χ(64) = A forces χ(25) = C
  (not A!), which seeds an alternating chain through χ(17), χ(33), χ(21),
  ultimately leaving χ(37) with no valid colour.

  **4-step cascade + no-colour-left terminal.**

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = χ(12) | + (16, 16, 20) |
  | P2 | χ(32) = χ(16) | + (32, 4, 12) |
  | P3 | χ(24) = χ(12) | + self-loop m = 8 |
  | P4 | χ(36) = χ(12) | + (16, 32, 36) |
  | 1 | χ(25) = χ(16) | (64, 9, 25) + (4, 24, 25) |
  | 2 | χ(17) = χ(9) | (32, 17, 25) + (20, 12, 17) |
  | 3 | χ(33) = χ(16) | (64, 17, 33) + (36, 24, 33) |
  | 4 | χ(21) = χ(9) | (16, 21, 25) + (4, 20, 21) |
  | T | **χ(37) ∉ {A, B, C}** | (64, 21, 37) + (4, 36, 37) + (16, 33, 37) |

  Terminal: χ(37) ≠ χ(9), χ(37) ≠ χ(12), χ(37) ≠ χ(16) but χ(37) < 3 and
  the three known colours are pairwise distinct — contradiction.

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - (16, 32, 36): 16 + 128 = 144 = 4·36 ✓
  - (64, 9, 25): 64 + 36 = 100 = 4·25 ✓
  - (4, 24, 25): 4 + 96 = 100 ✓
  - (32, 17, 25): 32 + 68 = 100 ✓
  - (20, 12, 17): 20 + 48 = 68 = 4·17 ✓
  - (64, 17, 33): 64 + 68 = 132 = 4·33 ✓
  - (36, 24, 33): 36 + 96 = 132 ✓
  - (16, 21, 25): 16 + 84 = 100 ✓
  - (4, 20, 21): 4 + 80 = 84 = 4·21 ✓
  - (64, 21, 37): 64 + 84 = 148 = 4·37 ✓
  - (4, 36, 37): 4 + 144 = 148 ✓
  - (16, 33, 37): 16 + 132 = 148 ✓ (TERMINAL — combined with prior two: χ(37) ∉ {A,B,C})
-/

set_option maxHeartbeats 1600000 in
/-- ** chi(64) = chi(9) closure**: residual cell (1) + χ(64) = χ(9) ⟹
  False at n ≥ 64. 4-step cascade ending in no-colour-left terminal on
  χ(37). Closes the final piece of cell (1) hLayer (d = 16). -/
theorem residual_cell_1_chi64_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12)
    (h64_eq_9 : χ 64 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have hχ33 : χ 33 < 3 := hχk 33 (by omega) (by omega)
  have hχ37 : χ 37 < 3 := hχk 37 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12). + (16, 16, 20).
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_1_chi20_ne_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 :=
    third_color_eq hχ20 hχ12 hχ9 hχ16 h9_ne_16 h20_ne_9 h20_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- PREAMBLE P2: χ(32) = χ(16). + (32, 4, 12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- PREAMBLE P3: χ(24) = χ(12). + self-loop m=8.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- PREAMBLE P4: χ(36) = χ(12). + (16, 32, 36).
  have h36_disj : χ 36 = χ 12 ∨ χ 36 = χ 16 :=
    residual_cell_1_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h36_ne_16 : χ 36 ≠ χ 16 := by
    intro h36_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 32
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h32_eq_16.symm
    · show χ 32 = χ (32 + 4)
      rw [show (32 + 4 : ℕ) = 36 by decide, h32_eq_16, ← h36_eq_16]
  have h36_eq_12 : χ 36 = χ 12 := h36_disj.resolve_right h36_ne_16
  -- MAIN CASCADE.
  -- S1: χ(25) = χ(16) (C). Via (64, 9, 25) ≠ A + (4, 24, 25) ≠ B.
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 9
      rw [show (4 * 16 : ℕ) = 64 by decide]; exact h64_eq_9
    · show χ 9 = χ (9 + 16)
      rw [show (9 + 16 : ℕ) = 25 by decide, h25_eq_9]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 24
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 1)
      rw [show (24 + 1 : ℕ) = 25 by decide, h24_eq_12, h25_eq_12]
  have h25_eq_16 : χ 25 = χ 16 :=
    third_color_eq hχ25 hχ16 hχ9 hχ12 h9_ne_12 h25_ne_9 h25_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(17) = χ(9) (A). Via (32, 17, 25) ≠ C + (20, 12, 17) ≠ B.
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 17
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h17_eq_16]
    · show χ 17 = χ (17 + 8)
      rw [show (17 + 8 : ℕ) = 25 by decide, h17_eq_16, ← h25_eq_16]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(33) = χ(16) (C). Via (64, 17, 33) ≠ A + (36, 24, 33) ≠ B.
  have h33_ne_9 : χ 33 ≠ χ 9 := by
    intro h33_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 17
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 16)
      rw [show (17 + 16 : ℕ) = 33 by decide, h17_eq_9, ← h33_eq_9]
  have h33_ne_12 : χ 33 ≠ χ 12 := by
    intro h33_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 24
      rw [show (4 * 9 : ℕ) = 36 by decide]; exact h36_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 9)
      rw [show (24 + 9 : ℕ) = 33 by decide, h24_eq_12, h33_eq_12]
  have h33_eq_16 : χ 33 = χ 16 :=
    third_color_eq hχ33 hχ16 hχ9 hχ12 h9_ne_12 h33_ne_9 h33_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(21) = χ(9) (A). Via (16, 21, 25) ≠ C + (4, 20, 21) ≠ B.
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 21
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h21_eq_16.symm
    · show χ 21 = χ (21 + 4)
      rw [show (21 + 4 : ℕ) = 25 by decide, h21_eq_16, ← h25_eq_16]
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  have h21_eq_9 : χ 21 = χ 9 :=
    third_color_eq hχ21 hχ9 hχ12 hχ16 h12_ne_16 h21_ne_12 h21_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: χ(37) has no valid color.
  have h37_ne_9 : χ 37 ≠ χ 9 := by
    intro h37_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 21
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h21_eq_9]
    · show χ 21 = χ (21 + 16)
      rw [show (21 + 16 : ℕ) = 37 by decide, h21_eq_9, ← h37_eq_9]
  have h37_ne_12 : χ 37 ≠ χ 12 := by
    intro h37_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 36) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 36
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h36_eq_12.symm
    · show χ 36 = χ (36 + 1)
      rw [show (36 + 1 : ℕ) = 37 by decide, h36_eq_12, h37_eq_12]
  have h37_ne_16 : χ 37 ≠ χ 16 := by
    intro h37_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 33) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 33
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h33_eq_16.symm
    · show χ 33 = χ (33 + 4)
      rw [show (33 + 4 : ℕ) = 37 by decide, h33_eq_16, h37_eq_16]
  have h37_eq_16 : χ 37 = χ 16 :=
    third_color_eq hχ37 hχ16 hχ9 hχ12 h9_ne_12 h37_ne_9 h37_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h37_ne_16 h37_eq_16

/-- ** contrapositive**: χ(64) ≠ χ(9) under cell (1) hypotheses. -/
theorem residual_cell_1_chi64_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 64 ≠ χ 9 := by
  intro h64_eq_9
  exact residual_cell_1_chi64_eq_chi9_forces_False_short χ h64 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12 h64_eq_9

/-- ** layer compression d=16**: χ(64) ∈ {χ(12), χ(16)} under cell (1).
  **Completes the cell (1) hLayer table** — all 16 layers (d = 1..16) closed.
  Feeds bridge as the final d = 16 hLayer case. -/
theorem residual_cell_1_layer_compression_d16
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 64 = χ 12 ∨ χ 64 = χ 16 := by
  have h64_ne_9 : χ 64 ≠ χ 9 :=
    residual_cell_1_chi64_ne_chi9 χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ64 : χ 64 < 3 := hχk 64 (by omega) (by omega)
  by_cases h_eq_12 : χ 64 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ64 hχ16 hχ9 hχ12 h9_ne_12 h64_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-- ** bonus sharpening**: χ(64) = χ(12) under cell (1).
  After hLayer d=16 closure, the disjunction collapses to a single colour:
  self-loop m=12 + χ(36) = χ(12) ⟹ χ(48) = χ(16) (unconditional under preamble);
  then self-loop m=16 + χ(48) = χ(16) ⟹ χ(64) ≠ χ(16);
  combined with d=16 disjunction: χ(64) = χ(12). -/
theorem residual_cell_1_chi64_eq_chi12
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 64 = χ 12 := by
  have hd16 : χ 64 = χ 12 ∨ χ 64 = χ 16 :=
    residual_cell_1_layer_compression_d16 χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  -- Sharpen χ(48) = χ(16): + self-loop m=12 + χ(36)=χ(12).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  have h36_disj : χ 36 = χ 12 ∨ χ 36 = χ 16 :=
    residual_cell_1_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h36_ne_16 : χ 36 ≠ χ 16 := by
    intro h36_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 32
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h32_eq_16.symm
    · show χ 32 = χ (32 + 4)
      rw [show (32 + 4 : ℕ) = 36 by decide, h32_eq_16, ← h36_eq_16]
  have h36_eq_12 : χ 36 = χ 12 := h36_disj.resolve_right h36_ne_16
  have h48_disj : χ 48 = χ 12 ∨ χ 48 = χ 16 :=
    residual_cell_1_layer_compression_d12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
  have h48_ne_12 : χ 48 ≠ χ 12 := by
    intro h48_eq_12
    -- Self-loop m=12: χ(36) ≠ χ(48). Under χ(48)=χ(12) and χ(36)=χ(12), contradiction.
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 12) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 12) = χ (4 * 12)
    rw [show ((4 - 1) * 12 : ℕ) = 36 by decide,
        show ((4 : ℕ) * 12) = 48 by decide, h36_eq_12, h48_eq_12]
  have h48_eq_16 : χ 48 = χ 16 := h48_disj.resolve_left h48_ne_12
  -- Self-loop m=16: χ(48) ≠ χ(64). Under χ(48)=χ(16): χ(64) ≠ χ(16).
  have h64_ne_16 : χ 64 ≠ χ 16 := by
    intro h64_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 16) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 16) = χ (4 * 16)
    rw [show ((4 - 1) * 16 : ℕ) = 48 by decide,
        show ((4 : ℕ) * 16) = 64 by decide, h48_eq_16, h64_eq_16]
  exact hd16.resolve_right h64_ne_16

/-! ### §113. — full hLayer assembly for residual cell (1).

  **Target.** Integrate all 16 d-layer compression theorems (- +
  base cases) into the exact hLayer shape required by :
  ```
  ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16
  ```

  Then apply `scale4_two_color_subcoloring_lifts_mono_solution` (
  bridge) to derive False directly from residual cell (1) hypotheses,
  completing the cell (1) closure.

  **No new arithmetic** — this is pure integration. Each d case dispatches
  to the corresponding R26X/R27X helper or base case.
-/

/-- ** full layer compression for cell (1)**: under residual cell (1)
  hypotheses, all 16 multiples-of-4 positions χ(4d) for d ∈ [1, 16] lie
  in {χ(12), χ(16)}. This is the exact hLayer hypothesis required by. -/
theorem residual_cell_1_full_layer_compression
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16 := by
  intro d hd1 hd16
  interval_cases d
  · -- d = 1: χ(4) = χ(12) by h4_eq_12.
    exact Or.inl (show χ (4 * 1) = χ 12 by rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12)
  · -- d = 2: χ(8) = χ(12) by h8_eq_12.
    exact Or.inl (show χ (4 * 2) = χ 12 by rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12)
  · -- d = 3: χ(12) = χ(12) by rfl.
    exact Or.inl (show χ (4 * 3) = χ 12 by rw [show (4 * 3 : ℕ) = 12 by decide])
  · -- d = 4: χ(16) = χ(16) by rfl.
    exact Or.inr (show χ (4 * 4) = χ 16 by rw [show (4 * 4 : ℕ) = 16 by decide])
  · -- d = 5:.
    have h := residual_cell_1_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 5 : ℕ) = 20 by decide]; exact h
  · -- d = 6:.
    have h := residual_cell_1_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 6 : ℕ) = 24 by decide]; exact h
  · -- d = 7:.
    have h := residual_cell_1_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 7 : ℕ) = 28 by decide]; exact h
  · -- d = 8:.
    have h := residual_cell_1_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 8 : ℕ) = 32 by decide]; exact h
  · -- d = 9:.
    have h := residual_cell_1_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 9 : ℕ) = 36 by decide]; exact h
  · -- d = 10:.
    have h := residual_cell_1_layer_compression_d10 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 10 : ℕ) = 40 by decide]; exact h
  · -- d = 11:.
    have h := residual_cell_1_layer_compression_d11 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 11 : ℕ) = 44 by decide]; exact h
  · -- d = 12:.
    have h := residual_cell_1_layer_compression_d12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 12 : ℕ) = 48 by decide]; exact h
  · -- d = 13:.
    have h := residual_cell_1_layer_compression_d13 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 13 : ℕ) = 52 by decide]; exact h
  · -- d = 14:.
    have h := residual_cell_1_layer_compression_d14 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 14 : ℕ) = 56 by decide]; exact h
  · -- d = 15:.
    have h := residual_cell_1_layer_compression_d15 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 15 : ℕ) = 60 by decide]; exact h
  · -- d = 16:.
    have h := residual_cell_1_layer_compression_d16 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    rw [show (4 * 16 : ℕ) = 64 by decide]; exact h

/-! ### §114. — residual cell (2) hLayer d = 5.

  **Cell (2) hypotheses** (from §95 docstring):
  - χ(8) = χ(12) = B (left anchor: B-pair at 8 and 12)
  - χ(4) = χ(16) = C (right anchor: C-pair at 4 and 16)

  ** hLayer target** {χ(12), χ(16)} still applies:
  - d=1: χ(4) = χ(16) ✓ (right branch)
  - d=2: χ(8) = χ(12) ✓ (left branch)
  - d=3: χ(12) = χ(12) ✓
  - d=4: χ(16) = χ(16) ✓

  **3-step cascade** (much shorter than cell (1)'s 4-step):

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(5) = χ(9) (A) | (12, 5, 8) [≠B] + (4, 4, 5) [≠C] |
  | 2 | χ(10) = χ(16) (C) | (8, 8, 10) [≠B] + (20, 5, 10) [≠A] |
  | 3 | χ(14) = χ(9) (A) | (8, 12, 14) [≠B] + (16, 10, 14) [≠C] |
  | T | **(20, 9, 14) mono** | χ(20) = χ(9) = χ(14) = A |

  All triples verified for b=4 (x + 4y = 4z):
  - (12, 5, 8): 12 + 20 = 32 = 4·8 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (20, 5, 10): 20 + 20 = 40 ✓
  - (8, 12, 14): 8 + 48 = 56 = 4·14 ✓
  - (16, 10, 14): 16 + 40 = 56 ✓
  - (20, 9, 14): 20 + 36 = 56 ✓ (TERMINAL MONO with all A)
-/

set_option maxHeartbeats 400000 in
/-- ** chi(20) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(20) = χ(9) ⟹ False at n ≥ 20. 3-step cascade ending in terminal
  mono triple (20, 9, 14). Cell (2) hypotheses: χ(8)=χ(12) (B-pair) and
  χ(4)=χ(16) (C-pair). -/
theorem residual_cell_2_chi20_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h20_eq_9 : χ 20 = χ 9) :
    False := by
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- S1: χ(5) = χ(9) (A). Via (12, 5, 8) ≠ B + (4, 4, 5) ≠ C.
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 5
      rw [show (4 * 3 : ℕ) = 12 by decide, h5_eq_12]
    · show χ 5 = χ (5 + 3)
      rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]
  have h5_ne_16 : χ 5 ≠ χ 16 := by
    intro h5_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_16, h5_eq_16]
  have h5_eq_9 : χ 5 = χ 9 :=
    third_color_eq hχ5 hχ9 hχ12 hχ16 h12_ne_16 h5_ne_12 h5_ne_16 h9_ne_12 h9_ne_16
  -- S2: χ(10) = χ(16) (C). Via (8, 8, 10) ≠ B + (20, 5, 10) ≠ A.
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 5
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_9, ← h10_eq_9]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S3: χ(14) = χ(9) (A). Via (8, 12, 14) ≠ B + (16, 10, 14) ≠ C.
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 10
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h10_eq_16.symm
    · show χ 10 = χ (10 + 4)
      rw [show (10 + 4 : ℕ) = 14 by decide, h10_eq_16, h14_eq_16]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ12 hχ16 h12_ne_16 h14_ne_12 h14_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (20, 9, 14) mono with χ(20) = χ(9) = χ(14) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 5) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 5) = χ 9
    rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_9
  · show χ 9 = χ (9 + 5)
    rw [show (9 + 5 : ℕ) = 14 by decide, ← h14_eq_9]

/-- ** contrapositive** (cell 2): χ(20) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi20_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 20 ≠ χ 9 := by
  intro h20_eq_9
  exact residual_cell_2_chi20_eq_chi9_forces_False_short χ h20 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h20_eq_9

/-- ** layer compression d=5 (cell 2)**: χ(20) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=5 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d5
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 20 = χ 12 ∨ χ 20 = χ 16 := by
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_2_chi20_ne_chi9 χ h20 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  by_cases h_eq_12 : χ 20 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ20 hχ16 hχ9 hχ12 h9_ne_12 h20_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §115. — residual cell (2) hLayer d = 6.

  **Target.** Under cell (2) hypotheses (χ(4) = χ(16) = C, χ(8) = χ(12) = B),
  mono-free `bAdicEquation 4` at n ≥ 24, prove χ(24) ∈ {χ(12), χ(16)}.

  **2-step cascade + no-colour-left terminal**:

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(5) = χ(9) (A) | (12, 5, 8) [≠B] + (4, 4, 5) [≠C] (UNCONDITIONAL) |
  | 2 | χ(11) = χ(16) (C) | (24, 5, 11) [≠A] + (12, 8, 11) [≠B] |
  | T | **χ(15) ∉ {A, B, C}** | (24, 9, 15) [≠A] + (12, 12, 15) [≠B] + (16, 11, 15) [≠C] |

  All triples verified for b=4 (x + 4y = 4z):
  - (12, 5, 8): 12 + 20 = 32 = 4·8 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (24, 5, 11): 24 + 20 = 44 = 4·11 ✓
  - (12, 8, 11): 12 + 32 = 44 ✓
  - (24, 9, 15): 24 + 36 = 60 = 4·15 ✓
  - (12, 12, 15): 12 + 48 = 60 ✓
  - (16, 11, 15): 16 + 44 = 60 ✓ (TERMINAL — combined with prior two: χ(15) ∉ {A,B,C})
-/

set_option maxHeartbeats 400000 in
/-- ** chi(24) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(24) = χ(9) ⟹ False at n ≥ 24. 2-step cascade ending in no-colour-left
  terminal on χ(15). -/
theorem residual_cell_2_chi24_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h24_eq_9 : χ 24 = χ 9) :
    False := by
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- S1: χ(5) = χ(9) (A). UNCONDITIONAL via (12, 5, 8) ≠ B + (4, 4, 5) ≠ C.
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 5
      rw [show (4 * 3 : ℕ) = 12 by decide, h5_eq_12]
    · show χ 5 = χ (5 + 3)
      rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]
  have h5_ne_16 : χ 5 ≠ χ 16 := by
    intro h5_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_16, h5_eq_16]
  have h5_eq_9 : χ 5 = χ 9 :=
    third_color_eq hχ5 hχ9 hχ12 hχ16 h12_ne_16 h5_ne_12 h5_ne_16 h9_ne_12 h9_ne_16
  -- S2: χ(11) = χ(16) (C). Via (24, 5, 11) ≠ A + (12, 8, 11) ≠ B.
  have h11_ne_9 : χ 11 ≠ χ 9 := by
    intro h11_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 5
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 6)
      rw [show (5 + 6 : ℕ) = 11 by decide, h5_eq_9, ← h11_eq_9]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_16 : χ 11 = χ 16 :=
    third_color_eq hχ11 hχ16 hχ9 hχ12 h9_ne_12 h11_ne_9 h11_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: χ(15) has no valid color.
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 9
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_9
    · show χ 9 = χ (9 + 6)
      rw [show (9 + 6 : ℕ) = 15 by decide, h15_eq_9]
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_ne_16 : χ 15 ≠ χ 16 := by
    intro h15_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, h15_eq_16]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h15_ne_16 h15_eq_16

/-- ** contrapositive** (cell 2): χ(24) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi24_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 24 ≠ χ 9 := by
  intro h24_eq_9
  exact residual_cell_2_chi24_eq_chi9_forces_False_short χ h24 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h24_eq_9

/-- ** layer compression d=6 (cell 2)**: χ(24) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=6 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 24 = χ 12 ∨ χ 24 = χ 16 := by
  have h24_ne_9 : χ 24 ≠ χ 9 :=
    residual_cell_2_chi24_ne_chi9 χ h24 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  by_cases h_eq_12 : χ 24 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §116. — residual cell (2) hLayer d = 7.

  **Target.** Under cell (2) hypotheses, prove χ(28) ∈ {χ(12), χ(16)}.

  **Unconditional preamble under cell (2)** (3 anchors):
  - P1: χ(20) = B via + (16, 16, 20) [(16,16,20) gives χ(20) ≠ C]
  - P2: χ(17) = A via (4, 16, 17) + (20, 12, 17) [(4,16,17) gives χ(17) ≠ C using χ(4)=χ(16)=C]
  - P3: χ(15) = A via (4, 15, 16) + (12, 12, 15) [(4,15,16) gives χ(15) ≠ C]

  **4-step cascade under χ(28) = A:**

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(10) = C | (28, 10, 17) [≠A] + (8, 8, 10) [≠B] |
  | 2 | χ(11) = A | (4, 10, 11) [≠C] + (12, 8, 11) [≠B] |
  | 3 | χ(18) = C | (28, 11, 18) [≠A] + (8, 18, 20) [≠B] |
  | 4 | χ(22) = A | (16, 18, 22) [≠C] + (8, 20, 22) [≠B] |
  | T | **(28, 15, 22) mono** | χ(28) = χ(15) = χ(22) = A |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (4, 16, 17): 4 + 64 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (4, 15, 16): 4 + 60 = 64 = 4·16 ✓
  - (12, 12, 15): 12 + 48 = 60 = 4·15 ✓
  - (8, 8, 10): 8 + 32 = 40 = 4·10 ✓
  - (28, 10, 17): 28 + 40 = 68 = 4·17 ✓
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓
  - (4, 10, 11): 4 + 40 = 44 ✓
  - (8, 18, 20): 8 + 72 = 80 ✓
  - (28, 11, 18): 28 + 44 = 72 = 4·18 ✓
  - (8, 20, 22): 8 + 80 = 88 = 4·22 ✓
  - (16, 18, 22): 16 + 72 = 88 ✓
  - (28, 15, 22): 28 + 60 = 88 ✓ (TERMINAL MONO with all A)
-/

set_option maxHeartbeats 800000 in
/-- ** chi(28) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(28) = χ(9) ⟹ False at n ≥ 28. 3-anchor unconditional preamble + 4-step
  cascade ending in terminal mono triple (28, 15, 22) under colour A. -/
theorem residual_cell_2_chi28_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h28 : 28 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h28_eq_9 : χ 28 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  -- PREAMBLE P1: χ(20) = χ(12) (B). + (16, 16, 20).
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_2_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 := h20_disj.resolve_right h20_ne_16
  -- PREAMBLE P2: χ(17) = χ(9) (A). (4, 16, 17) ≠ C + (20, 12, 17) ≠ B.
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 16
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16
    · show χ 16 = χ (16 + 1)
      rw [show (16 + 1 : ℕ) = 17 by decide, h17_eq_16]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
  -- PREAMBLE P3: χ(15) = χ(9) (A). (4, 15, 16) ≠ C + (12, 12, 15) ≠ B.
  have h15_ne_16 : χ 15 ≠ χ 16 := by
    intro h15_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 15
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h15_eq_16.symm
    · show χ 15 = χ (15 + 1)
      rw [show (15 + 1 : ℕ) = 16 by decide]; exact h15_eq_16
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_eq_9 : χ 15 = χ 9 :=
    third_color_eq hχ15 hχ9 hχ12 hχ16 h12_ne_16 h15_ne_12 h15_ne_16 h9_ne_12 h9_ne_16
  -- S1: χ(10) = χ(16) (C). Via (28, 10, 17) ≠ A + (8, 8, 10) ≠ B.
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 10
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h10_eq_9]
    · show χ 10 = χ (10 + 7)
      rw [show (10 + 7 : ℕ) = 17 by decide, h10_eq_9, ← h17_eq_9]
  have h10_ne_12 : χ 10 ≠ χ 12 := by
    intro h10_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_12, h10_eq_12]
  have h10_eq_16 : χ 10 = χ 16 :=
    third_color_eq hχ10 hχ16 hχ9 hχ12 h9_ne_12 h10_ne_9 h10_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(11) = χ(9) (A). Via (4, 10, 11) ≠ C + (12, 8, 11) ≠ B.
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 10
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h10_eq_16.symm
    · show χ 10 = χ (10 + 1)
      rw [show (10 + 1 : ℕ) = 11 by decide, h10_eq_16, h11_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(18) = χ(16) (C). Via (28, 11, 18) ≠ A + (8, 18, 20) ≠ B.
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 11
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h11_eq_9]
    · show χ 11 = χ (11 + 7)
      rw [show (11 + 7 : ℕ) = 18 by decide, h11_eq_9, ← h18_eq_9]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 18
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_12, ← h20_eq_12]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(22) = χ(9) (A). Via (16, 18, 22) ≠ C + (8, 20, 22) ≠ B.
  have h22_ne_16 : χ 22 ≠ χ 16 := by
    intro h22_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 18
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h18_eq_16.symm
    · show χ 18 = χ (18 + 4)
      rw [show (18 + 4 : ℕ) = 22 by decide, h18_eq_16, h22_eq_16]
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 20
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_12, h22_eq_12]
  have h22_eq_9 : χ 22 = χ 9 :=
    third_color_eq hχ22 hχ9 hχ12 hχ16 h12_ne_16 h22_ne_12 h22_ne_16 h9_ne_12 h9_ne_16
  -- TERMINAL: (28, 15, 22) mono with χ(28) = χ(15) = χ(22) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 7) (y := 15) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 7) = χ 15
    rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h15_eq_9]
  · show χ 15 = χ (15 + 7)
    rw [show (15 + 7 : ℕ) = 22 by decide, h15_eq_9, ← h22_eq_9]

/-- ** contrapositive** (cell 2): χ(28) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi28_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h28 : 28 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 28 ≠ χ 9 := by
  intro h28_eq_9
  exact residual_cell_2_chi28_eq_chi9_forces_False_short χ h28 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h28_eq_9

/-- ** layer compression d=7 (cell 2)**: χ(28) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=7 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d7
    {n : ℕ} (χ : ℕ → ℕ) (h28 : 28 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 28 = χ 12 ∨ χ 28 = χ 16 := by
  have h28_ne_9 : χ 28 ≠ χ 9 :=
    residual_cell_2_chi28_ne_chi9 χ h28 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  by_cases h_eq_12 : χ 28 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ28 hχ16 hχ9 hχ12 h9_ne_12 h28_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §117. — residual cell (2) hLayer d = 8 + reusable anchor helpers.

  **Target.** Under cell (2) hypotheses, prove χ(32) ∈ {χ(12), χ(16)}.

  **Closure**: ONE-STEP via direct terminal mono (32, 9, 17), using the
  unconditional cell (2) anchor χ(17) = χ(9) = A. The simplest hLayer
  closure yet.

  Two reusable helpers are extracted for future cell (2) rounds:
  - `residual_cell_2_chi20_eq_chi12`: χ(20) = B, unconditional under cell (2).
  - `residual_cell_2_chi17_eq_chi9`: χ(17) = A, unconditional under cell (2).

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (4, 16, 17): 4 + 64 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (32, 9, 17): 32 + 36 = 68 ✓ (TERMINAL MONO with all A)
-/

/-- ** helper: χ(20) = χ(12) unconditional under cell (2)**.
   (`residual_cell_2_layer_compression_d5`) gives χ(20) ∈ {χ(12), χ(16)}.
  Self-anchor triple (16, 16, 20) forces χ(20) ≠ χ(16), so χ(20) = χ(12). -/
theorem residual_cell_2_chi20_eq_chi12
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 20 = χ 12 := by
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_2_layer_compression_d5 χ h20 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  exact h20_disj.resolve_right h20_ne_16

/-- ** helper: χ(17) = χ(9) unconditional under cell (2)**.
  (4, 16, 17) forces χ(17) ≠ C (via χ(4) = χ(16) = C anchor pair).
  (20, 12, 17) forces χ(17) ≠ B (uses χ(20) = B from helper).
  third_color_eq gives χ(17) = χ(9). -/
theorem residual_cell_2_chi17_eq_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 17 = χ 9 := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ h20 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 16
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16
    · show χ 16 = χ (16 + 1)
      rw [show (16 + 1 : ℕ) = 17 by decide, h17_eq_16]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  exact third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16

/-- ** chi(32) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(32) = χ(9) ⟹ False at n ≥ 32. ONE-STEP via terminal mono (32, 9, 17)
  using unconditional χ(17) = A helper. -/
theorem residual_cell_2_chi32_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h32_eq_9 : χ 32 = χ 9) :
    False := by
  have h17_eq_9 : χ 17 = χ 9 :=
    residual_cell_2_chi17_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- TERMINAL: (32, 9, 17) mono with χ(32) = χ(9) = χ(17) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 9
    rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
  · show χ 9 = χ (9 + 8)
    rw [show (9 + 8 : ℕ) = 17 by decide, ← h17_eq_9]

/-- ** contrapositive** (cell 2): χ(32) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi32_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 32 ≠ χ 9 := by
  intro h32_eq_9
  exact residual_cell_2_chi32_eq_chi9_forces_False_short χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h32_eq_9

/-- ** layer compression d=8 (cell 2)**: χ(32) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=8 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d8
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 32 = χ 12 ∨ χ 32 = χ 16 := by
  have h32_ne_9 : χ 32 ≠ χ 9 :=
    residual_cell_2_chi32_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  by_cases h_eq_12 : χ 32 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ32 hχ16 hχ9 hχ12 h9_ne_12 h32_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §118. — residual cell (2) hLayer d = 9 + chi(5)=chi(9) helper.

  **Target.** Under cell (2) hypotheses, prove χ(36) ∈ {χ(12), χ(16)}.

  **2-step cascade + terminal mono (16, 14, 18) all C**:

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | H | χ(5) = χ(9) (A) | (12, 5, 8) [≠B] + (4, 4, 5) [≠C] (HELPER, UNCONDITIONAL) |
  | 1 | χ(14) = χ(16) (C) | (36, 5, 14) [≠A] + (8, 12, 14) [≠B] |
  | 2 | χ(18) = χ(16) (C) | (36, 9, 18) [≠A] + (8, 18, 20) [≠B] |
  | T | **(16, 14, 18) mono** | χ(16) = χ(14) = χ(18) = C |

  Uses helper `residual_cell_2_chi20_eq_chi12` for χ(20) = B in S2.

  All triples verified for b=4 (x + 4y = 4z):
  - (12, 5, 8): 12 + 20 = 32 = 4·8 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (36, 5, 14): 36 + 20 = 56 = 4·14 ✓
  - (8, 12, 14): 8 + 48 = 56 ✓
  - (36, 9, 18): 36 + 36 = 72 = 4·18 ✓
  - (8, 18, 20): 8 + 72 = 80 = 4·20 ✓
  - (16, 14, 18): 16 + 56 = 72 ✓ (TERMINAL MONO with all C)
-/

/-- ** helper: χ(5) = χ(9) unconditional under cell (2)**.
  (12, 5, 8) forces χ(5) ≠ B (via χ(12) = χ(8) = B anchor pair).
  (4, 4, 5) forces χ(5) ≠ C (via χ(4) = C self-mono).
  third_color_eq gives χ(5) = χ(9). Reusable in future cell (2) cascades. -/
theorem residual_cell_2_chi5_eq_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 5 = χ 9 := by
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 5
      rw [show (4 * 3 : ℕ) = 12 by decide, h5_eq_12]
    · show χ 5 = χ (5 + 3)
      rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]
  have h5_ne_16 : χ 5 ≠ χ 16 := by
    intro h5_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_16, h5_eq_16]
  exact third_color_eq hχ5 hχ9 hχ12 hχ16 h12_ne_16 h5_ne_12 h5_ne_16 h9_ne_12 h9_ne_16

set_option maxHeartbeats 400000 in
/-- ** chi(36) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(36) = χ(9) ⟹ False at n ≥ 36. 2-step cascade ending in terminal
  mono (16, 14, 18) under colour C. -/
theorem residual_cell_2_chi36_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h36_eq_9 : χ 36 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  -- Helpers from +.
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h5_eq_9 : χ 5 = χ 9 :=
    residual_cell_2_chi5_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- S1: χ(14) = χ(16) (C). Via (36, 5, 14) ≠ A + (8, 12, 14) ≠ B.
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 5
      rw [show (4 * 9 : ℕ) = 36 by decide, h36_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 9)
      rw [show (5 + 9 : ℕ) = 14 by decide, h5_eq_9, ← h14_eq_9]
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_eq_16 : χ 14 = χ 16 :=
    third_color_eq hχ14 hχ16 hχ9 hχ12 h9_ne_12 h14_ne_9 h14_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(18) = χ(16) (C). Via (36, 9, 18) ≠ A + (8, 18, 20) ≠ B.
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 9
      rw [show (4 * 9 : ℕ) = 36 by decide]; exact h36_eq_9
    · show χ 9 = χ (9 + 9)
      rw [show (9 + 9 : ℕ) = 18 by decide, h18_eq_9]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 18
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_12, ← h20_eq_12]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (16, 14, 18) mono with χ(16) = χ(14) = χ(18) = C.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 14
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h14_eq_16.symm
  · show χ 14 = χ (14 + 4)
    rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, ← h18_eq_16]

/-- ** contrapositive** (cell 2): χ(36) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi36_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 36 ≠ χ 9 := by
  intro h36_eq_9
  exact residual_cell_2_chi36_eq_chi9_forces_False_short χ h36 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h36_eq_9

/-- ** layer compression d=9 (cell 2)**: χ(36) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=9 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 36 = χ 12 ∨ χ 36 = χ 16 := by
  have h36_ne_9 : χ 36 ≠ χ 9 :=
    residual_cell_2_chi36_ne_chi9 χ h36 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  by_cases h_eq_12 : χ 36 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ36 hχ16 hχ9 hχ12 h9_ne_12 h36_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §119. — residual cell (2) hLayer d = 10 + chi(15)=chi(9) helper.

  **Target.** Under cell (2) hypotheses, prove χ(40) ∈ {χ(12), χ(16)}.

  **Closure**: ONE-STEP via terminal mono (40, 5, 15), using two unconditional
  cell (2) helpers: χ(5) = A () and χ(15) = A (NEW ).

  All triples verified for b=4 (x + 4y = 4z):
  - (4, 15, 16): 4 + 60 = 64 = 4·16 ✓
  - (12, 12, 15): 12 + 48 = 60 = 4·15 ✓
  - (40, 5, 15): 40 + 20 = 60 ✓ (TERMINAL MONO with all A)
-/

/-- ** helper: χ(15) = χ(9) unconditional under cell (2)**.
  (4, 15, 16) forces χ(15) ≠ C (via χ(4) = χ(16) = C anchor pair).
  (12, 12, 15) forces χ(15) ≠ B (via χ(12) = B self-mono).
  third_color_eq gives χ(15) = χ(9). Reusable in future cell (2) cascades. -/
theorem residual_cell_2_chi15_eq_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 15 = χ 9 := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have h15_ne_16 : χ 15 ≠ χ 16 := by
    intro h15_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 15
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h15_eq_16.symm
    · show χ 15 = χ (15 + 1)
      rw [show (15 + 1 : ℕ) = 16 by decide]; exact h15_eq_16
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  exact third_color_eq hχ15 hχ9 hχ12 hχ16 h12_ne_16 h15_ne_12 h15_ne_16 h9_ne_12 h9_ne_16

/-- ** chi(40) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(40) = χ(9) ⟹ False at n ≥ 40. ONE-STEP via terminal mono (40, 5, 15)
  using unconditional χ(5) = A and χ(15) = A helpers. -/
theorem residual_cell_2_chi40_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h40_eq_9 : χ 40 = χ 9) :
    False := by
  have h5_eq_9 : χ 5 = χ 9 :=
    residual_cell_2_chi5_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h15_eq_9 : χ 15 = χ 9 :=
    residual_cell_2_chi15_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- TERMINAL: (40, 5, 15) mono with χ(40) = χ(5) = χ(15) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 10) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 10) = χ 5
    rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h5_eq_9]
  · show χ 5 = χ (5 + 10)
    rw [show (5 + 10 : ℕ) = 15 by decide, h5_eq_9, ← h15_eq_9]

/-- ** contrapositive** (cell 2): χ(40) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi40_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 40 ≠ χ 9 := by
  intro h40_eq_9
  exact residual_cell_2_chi40_eq_chi9_forces_False_short χ h40 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h40_eq_9

/-- ** layer compression d=10 (cell 2)**: χ(40) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=10 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d10
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 40 = χ 12 ∨ χ 40 = χ 16 := by
  have h40_ne_9 : χ 40 ≠ χ 9 :=
    residual_cell_2_chi40_ne_chi9 χ h40 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ40 : χ 40 < 3 := hχk 40 (by omega) (by omega)
  by_cases h_eq_12 : χ 40 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ40 hχ16 hχ9 hχ12 h9_ne_12 h40_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §120. — residual cell (2) hLayer d = 11 + chi(3)=chi(9) helper.

  **Target.** Under cell (2) hypotheses, prove χ(44) ∈ {χ(12), χ(16)}.

  **8-step cascade + terminal mono (8, 26, 28) all B**.

  The first-strike pattern (44, 9, 20) fails because χ(20) = B fixed. Cell (2)
  needs an indirect chain through alternating positions, eventually forcing
  χ(26) = B and χ(28) = B (via / sharpening), giving B-mono (8, 26, 28).

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | H | χ(3) = A (UNCOND) | (4, 3, 4) [≠C] + (20, 3, 8) [≠B] (NEW HELPER) |
  | 1 | χ(14) = C | (44, 3, 14) [≠A] + (8, 12, 14) [≠B] |
  | 2 | χ(18) = A | (16, 14, 18) [≠C] + (8, 18, 20) [≠B] |
  | 3 | χ(7) = C | (44, 7, 18) [≠A] + (20, 7, 12) [≠B] |
  | 4 | χ(11) = A | (16, 7, 11) [≠C] + (12, 8, 11) [≠B] |
  | 5 | χ(22) = C | (44, 11, 22) [≠A] + (8, 20, 22) [≠B] |
  | 6 | χ(26) = B | (44, 15, 26) [≠A] + (16, 22, 26) [≠C] |
  | 7 | χ(24) = C | (8, 24, 26) [≠B] + |
  | 8 | χ(28) = B | (16, 24, 28) [≠C] + |
  | T | **(8, 26, 28) mono** | χ(8) = χ(26) = χ(28) = B |
-/

/-- ** helper: χ(3) = χ(9) unconditional under cell (2)**.
  (4, 3, 4) forces χ(3) ≠ C (via χ(4) = C self-mono).
  (20, 3, 8) forces χ(3) ≠ B (via χ(20) = χ(8) = B; uses helper).
  Reusable in future cell (2) cascades. -/
theorem residual_cell_2_chi3_eq_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 3 = χ 9 := by
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ h20 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h3_ne_16 : χ 3 ≠ χ 16 := by
    intro h3_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h3_eq_16.symm
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h3_eq_16, ← h4_eq_16]
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 3
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12.trans h3_eq_12.symm
    · show χ 3 = χ (3 + 5)
      rw [show (3 + 5 : ℕ) = 8 by decide, h3_eq_12, ← h8_eq_12]
  exact third_color_eq hχ3 hχ9 hχ12 hχ16 h12_ne_16 h3_ne_12 h3_ne_16 h9_ne_12 h9_ne_16

set_option maxHeartbeats 1600000 in
/-- ** chi(44) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(44) = χ(9) ⟹ False at n ≥ 44. 8-step cascade ending in terminal
  mono triple (8, 26, 28) under colour B. -/
theorem residual_cell_2_chi44_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h44_eq_9 : χ 44 = χ 9) :
    False := by
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ26 : χ 26 < 3 := hχk 26 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  -- Helpers.
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h3_eq_9 : χ 3 = χ 9 :=
    residual_cell_2_chi3_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h15_eq_9 : χ 15 = χ 9 :=
    residual_cell_2_chi15_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- S1: χ(14) = χ(16) (C).
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 3
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h3_eq_9]
    · show χ 3 = χ (3 + 11)
      rw [show (3 + 11 : ℕ) = 14 by decide, h3_eq_9, ← h14_eq_9]
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_eq_16 : χ 14 = χ 16 :=
    third_color_eq hχ14 hχ16 hχ9 hχ12 h9_ne_12 h14_ne_9 h14_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(18) = χ(9) (A).
  have h18_ne_16 : χ 18 ≠ χ 16 := by
    intro h18_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 14
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h14_eq_16.symm
    · show χ 14 = χ (14 + 4)
      rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, h18_eq_16]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 18
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_12, ← h20_eq_12]
  have h18_eq_9 : χ 18 = χ 9 :=
    third_color_eq hχ18 hχ9 hχ12 hχ16 h12_ne_16 h18_ne_12 h18_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(7) = χ(16) (C).
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 7
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h7_eq_9]
    · show χ 7 = χ (7 + 11)
      rw [show (7 + 11 : ℕ) = 18 by decide, h7_eq_9, ← h18_eq_9]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 7
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12.trans h7_eq_12.symm
    · show χ 7 = χ (7 + 5)
      rw [show (7 + 5 : ℕ) = 12 by decide]; exact h7_eq_12
  have h7_eq_16 : χ 7 = χ 16 :=
    third_color_eq hχ7 hχ16 hχ9 hχ12 h9_ne_12 h7_ne_9 h7_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(11) = χ(9) (A).
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 7
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h7_eq_16.symm
    · show χ 7 = χ (7 + 4)
      rw [show (7 + 4 : ℕ) = 11 by decide, h7_eq_16, h11_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(22) = χ(16) (C).
  have h22_ne_9 : χ 22 ≠ χ 9 := by
    intro h22_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 11
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h11_eq_9]
    · show χ 11 = χ (11 + 11)
      rw [show (11 + 11 : ℕ) = 22 by decide, h11_eq_9, ← h22_eq_9]
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 20
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_12, h22_eq_12]
  have h22_eq_16 : χ 22 = χ 16 :=
    third_color_eq hχ22 hχ16 hχ9 hχ12 h9_ne_12 h22_ne_9 h22_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S6: χ(26) = χ(12) (B).
  have h26_ne_9 : χ 26 ≠ χ 9 := by
    intro h26_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 11) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 11) = χ 15
      rw [show (4 * 11 : ℕ) = 44 by decide, h44_eq_9, ← h15_eq_9]
    · show χ 15 = χ (15 + 11)
      rw [show (15 + 11 : ℕ) = 26 by decide, h15_eq_9, ← h26_eq_9]
  have h26_ne_16 : χ 26 ≠ χ 16 := by
    intro h26_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 22
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h22_eq_16.symm
    · show χ 22 = χ (22 + 4)
      rw [show (22 + 4 : ℕ) = 26 by decide, h22_eq_16, h26_eq_16]
  have h26_eq_12 : χ 26 = χ 12 :=
    third_color_eq hχ26 hχ12 hχ9 hχ16 h9_ne_16 h26_ne_9 h26_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S7: χ(24) = χ(16) (C). Uses disjunction + (8, 24, 26) ≠ B.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_2_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h24_ne_12 : χ 24 ≠ χ 12 := by
    intro h24_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 24
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 2)
      rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_12, h26_eq_12]
  have h24_eq_16 : χ 24 = χ 16 := h24_disj.resolve_left h24_ne_12
  -- S8: χ(28) = χ(12) (B). Uses disjunction + (16, 24, 28) ≠ C.
  have h28_disj : χ 28 = χ 12 ∨ χ 28 = χ 16 :=
    residual_cell_2_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 24
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h24_eq_16.symm
    · show χ 24 = χ (24 + 4)
      rw [show (24 + 4 : ℕ) = 28 by decide, h24_eq_16, h28_eq_16]
  have h28_eq_12 : χ 28 = χ 12 := h28_disj.resolve_right h28_ne_16
  -- TERMINAL: (8, 26, 28) mono with χ(8) = χ(26) = χ(28) = B.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 26) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 2) = χ 26
    rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h26_eq_12.symm
  · show χ 26 = χ (26 + 2)
    rw [show (26 + 2 : ℕ) = 28 by decide, h26_eq_12, h28_eq_12]

/-- ** contrapositive** (cell 2): χ(44) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi44_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 44 ≠ χ 9 := by
  intro h44_eq_9
  exact residual_cell_2_chi44_eq_chi9_forces_False_short χ h44 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h44_eq_9

/-- ** layer compression d=11 (cell 2)**: χ(44) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=11 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d11
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 44 = χ 12 ∨ χ 44 = χ 16 := by
  have h44_ne_9 : χ 44 ≠ χ 9 :=
    residual_cell_2_chi44_ne_chi9 χ h44 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ44 : χ 44 < 3 := hχk 44 (by omega) (by omega)
  by_cases h_eq_12 : χ 44 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ44 hχ16 hχ9 hχ12 h9_ne_12 h44_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §121. — residual cell (2) hLayer d = 12.

  **Target.** Under cell (2) hypotheses, prove χ(48) ∈ {χ(12), χ(16)}.

  **Closure**: ONE-STEP via direct terminal mono (48, 3, 15) using
  existing helpers χ(3) = A () and χ(15) = A (). No new helper needed.

  Triple verified: (48, 3, 15): 48 + 12 = 60 = 4·15 ✓ (TERMINAL MONO with all A)
-/

/-- ** chi(48) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(48) = χ(9) ⟹ False at n ≥ 48. ONE-STEP via terminal mono (48, 3, 15)
  using existing helpers χ(3) = A () and χ(15) = A (). -/
theorem residual_cell_2_chi48_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h48_eq_9 : χ 48 = χ 9) :
    False := by
  have h3_eq_9 : χ 3 = χ 9 :=
    residual_cell_2_chi3_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h15_eq_9 : χ 15 = χ 9 :=
    residual_cell_2_chi15_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- TERMINAL: (48, 3, 15) mono with χ(48) = χ(3) = χ(15) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 3) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 12) = χ 3
    rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_9, ← h3_eq_9]
  · show χ 3 = χ (3 + 12)
    rw [show (3 + 12 : ℕ) = 15 by decide, h3_eq_9, ← h15_eq_9]

/-- ** contrapositive** (cell 2): χ(48) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi48_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 48 ≠ χ 9 := by
  intro h48_eq_9
  exact residual_cell_2_chi48_eq_chi9_forces_False_short χ h48 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h48_eq_9

/-- ** layer compression d=12 (cell 2)**: χ(48) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=12 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d12
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 48 = χ 12 ∨ χ 48 = χ 16 := by
  have h48_ne_9 : χ 48 ≠ χ 9 :=
    residual_cell_2_chi48_ne_chi9 χ h48 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ48 : χ 48 < 3 := hχk 48 (by omega) (by omega)
  by_cases h_eq_12 : χ 48 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ48 hχ16 hχ9 hχ12 h9_ne_12 h48_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §122. — residual cell (2) hLayer d = 13.

  **Target.** Under cell (2) hypotheses, prove χ(52) ∈ {χ(12), χ(16)}.

  **1-step cascade + no-colour-left terminal on χ(22)**:

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(18) = C | (52, 5, 18) [≠A; uses χ(5)=A] + (8, 18, 20) [≠B; uses χ(20)=B] |
  | T | **χ(22) ∉ {A, B, C}** | (52, 9, 22) [≠A] + (8, 20, 22) [≠B] + (16, 18, 22) [≠C; uses S1] |

  All triples verified for b=4 (x + 4y = 4z):
  - (52, 5, 18): 52 + 20 = 72 = 4·18 ✓
  - (8, 18, 20): 8 + 72 = 80 = 4·20 ✓
  - (52, 9, 22): 52 + 36 = 88 = 4·22 ✓
  - (8, 20, 22): 8 + 80 = 88 ✓
  - (16, 18, 22): 16 + 72 = 88 ✓ (TERMINAL — combined with prior two: χ(22) ∉ {A,B,C})
-/

set_option maxHeartbeats 400000 in
/-- ** chi(52) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(52) = χ(9) ⟹ False at n ≥ 52. 1-step cascade (χ(18) = C) + no-colour-left
  terminal on χ(22) via three triples excluding A, B, C. -/
theorem residual_cell_2_chi52_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h52_eq_9 : χ 52 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  -- Helpers.
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h5_eq_9 : χ 5 = χ 9 :=
    residual_cell_2_chi5_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- S1: χ(18) = χ(16) (C). Via (52, 5, 18) ≠ A + (8, 18, 20) ≠ B.
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 13) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 13) = χ 5
      rw [show (4 * 13 : ℕ) = 52 by decide, h52_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 13)
      rw [show (5 + 13 : ℕ) = 18 by decide, h5_eq_9, ← h18_eq_9]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 18
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_12, ← h20_eq_12]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: no-colour-left on χ(22).
  have h22_ne_9 : χ 22 ≠ χ 9 := by
    intro h22_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 13) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 13) = χ 9
      rw [show (4 * 13 : ℕ) = 52 by decide]; exact h52_eq_9
    · show χ 9 = χ (9 + 13)
      rw [show (9 + 13 : ℕ) = 22 by decide, h22_eq_9]
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 20
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_12, h22_eq_12]
  have h22_ne_16 : χ 22 ≠ χ 16 := by
    intro h22_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 18
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h18_eq_16.symm
    · show χ 18 = χ (18 + 4)
      rw [show (18 + 4 : ℕ) = 22 by decide, h18_eq_16, h22_eq_16]
  have h22_eq_16 : χ 22 = χ 16 :=
    third_color_eq hχ22 hχ16 hχ9 hχ12 h9_ne_12 h22_ne_9 h22_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h22_ne_16 h22_eq_16

/-- ** contrapositive** (cell 2): χ(52) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi52_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 52 ≠ χ 9 := by
  intro h52_eq_9
  exact residual_cell_2_chi52_eq_chi9_forces_False_short χ h52 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h52_eq_9

/-- ** layer compression d=13 (cell 2)**: χ(52) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=13 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d13
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 52 = χ 12 ∨ χ 52 = χ 16 := by
  have h52_ne_9 : χ 52 ≠ χ 9 :=
    residual_cell_2_chi52_ne_chi9 χ h52 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ52 : χ 52 < 3 := hχk 52 (by omega) (by omega)
  by_cases h_eq_12 : χ 52 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ52 hχ16 hχ9 hχ12 h9_ne_12 h52_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §123. — residual cell (2) hLayer d = 14.

  **Target.** Under cell (2) hypotheses, prove χ(56) ∈ {χ(12), χ(16)}.

  **Closure**: ONE-STEP via direct terminal mono (56, 3, 17) using existing
  helpers χ(3) = A () and χ(17) = A (). No new helper needed.

  Triple verified: (56, 3, 17): 56 + 12 = 68 = 4·17 ✓ (TERMINAL MONO with all A)
-/

/-- ** chi(56) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(56) = χ(9) ⟹ False at n ≥ 56. ONE-STEP via terminal mono (56, 3, 17)
  using existing helpers χ(3) = A () and χ(17) = A (). -/
theorem residual_cell_2_chi56_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h56_eq_9 : χ 56 = χ 9) :
    False := by
  have h3_eq_9 : χ 3 = χ 9 :=
    residual_cell_2_chi3_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h17_eq_9 : χ 17 = χ 9 :=
    residual_cell_2_chi17_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- TERMINAL: (56, 3, 17) mono with χ(56) = χ(3) = χ(17) = A.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 3) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 14) = χ 3
    rw [show (4 * 14 : ℕ) = 56 by decide, h56_eq_9, ← h3_eq_9]
  · show χ 3 = χ (3 + 14)
    rw [show (3 + 14 : ℕ) = 17 by decide, h3_eq_9, ← h17_eq_9]

/-- ** contrapositive** (cell 2): χ(56) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi56_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 56 ≠ χ 9 := by
  intro h56_eq_9
  exact residual_cell_2_chi56_eq_chi9_forces_False_short χ h56 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h56_eq_9

/-- ** layer compression d=14 (cell 2)**: χ(56) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=14 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d14
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 56 = χ 12 ∨ χ 56 = χ 16 := by
  have h56_ne_9 : χ 56 ≠ χ 9 :=
    residual_cell_2_chi56_ne_chi9 χ h56 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ56 : χ 56 < 3 := hχk 56 (by omega) (by omega)
  by_cases h_eq_12 : χ 56 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ56 hχ16 hχ9 hχ12 h9_ne_12 h56_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §124. — residual cell (2) hLayer d = 15.

  **Target.** Under cell (2) hypotheses, prove χ(60) ∈ {χ(12), χ(16)}.

  **7-step cascade + no-colour-left terminal on χ(30)**:

  | Step | Position | Triple(s) |
  |------|-----------|-----------|
  | 1 | χ(18) = C | (60, 3, 18) [≠A; χ(3)=A via ] + (8, 18, 20) [≠B; χ(20)=B via ] |
  | 2 | χ(14) = A | (8, 12, 14) [≠B] + (16, 14, 18) [≠C; uses S1] |
  | 3 | χ(22) = A | (8, 20, 22) [≠B] + (16, 18, 22) [≠C; uses S1] |
  | 4 | χ(7) = C | (20, 7, 12) [≠B] + (60, 7, 22) [≠A; uses S3] |
  | 5 | χ(11) = A | (12, 8, 11) [≠B] + (16, 7, 11) [≠C; uses S4] |
  | 6 | χ(24) = B | (24, 18, 24) [≠C; uses S1] + [χ(24) ∈ {B,C}] |
  | 7 | χ(26) = C | (60, 11, 26) [≠A; uses S5] + (8, 24, 26) [≠B; uses S6] |
  | T | **χ(30) no colour** | (60, 15, 30) [≠A; χ(15)=A via ] + (24, 24, 30) [≠B; uses S6] + (16, 26, 30) [≠C; uses S7] |

  All triples verified for b=4 (x + 4y = 4z):
  - (60, 3, 18): 60 + 12 = 72 = 4·18 ✓
  - (8, 18, 20): 8 + 72 = 80 = 4·20 ✓
  - (8, 12, 14): 8 + 48 = 56 = 4·14 ✓
  - (16, 14, 18): 16 + 56 = 72 = 4·18 ✓
  - (8, 20, 22): 8 + 80 = 88 = 4·22 ✓
  - (16, 18, 22): 16 + 72 = 88 = 4·22 ✓
  - (20, 7, 12): 20 + 28 = 48 = 4·12 ✓
  - (60, 7, 22): 60 + 28 = 88 = 4·22 ✓
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓
  - (16, 7, 11): 16 + 28 = 44 = 4·11 ✓
  - (24, 18, 24): 24 + 72 = 96 = 4·24 ✓ (degenerate: x = z)
  - (60, 11, 26): 60 + 44 = 104 = 4·26 ✓
  - (8, 24, 26): 8 + 96 = 104 = 4·26 ✓
  - (60, 15, 30): 60 + 60 = 120 = 4·30 ✓
  - (24, 24, 30): 24 + 96 = 120 = 4·30 ✓
  - (16, 26, 30): 16 + 104 = 120 = 4·30 ✓
-/

set_option maxHeartbeats 1600000 in
/-- ** chi(60) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(60) = χ(9) ⟹ False at n ≥ 60. 7-step cascade ending in no-colour-left
  terminal on χ(30). -/
theorem residual_cell_2_chi60_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h60_eq_9 : χ 60 = χ 9) :
    False := by
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ26 : χ 26 < 3 := hχk 26 (by omega) (by omega)
  have hχ30 : χ 30 < 3 := hχk 30 (by omega) (by omega)
  -- Helpers.
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h3_eq_9 : χ 3 = χ 9 :=
    residual_cell_2_chi3_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h15_eq_9 : χ 15 = χ 9 :=
    residual_cell_2_chi15_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- S1: χ(18) = χ(16) (C). (60, 3, 18) [≠A] + (8, 18, 20) [≠B].
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 15) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 15) = χ 3
      rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h3_eq_9]
    · show χ 3 = χ (3 + 15)
      rw [show (3 + 15 : ℕ) = 18 by decide, h3_eq_9, ← h18_eq_9]
  have h18_ne_12 : χ 18 ≠ χ 12 := by
    intro h18_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 18
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 2)
      rw [show (18 + 2 : ℕ) = 20 by decide, h18_eq_12, ← h20_eq_12]
  have h18_eq_16 : χ 18 = χ 16 :=
    third_color_eq hχ18 hχ16 hχ9 hχ12 h9_ne_12 h18_ne_9 h18_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(14) = χ(9) (A). (8, 12, 14) [≠B] + (16, 14, 18) [≠C].
  have h14_ne_12 : χ 14 ≠ χ 12 := by
    intro h14_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 12
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12
    · show χ 12 = χ (12 + 2)
      rw [show (12 + 2 : ℕ) = 14 by decide, h14_eq_12]
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 14
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h14_eq_16.symm
    · show χ 14 = χ (14 + 4)
      rw [show (14 + 4 : ℕ) = 18 by decide, h14_eq_16, h18_eq_16]
  have h14_eq_9 : χ 14 = χ 9 :=
    third_color_eq hχ14 hχ9 hχ12 hχ16 h12_ne_16 h14_ne_12 h14_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(22) = χ(9) (A). (8, 20, 22) [≠B] + (16, 18, 22) [≠C].
  have h22_ne_12 : χ 22 ≠ χ 12 := by
    intro h22_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 20
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 2)
      rw [show (20 + 2 : ℕ) = 22 by decide, h20_eq_12, h22_eq_12]
  have h22_ne_16 : χ 22 ≠ χ 16 := by
    intro h22_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 18
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h18_eq_16.symm
    · show χ 18 = χ (18 + 4)
      rw [show (18 + 4 : ℕ) = 22 by decide, h18_eq_16, h22_eq_16]
  have h22_eq_9 : χ 22 = χ 9 :=
    third_color_eq hχ22 hχ9 hχ12 hχ16 h12_ne_16 h22_ne_12 h22_ne_16 h9_ne_12 h9_ne_16
  -- S4: χ(7) = χ(16) (C). (20, 7, 12) [≠B] + (60, 7, 22) [≠A].
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 15) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 15) = χ 7
      rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h7_eq_9]
    · show χ 7 = χ (7 + 15)
      rw [show (7 + 15 : ℕ) = 22 by decide, h7_eq_9, ← h22_eq_9]
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 7
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12.trans h7_eq_12.symm
    · show χ 7 = χ (7 + 5)
      rw [show (7 + 5 : ℕ) = 12 by decide]; exact h7_eq_12
  have h7_eq_16 : χ 7 = χ 16 :=
    third_color_eq hχ7 hχ16 hχ9 hχ12 h9_ne_12 h7_ne_9 h7_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S5: χ(11) = χ(9) (A). (12, 8, 11) [≠B] + (16, 7, 11) [≠C].
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 8
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h8_eq_12.symm
    · show χ 8 = χ (8 + 3)
      rw [show (8 + 3 : ℕ) = 11 by decide, h8_eq_12, h11_eq_12]
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 7
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h7_eq_16.symm
    · show χ 7 = χ (7 + 4)
      rw [show (7 + 4 : ℕ) = 11 by decide, h7_eq_16, h11_eq_16]
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S6: χ(24) = χ(12) (B). [χ(24) ∈ {B,C}] + (24, 18, 24) [≠C].
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_2_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    -- (24, 18, 24): degenerate triple x=z=24. Mono iff χ(24)=χ(18)=C.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 18
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_16.trans h18_eq_16.symm
    · show χ 18 = χ (18 + 6)
      rw [show (18 + 6 : ℕ) = 24 by decide, h18_eq_16, h24_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- S7: χ(26) = χ(16) (C). (60, 11, 26) [≠A] + (8, 24, 26) [≠B].
  have h26_ne_9 : χ 26 ≠ χ 9 := by
    intro h26_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 15) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 15) = χ 11
      rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h11_eq_9]
    · show χ 11 = χ (11 + 15)
      rw [show (11 + 15 : ℕ) = 26 by decide, h11_eq_9, ← h26_eq_9]
  have h26_ne_12 : χ 26 ≠ χ 12 := by
    intro h26_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 24
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12.trans h24_eq_12.symm
    · show χ 24 = χ (24 + 2)
      rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_12, h26_eq_12]
  have h26_eq_16 : χ 26 = χ 16 :=
    third_color_eq hχ26 hχ16 hχ9 hχ12 h9_ne_12 h26_ne_9 h26_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: no-colour-left on χ(30).
  have h30_ne_9 : χ 30 ≠ χ 9 := by
    intro h30_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 15) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 15) = χ 15
      rw [show (4 * 15 : ℕ) = 60 by decide, h60_eq_9, ← h15_eq_9]
    · show χ 15 = χ (15 + 15)
      rw [show (15 + 15 : ℕ) = 30 by decide, h15_eq_9, ← h30_eq_9]
  have h30_ne_12 : χ 30 ≠ χ 12 := by
    intro h30_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 24
      rw [show (4 * 6 : ℕ) = 24 by decide]
    · show χ 24 = χ (24 + 6)
      rw [show (24 + 6 : ℕ) = 30 by decide, h24_eq_12, h30_eq_12]
  have h30_ne_16 : χ 30 ≠ χ 16 := by
    intro h30_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 26) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 26
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h26_eq_16.symm
    · show χ 26 = χ (26 + 4)
      rw [show (26 + 4 : ℕ) = 30 by decide, h26_eq_16, h30_eq_16]
  have h30_eq_16 : χ 30 = χ 16 :=
    third_color_eq hχ30 hχ16 hχ9 hχ12 h9_ne_12 h30_ne_9 h30_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  exact h30_ne_16 h30_eq_16

/-- ** contrapositive** (cell 2): χ(60) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi60_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 60 ≠ χ 9 := by
  intro h60_eq_9
  exact residual_cell_2_chi60_eq_chi9_forces_False_short χ h60 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h60_eq_9

/-- ** layer compression d=15 (cell 2)**: χ(60) ∈ {χ(12), χ(16)} under
  residual cell (2). Feeds bridge as the d=15 hLayer case for cell (2). -/
theorem residual_cell_2_layer_compression_d15
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 60 = χ 12 ∨ χ 60 = χ 16 := by
  have h60_ne_9 : χ 60 ≠ χ 9 :=
    residual_cell_2_chi60_ne_chi9 χ h60 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ60 : χ 60 < 3 := hχk 60 (by omega) (by omega)
  by_cases h_eq_12 : χ 60 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ60 hχ16 hχ9 hχ12 h9_ne_12 h60_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §125. — residual cell (2) hLayer d = 16 (final layer).

  **Target.** Under cell (2) hypotheses, mono-free `bAdicEquation 4` at
  n ≥ 64, prove χ(64) ∈ {χ(12), χ(16)}. Closes the cell (2) hLayer table.

  **6-step cascade + terminal MONO (12, 33, 36) all B.**

  Under h64_eq_9: χ(64) = A.

  | Step | Position | Triple(s) |
  |------|-----------|-----------|
  | S1 | χ(25) = C | (64, 9, 25) [≠A] + (20, 20, 25) [≠B; degenerate y=z] |
  | S2 | χ(24) = B | (4, 24, 25) [≠C; uses S1, χ(4)=χ(25)=C] + [χ(24)∈{B,C}] |
  | S3 | χ(21) = B | (64, 5, 21) [≠A; uses χ(5)=A ] + (16, 21, 25) [≠C; uses S1] |
  | S4 | χ(32) = C | self-loop m=8 [χ(24)≠χ(32); uses S2] + [χ(32)∈{B,C}] |
  | S5 | χ(33) = B | (64, 17, 33) [≠A; uses χ(17)=A helper] + (4, 32, 33) [≠C; uses S4] |
  | S6 | χ(36) = B | (16, 32, 36) [≠C; uses S4] + d9 [χ(36)∈{B,C}] |
  | T | **(12, 33, 36) mono** | χ(12) = χ(33) = χ(36) = B (uses S5, S6) |

  All triples verified for b=4 (x + 4y = 4z):
  - (64, 9, 25): 64 + 36 = 100 = 4·25 ✓
  - (20, 20, 25): 20 + 80 = 100 ✓ (degenerate y=z so self-mono if χ(20)=χ(25))
  - (4, 24, 25): 4 + 96 = 100 ✓
  - (64, 5, 21): 64 + 20 = 84 = 4·21 ✓
  - (16, 21, 25): 16 + 84 = 100 ✓
  - self-loop m=8: χ(24) ≠ χ(32) ✓
  - (64, 17, 33): 64 + 68 = 132 = 4·33 ✓
  - (4, 32, 33): 4 + 128 = 132 ✓
  - (16, 32, 36): 16 + 128 = 144 = 4·36 ✓
  - (12, 33, 36): 12 + 132 = 144 ✓ (TERMINAL MONO with all B)
-/

set_option maxHeartbeats 1600000 in
/-- ** chi(64) = chi(9) closure (cell 2)**: residual cell (2) +
  χ(64) = χ(9) ⟹ False at n ≥ 64. 6-step cascade ending in B-monochromatic
  terminal (12, 33, 36). Closes the final piece of cell (2) hLayer (d = 16). -/
theorem residual_cell_2_chi64_eq_chi9_forces_False_short
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12)
    (h64_eq_9 : χ 64 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  have hχ33 : χ 33 < 3 := hχk 33 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  -- Helpers.
  have h20_eq_12 : χ 20 = χ 12 :=
    residual_cell_2_chi20_eq_chi12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h5_eq_9 : χ 5 = χ 9 :=
    residual_cell_2_chi5_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h17_eq_9 : χ 17 = χ 9 :=
    residual_cell_2_chi17_eq_chi9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  -- S1: χ(25) = χ(16) (C). (64, 9, 25) [≠A] + (20, 20, 25) [≠B].
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 9
      rw [show (4 * 16 : ℕ) = 64 by decide]; exact h64_eq_9
    · show χ 9 = χ (9 + 16)
      rw [show (9 + 16 : ℕ) = 25 by decide, h25_eq_9]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 20
      rw [show (4 * 5 : ℕ) = 20 by decide]
    · show χ 20 = χ (20 + 5)
      rw [show (20 + 5 : ℕ) = 25 by decide, h20_eq_12, h25_eq_12]
  have h25_eq_16 : χ 25 = χ 16 :=
    third_color_eq hχ25 hχ16 hχ9 hχ12 h9_ne_12 h25_ne_9 h25_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(24) = χ(12) (B). (4, 24, 25) [≠C; uses S1] + [χ(24) ∈ {B,C}].
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_2_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 24
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h24_eq_16.symm
    · show χ 24 = χ (24 + 1)
      rw [show (24 + 1 : ℕ) = 25 by decide, h24_eq_16, ← h25_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- S3: χ(21) = χ(12) (B). (64, 5, 21) [≠A; uses χ(5)=A] + (16, 21, 25) [≠C; uses S1].
  have h21_ne_9 : χ 21 ≠ χ 9 := by
    intro h21_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 5
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 16)
      rw [show (5 + 16 : ℕ) = 21 by decide, h5_eq_9, ← h21_eq_9]
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 21
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h21_eq_16.symm
    · show χ 21 = χ (21 + 4)
      rw [show (21 + 4 : ℕ) = 25 by decide, h21_eq_16, ← h25_eq_16]
  have h21_eq_12 : χ 21 = χ 12 :=
    third_color_eq hχ21 hχ12 hχ9 hχ16 h9_ne_16 h21_ne_9 h21_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S4: χ(32) = χ(16) (C). self-loop m=8 [χ(24) ≠ χ(32)] + [χ(32) ∈ {B,C}].
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_2_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide, h24_eq_12, ← h32_eq_12]
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- S5: χ(33) = χ(12) (B). (64, 17, 33) [≠A; χ(17)=A] + (4, 32, 33) [≠C; uses S4].
  have h33_ne_9 : χ 33 ≠ χ 9 := by
    intro h33_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 17
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h17_eq_9]
    · show χ 17 = χ (17 + 16)
      rw [show (17 + 16 : ℕ) = 33 by decide, h17_eq_9, ← h33_eq_9]
  have h33_ne_16 : χ 33 ≠ χ 16 := by
    intro h33_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 32
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16.trans h32_eq_16.symm
    · show χ 32 = χ (32 + 1)
      rw [show (32 + 1 : ℕ) = 33 by decide, h32_eq_16, h33_eq_16]
  have h33_eq_12 : χ 33 = χ 12 :=
    third_color_eq hχ33 hχ12 hχ9 hχ16 h9_ne_16 h33_ne_9 h33_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S6: χ(36) = χ(12) (B). (16, 32, 36) [≠C; uses S4] + d9 [χ(36) ∈ {B,C}].
  have h36_disj : χ 36 = χ 12 ∨ χ 36 = χ 16 :=
    residual_cell_2_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have h36_ne_16 : χ 36 ≠ χ 16 := by
    intro h36_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 32) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 32
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h32_eq_16.symm
    · show χ 32 = χ (32 + 4)
      rw [show (32 + 4 : ℕ) = 36 by decide, h32_eq_16, h36_eq_16]
  have h36_eq_12 : χ 36 = χ 12 := h36_disj.resolve_right h36_ne_16
  -- TERMINAL: (12, 33, 36) mono with χ(12) = χ(33) = χ(36) = B.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 3) = χ 33
    rw [show (4 * 3 : ℕ) = 12 by decide]; exact h33_eq_12.symm
  · show χ 33 = χ (33 + 3)
    rw [show (33 + 3 : ℕ) = 36 by decide, h33_eq_12, h36_eq_12]

/-- ** contrapositive** (cell 2): χ(64) ≠ χ(9) under cell (2) hypotheses. -/
theorem residual_cell_2_chi64_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 64 ≠ χ 9 := by
  intro h64_eq_9
  exact residual_cell_2_chi64_eq_chi9_forces_False_short χ h64 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12 h64_eq_9

/-- ** layer compression d=16 (cell 2)**: χ(64) ∈ {χ(12), χ(16)} under
  residual cell (2). **Completes the cell (2) hLayer table** — all 16 layers
  (d = 1..16) closed. Feeds bridge as the final d = 16 hLayer case for
  cell (2). -/
theorem residual_cell_2_layer_compression_d16
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    χ 64 = χ 12 ∨ χ 64 = χ 16 := by
  have h64_ne_9 : χ 64 ≠ χ 9 :=
    residual_cell_2_chi64_ne_chi9 χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ64 : χ 64 < 3 := hχk 64 (by omega) (by omega)
  by_cases h_eq_12 : χ 64 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ64 hχ16 hχ9 hχ12 h9_ne_12 h64_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §126. — full hLayer assembly for residual cell (2).

  **Target.** Integrate all 16 d-layer compression theorems (- +
  - + base cases) into the exact hLayer shape required by :
  ```
  ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16
  ```

  No new arithmetic — pure integration via `interval_cases`. Each d case
  dispatches to the corresponding cell (2) lemma or base case.

  **Base layers** (from cell (2) hypotheses directly):
  - d=1: χ(4) = χ(16) via h4_eq_16 (right branch).
  - d=2: χ(8) = χ(12) via h8_eq_12 (left branch).
  - d=3: χ(12) = χ(12) by rfl (left branch).
  - d=4: χ(16) = χ(16) by rfl (right branch).
-/

/-- ** full layer compression for cell (2)**: under residual cell (2)
  hypotheses, all 16 multiples-of-4 positions χ(4d) for d ∈ [1, 16] lie
  in {χ(12), χ(16)}. This is the exact hLayer hypothesis required by. -/
theorem residual_cell_2_full_layer_compression
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16 := by
  intro d hd1 hd16
  interval_cases d
  · -- d = 1: χ(4) = χ(16) by h4_eq_16 (right branch).
    exact Or.inr (show χ (4 * 1) = χ 16 by rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_16)
  · -- d = 2: χ(8) = χ(12) by h8_eq_12 (left branch).
    exact Or.inl (show χ (4 * 2) = χ 12 by rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_12)
  · -- d = 3: χ(12) = χ(12) by rfl.
    exact Or.inl (show χ (4 * 3) = χ 12 by rw [show (4 * 3 : ℕ) = 12 by decide])
  · -- d = 4: χ(16) = χ(16) by rfl.
    exact Or.inr (show χ (4 * 4) = χ 16 by rw [show (4 * 4 : ℕ) = 16 by decide])
  · -- d = 5:.
    have h := residual_cell_2_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 5 : ℕ) = 20 by decide]; exact h
  · -- d = 6:.
    have h := residual_cell_2_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 6 : ℕ) = 24 by decide]; exact h
  · -- d = 7:.
    have h := residual_cell_2_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 7 : ℕ) = 28 by decide]; exact h
  · -- d = 8:.
    have h := residual_cell_2_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 8 : ℕ) = 32 by decide]; exact h
  · -- d = 9:.
    have h := residual_cell_2_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 9 : ℕ) = 36 by decide]; exact h
  · -- d = 10:.
    have h := residual_cell_2_layer_compression_d10 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 10 : ℕ) = 40 by decide]; exact h
  · -- d = 11:.
    have h := residual_cell_2_layer_compression_d11 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 11 : ℕ) = 44 by decide]; exact h
  · -- d = 12:.
    have h := residual_cell_2_layer_compression_d12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 12 : ℕ) = 48 by decide]; exact h
  · -- d = 13:.
    have h := residual_cell_2_layer_compression_d13 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 13 : ℕ) = 52 by decide]; exact h
  · -- d = 14:.
    have h := residual_cell_2_layer_compression_d14 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 14 : ℕ) = 56 by decide]; exact h
  · -- d = 15:.
    have h := residual_cell_2_layer_compression_d15 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 15 : ℕ) = 60 by decide]; exact h
  · -- d = 16:.
    have h := residual_cell_2_layer_compression_d16 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
    rw [show (4 * 16 : ℕ) = 64 by decide]; exact h

/-! ### §127. — residual cell (3) hLayer d = 5 — DELIVERABLE B (forced prefix).

  **Cell (3) hypotheses**:
  - h4_eq_12 : χ(4) = χ(12) = B
  - h8_eq_16 : χ(8) = χ(16) = C

  **Cell (3) vs cell (2)**: B↔C swap at positions 4 ↔ 8 (cell (2) had χ(4)=C, χ(8)=B).

  **Status**: Cell (3) d=5 is **NOT closeable at n ≥ 20** with current cascade.
  The §95 docstring notes cell (3) needs the (χ(11), χ(13)) = (A, A) sub-case,
  which cascades beyond n = 20. My analysis confirms: 8 positions force, but **no
  mono triple emerges in [1, 20]**, and sub-case (χ(5), χ(7)) = (A, C) admits a
  consistent partial assignment.

  **Deliverable B**: Forced-color prefix theorem documenting 8 forced positions
  under cell (3) + χ(20) = χ(9). Future rounds will continue the cascade at
  higher n thresholds (likely n ≥ 28-40 based on §95).

  **Forced positions** (all under cell (3) + χ(20) = χ(9)):
  - χ(15) = C via self-loop m=5 + (12, 12, 15)
  - χ(11) = A via (16, 11, 15) + (12, 8, 11) [unconditional, χ(11) ≠ B]
  - χ(14) = B via (20, 9, 14) + (8, 14, 16) [unconditional, χ(14) ≠ C]
  - χ(17) = A via (12, 14, 17) + (8, 15, 17)
  - χ(13) = A via (8, 13, 15) + (4, 12, 13) [unconditional, χ(13) ≠ B]
  - χ(18) = B via (20, 13, 18) + (8, 16, 18) [unconditional, χ(18) ≠ C]
  - χ(19) = A via (4, 18, 19) + (16, 15, 19)
  - χ(6) = B via (20, 6, 11) + (8, 6, 8) [unconditional, χ(6) ≠ C]

  All triples verified for b=4 (x + 4y = 4z):
  - (20, 15, 20): 20 + 60 = 80 = 4·20 ✓ (self-loop m=5: χ(15) ≠ χ(20))
  - (12, 12, 15): 12 + 48 = 60 = 4·15 ✓ (χ(15) ≠ B unconditional)
  - (16, 11, 15): 16 + 44 = 60 = 4·15 ✓
  - (12, 8, 11): 12 + 32 = 44 = 4·11 ✓ — wait, this is trivial in cell (3) since χ(12)=B, χ(8)=C
  Actually (12, 8, 11) is trivial. Correct unconditional: **(4, 11, 12)** uses χ(4) = χ(12) = B, gives χ(11) ≠ B.
  - (4, 11, 12): 4 + 44 = 48 = 4·12 ✓
  - (20, 9, 14): 20 + 36 = 56 = 4·14 ✓
  - (8, 14, 16): 8 + 56 = 64 = 4·16 ✓ (χ(14) ≠ C unconditional)
  - (12, 14, 17): 12 + 56 = 68 = 4·17 ✓
  - (8, 15, 17): 8 + 60 = 68 ✓
  - (8, 13, 15): 8 + 52 = 60 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓ (χ(13) ≠ B unconditional)
  - (20, 13, 18): 20 + 52 = 72 = 4·18 ✓
  - (8, 16, 18): 8 + 64 = 72 ✓ (χ(18) ≠ C unconditional)
  - (4, 18, 19): 4 + 72 = 76 = 4·19 ✓
  - (16, 15, 19): 16 + 60 = 76 ✓
  - (20, 6, 11): 20 + 24 = 44 = 4·11 ✓
  - (8, 6, 8): 8 + 24 = 32 = 4·8 ✓ (χ(6) ≠ C unconditional)
-/

set_option maxHeartbeats 800000 in
/-- ** cell (3) d=5 forced-color prefix** (Deliverable B): under cell (3)
  hypotheses + χ(20) = χ(9), the 8 positions {6, 11, 13, 14, 15, 17, 18, 19}
  are forced to specific colors. **No terminal mono emerges at n ≥ 20** —
  cell (3) d=5 closure requires higher threshold (matches §95 obstruction
  note). This theorem documents the forced prefix for future rounds. -/
theorem residual_cell_3_chi20_eq_chi9_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9) :
    χ 15 = χ 16 ∧ χ 11 = χ 9 ∧ χ 14 = χ 12 ∧
    χ 17 = χ 9 ∧ χ 13 = χ 9 ∧ χ 18 = χ 12 ∧
    χ 19 = χ 9 ∧ χ 6 = χ 12 := by
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ14 : χ 14 < 3 := hχk 14 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ19 : χ 19 < 3 := hχk 19 (by omega) (by omega)
  -- S1: χ(15) = χ(16) (C). Via self-loop m=5 + (12, 12, 15).
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 5) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 5) = χ (4 * 5)
    rw [show ((4 - 1) * 5 : ℕ) = 15 by decide,
        show ((4 : ℕ) * 5) = 20 by decide, h15_eq_9, ← h20_eq_9]
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(11) = χ(9) (A). Via (16, 11, 15) + (4, 11, 12).
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 11
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h11_eq_12.symm
    · show χ 11 = χ (11 + 1)
      rw [show (11 + 1 : ℕ) = 12 by decide]; exact h11_eq_12
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(14) = χ(12) (B). Via (20, 9, 14) + (8, 14, 16).
  have h14_ne_9 : χ 14 ≠ χ 9 := by
    intro h14_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 9
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_9
    · show χ 9 = χ (9 + 5)
      rw [show (9 + 5 : ℕ) = 14 by decide, h14_eq_9]
  have h14_ne_16 : χ 14 ≠ χ 16 := by
    intro h14_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 14
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16.trans h14_eq_16.symm
    · show χ 14 = χ (14 + 2)
      rw [show (14 + 2 : ℕ) = 16 by decide]; exact h14_eq_16
  have h14_eq_12 : χ 14 = χ 12 :=
    third_color_eq hχ14 hχ12 hχ9 hχ16 h9_ne_16 h14_ne_9 h14_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S4: χ(17) = χ(9) (A). Via (12, 14, 17) + (8, 15, 17).
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 14) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 14
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h14_eq_12.symm
    · show χ 14 = χ (14 + 3)
      rw [show (14 + 3 : ℕ) = 17 by decide, h14_eq_12, h17_eq_12]
  have h17_ne_16 : χ 17 ≠ χ 16 := by
    intro h17_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 15
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16.trans h15_eq_16.symm
    · show χ 15 = χ (15 + 2)
      rw [show (15 + 2 : ℕ) = 17 by decide, h15_eq_16, h17_eq_16]
  have h17_eq_9 : χ 17 = χ 9 :=
    third_color_eq hχ17 hχ9 hχ12 hχ16 h12_ne_16 h17_ne_12 h17_ne_16 h9_ne_12 h9_ne_16
  -- S5: χ(13) = χ(9) (A). Via (8, 13, 15) + (4, 12, 13).
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_ne_16 : χ 13 ≠ χ 16 := by
    intro h13_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 13
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16.trans h13_eq_16.symm
    · show χ 13 = χ (13 + 2)
      rw [show (13 + 2 : ℕ) = 15 by decide, h13_eq_16, ← h15_eq_16]
  have h13_eq_9 : χ 13 = χ 9 :=
    third_color_eq hχ13 hχ9 hχ12 hχ16 h12_ne_16 h13_ne_12 h13_ne_16 h9_ne_12 h9_ne_16
  -- S6: χ(18) = χ(12) (B). Via (20, 13, 18) + (8, 16, 18).
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 13
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 5)
      rw [show (13 + 5 : ℕ) = 18 by decide, h13_eq_9, ← h18_eq_9]
  have h18_ne_16 : χ 18 ≠ χ 16 := by
    intro h18_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 16
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16
    · show χ 16 = χ (16 + 2)
      rw [show (16 + 2 : ℕ) = 18 by decide, h18_eq_16]
  have h18_eq_12 : χ 18 = χ 12 :=
    third_color_eq hχ18 hχ12 hχ9 hχ16 h9_ne_16 h18_ne_9 h18_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S7: χ(19) = χ(9) (A). Via (4, 18, 19) + (16, 15, 19).
  have h19_ne_12 : χ 19 ≠ χ 12 := by
    intro h19_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 18
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h18_eq_12.symm
    · show χ 18 = χ (18 + 1)
      rw [show (18 + 1 : ℕ) = 19 by decide, h18_eq_12, h19_eq_12]
  have h19_ne_16 : χ 19 ≠ χ 16 := by
    intro h19_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 15) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 15
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h15_eq_16.symm
    · show χ 15 = χ (15 + 4)
      rw [show (15 + 4 : ℕ) = 19 by decide, h15_eq_16, h19_eq_16]
  have h19_eq_9 : χ 19 = χ 9 :=
    third_color_eq hχ19 hχ9 hχ12 hχ16 h12_ne_16 h19_ne_12 h19_ne_16 h9_ne_12 h9_ne_16
  -- S8: χ(6) = χ(12) (B). Via (20, 6, 11) + (8, 6, 8).
  have h6_ne_9 : χ 6 ≠ χ 9 := by
    intro h6_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 6
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h6_eq_9]
    · show χ 6 = χ (6 + 5)
      rw [show (6 + 5 : ℕ) = 11 by decide, h6_eq_9, ← h11_eq_9]
  have h6_ne_16 : χ 6 ≠ χ 16 := by
    intro h6_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 6) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 6
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16.trans h6_eq_16.symm
    · show χ 6 = χ (6 + 2)
      rw [show (6 + 2 : ℕ) = 8 by decide]; exact h6_eq_16.trans h8_eq_16.symm
  have h6_eq_12 : χ 6 = χ 12 :=
    third_color_eq hχ6 hχ12 hχ9 hχ16 h9_ne_16 h6_ne_9 h6_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- Conjoin all 8 forced positions.
  exact ⟨h15_eq_16, h11_eq_9, h14_eq_12, h17_eq_9, h13_eq_9, h18_eq_12, h19_eq_9, h6_eq_12⟩

/-! ### §128. — residual cell (3) hLayer d = 5 extended prefix + (C,C) sub-case.

  **Continuation from **.

  **Deliverable B**: Extended prefix at n ≥ 24 adding:
  - χ(22) ≠ A via (20, 17, 22) [n ≥ 22]
  - χ(24) ≠ A via (20, 19, 24) [n ≥ 24]

  **Deliverable C (partial)**: Sub-case (χ(5), χ(7)) = (C, C) closed via
  trivial terminal (8, 5, 7) mono.

  **Obstruction documented**: The remaining 3 sub-cases on (χ(5), χ(7)) —
  namely (A,A), (A,C), (C,A) — all admit valid partial 3-colorings up to
  n ≥ 24 without any mono triple. Higher threshold (n ≥ 28-40) or case
  split deeper needed; matches §95 docstring's "OBSTRUCTION not closed"
  for cell (3).

  Triples used (b=4):
  - (20, 17, 22): 20 + 68 = 88 = 4·22 ✓ (χ(22) ≠ A; uses χ(17) = A from )
  - (20, 19, 24): 20 + 76 = 96 = 4·24 ✓ (χ(24) ≠ A; uses χ(19) = A from )
  - (8, 5, 7): 8 + 20 = 28 = 4·7 ✓ ((C, C) sub-case terminal)
-/

/-- ** cell (3) d=5 extended prefix (Deliverable B)**: under cell (3) +
  χ(20) = χ(9) at n ≥ 24, 's 8-position prefix plus χ(22) ≠ A and
  χ(24) ≠ A. -/
theorem residual_cell_3_chi20_eq_chi9_forces_prefix2
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9) :
    χ 15 = χ 16 ∧ χ 11 = χ 9 ∧ χ 14 = χ 12 ∧
    χ 17 = χ 9 ∧ χ 13 = χ 9 ∧ χ 18 = χ 12 ∧
    χ 19 = χ 9 ∧ χ 6 = χ 12 ∧
    χ 22 ≠ χ 9 ∧ χ 24 ≠ χ 9 := by
  obtain ⟨h15, h11, h14, h17, h13, h18, h19, h6⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  refine ⟨h15, h11, h14, h17, h13, h18, h19, h6, ?_, ?_⟩
  · -- χ(22) ≠ A via (20, 17, 22).
    intro h22_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 17
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h17]
    · show χ 17 = χ (17 + 5)
      rw [show (17 + 5 : ℕ) = 22 by decide, h17, ← h22_eq_9]
  · -- χ(24) ≠ A via (20, 19, 24).
    intro h24_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 19
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h19]
    · show χ 19 = χ (19 + 5)
      rw [show (19 + 5 : ℕ) = 24 by decide, h19, ← h24_eq_9]

/-- ** cell (3) d=5 sub-case (C, C) closure (Deliverable C partial)**:
  if χ(5) = χ(16) AND χ(7) = χ(16) under cell (3) + χ(20) = χ(9), then
  (8, 5, 7) is a mono triple all = C, giving False at n ≥ 20.

  This handles ONE of the 4 sub-cases on (χ(5), χ(7)). The other 3 sub-cases
  ((A,A), (A,C), (C,A)) require deeper cascades and are not closed here. -/
theorem residual_cell_3_chi20_eq_chi9_subcase_chi5_chi7_both_C_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h20 : 20 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9)
    (h5_eq_16 : χ 5 = χ 16)
    (h7_eq_16 : χ 7 = χ 16) :
    False := by
  -- TERMINAL: (8, 5, 7) mono with χ(8) = χ(5) = χ(7) = C.
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 2) = χ 5
    rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h5_eq_16]
  · show χ 5 = χ (5 + 2)
    rw [show (5 + 2 : ℕ) = 7 by decide, h5_eq_16, ← h7_eq_16]

/-! ### §129. — residual cell (3) d=5 (A,A) sub-case (Deliverable B partial).

  **Sub-case**: under cell (3) + χ(20) = χ(9) + χ(5) = χ(9) + χ(7) = χ(9).

  **Discovery**: Many positions force *unconditionally* under / + χ(20) = χ(9):
  - χ(24) = C: self-loop m=6 ((24, 18, 24)) + χ(18) = B from forces χ(24) ≠ B;
    combined with 's χ(24) ≠ A → χ(24) = C.
  - χ(22) = B: (8, 22, 24) gives χ(22) ≠ C; combined with χ(22) ≠ A → χ(22) = B.
  - χ(25) = C: (20, 20, 25) self-mono gives χ(25) ≠ A; (12, 22, 25) gives χ(25) ≠ B.
  - χ(21) = A: (12, 18, 21) gives χ(21) ≠ B; (16, 21, 25) gives χ(21) ≠ C.
  - χ(26) = B: (20, 21, 26) gives χ(26) ≠ A; (8, 24, 26) gives χ(26) ≠ C.
  - χ(23) = A: (12, 23, 26) gives χ(23) ≠ B; (8, 23, 25) gives χ(23) ≠ C.
  - χ(28) = B: (20, 23, 28) gives χ(28) ≠ A; (16, 24, 28) gives χ(28) ≠ C.
  - χ(29) = A: (28, 22, 29) gives χ(29) ≠ B; (16, 25, 29) gives χ(29) ≠ C.
  - χ(31) = A: (12, 28, 31) gives χ(31) ≠ B; (24, 25, 31) gives χ(31) ≠ C.
  - χ(2) ≠ C: (24, 2, 8) gives χ(2) ≠ C.

  **Sub-case (A, A) specific**:
  - χ(10) = B: (20, 5, 10) gives χ(10) ≠ A; combined with χ(10) ≠ C unconditional.
  - χ(2) ≠ A: (20, 2, 7) gives χ(2) ≠ A.
  - Combined: **χ(2) = B**.

  **Obstruction**: Despite ~17 forced positions, NO mono triple emerges in [1, 31].
  - A-mono requires (20, y, y+5) with both A. No such pair exists in the A-set.
  - B/C mono requires anchor-pairs both same color at distance 1/2/3/4. None work.

  This documents that cell (3) (A,A) sub-case requires either much higher threshold
  (n ≥ 40+ for χ(36), χ(40) derivations) or a fundamentally different terminal mechanism.

  Triples used (b=4):
  - (20, 5, 10): 20 + 20 = 40 = 4·10 ✓ (χ(10) ≠ A)
  - (8, 8, 10): 8 + 32 = 40 ✓ (χ(10) ≠ C; from -era)
  - (20, 2, 7): 20 + 8 = 28 = 4·7 ✓ (χ(2) ≠ A)
  - (24, 2, 8): 24 + 8 = 32 = 4·8 ✓ (χ(2) ≠ C; uses χ(24) = C)
  - (24, 18, 24): 24 + 72 = 96 = 4·24 ✓ (χ(24) ≠ B; self-loop m=6)
  - (8, 22, 24): 8 + 88 = 96 ✓ (χ(22) ≠ C)
  - (20, 20, 25): 20 + 80 = 100 = 4·25 ✓ (χ(25) ≠ A; self-mono d=5)
  - (12, 22, 25): 12 + 88 = 100 ✓ (χ(25) ≠ B)
  - (12, 18, 21): 12 + 72 = 84 = 4·21 ✓ (χ(21) ≠ B)
  - (16, 21, 25): 16 + 84 = 100 ✓ (χ(21) ≠ C)
  - (20, 21, 26): 20 + 84 = 104 = 4·26 ✓ (χ(26) ≠ A)
  - (8, 24, 26): 8 + 96 = 104 ✓ (χ(26) ≠ C)
  - (12, 23, 26): 12 + 92 = 104 ✓ (χ(23) ≠ B)
  - (8, 23, 25): 8 + 92 = 100 ✓ (χ(23) ≠ C)
  - (20, 23, 28): 20 + 92 = 112 = 4·28 ✓ (χ(28) ≠ A)
  - (16, 24, 28): 16 + 96 = 112 ✓ (χ(28) ≠ C)
  - (28, 22, 29): 28 + 88 = 116 = 4·29 ✓ (χ(29) ≠ B)
  - (16, 25, 29): 16 + 100 = 116 ✓ (χ(29) ≠ C)
  - (12, 28, 31): 12 + 112 = 124 = 4·31 ✓ (χ(31) ≠ B)
  - (24, 25, 31): 24 + 100 = 124 ✓ (χ(31) ≠ C)
-/

set_option maxHeartbeats 1600000 in
/-- ** (A,A) sub-case prefix (Deliverable B)**: under cell (3) + χ(20) = χ(9)
  + χ(5) = χ(9) + χ(7) = χ(9), at n ≥ 32, derive 17+ forced positions but no
  terminal mono emerges. This documents the cell (3) obstruction depth and
  provides a starting point for future deeper cascades. -/
theorem residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_A_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9)
    (h5_eq_9 : χ 5 = χ 9)
    (h7_eq_9 : χ 7 = χ 9) :
    χ 10 = χ 12 ∧ χ 24 = χ 16 ∧ χ 22 = χ 12 ∧
    χ 25 = χ 16 ∧ χ 21 = χ 9 ∧ χ 26 = χ 12 ∧
    χ 23 = χ 9 ∧ χ 28 = χ 12 ∧ χ 29 = χ 9 ∧ χ 31 = χ 9 := by
  -- Get prefix (8 positions).
  obtain ⟨h15, h11, h14, h17, h13, h18, h19, h6⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ22 : χ 22 < 3 := hχk 22 (by omega) (by omega)
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ25 : χ 25 < 3 := hχk 25 (by omega) (by omega)
  have hχ26 : χ 26 < 3 := hχk 26 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  have hχ29 : χ 29 < 3 := hχk 29 (by omega) (by omega)
  have hχ31 : χ 31 < 3 := hχk 31 (by omega) (by omega)
  -- S1: χ(10) = B (sub-case (A,A) specific). Via (20, 5, 10) ≠ A + (8, 8, 10) ≠ C.
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 5
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_9, ← h10_eq_9]
  have h10_ne_16 : χ 10 ≠ χ 16 := by
    intro h10_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_16, h10_eq_16]
  have h10_eq_12 : χ 10 = χ 12 :=
    third_color_eq hχ10 hχ12 hχ9 hχ16 h9_ne_16 h10_ne_9 h10_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S2: χ(24) = C unconditional. Via (20, 19, 24) ≠ A + (24, 18, 24) ≠ B.
  have h24_ne_9 : χ 24 ≠ χ 9 := by
    intro h24_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 19
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h19]
    · show χ 19 = χ (19 + 5)
      rw [show (19 + 5 : ℕ) = 24 by decide, h19, ← h24_eq_9]
  have h24_ne_12 : χ 24 ≠ χ 12 := by
    intro h24_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 18
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_12, ← h18]
    · show χ 18 = χ (18 + 6)
      rw [show (18 + 6 : ℕ) = 24 by decide, h18, h24_eq_12]
  have h24_eq_16 : χ 24 = χ 16 :=
    third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h24_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S3: χ(22) = B unconditional. Via (20, 17, 22) ≠ A + (8, 22, 24) ≠ C.
  have h22_ne_9 : χ 22 ≠ χ 9 := by
    intro h22_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 17
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h17]
    · show χ 17 = χ (17 + 5)
      rw [show (17 + 5 : ℕ) = 22 by decide, h17, ← h22_eq_9]
  have h22_ne_16 : χ 22 ≠ χ 16 := by
    intro h22_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 22
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h22_eq_16]
    · show χ 22 = χ (22 + 2)
      rw [show (22 + 2 : ℕ) = 24 by decide, h22_eq_16, ← h24_eq_16]
  have h22_eq_12 : χ 22 = χ 12 :=
    third_color_eq hχ22 hχ12 hχ9 hχ16 h9_ne_16 h22_ne_9 h22_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S4: χ(25) = C unconditional. Via (20, 20, 25) ≠ A + (12, 22, 25) ≠ B.
  have h25_ne_9 : χ 25 ≠ χ 9 := by
    intro h25_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 20
      rw [show (4 * 5 : ℕ) = 20 by decide]
    · show χ 20 = χ (20 + 5)
      rw [show (20 + 5 : ℕ) = 25 by decide, h20_eq_9, h25_eq_9]
  have h25_ne_12 : χ 25 ≠ χ 12 := by
    intro h25_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 22
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h22_eq_12.symm
    · show χ 22 = χ (22 + 3)
      rw [show (22 + 3 : ℕ) = 25 by decide, h22_eq_12, h25_eq_12]
  have h25_eq_16 : χ 25 = χ 16 :=
    third_color_eq hχ25 hχ16 hχ9 hχ12 h9_ne_12 h25_ne_9 h25_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S5: χ(21) = A unconditional. Via (12, 18, 21) ≠ B + (16, 21, 25) ≠ C.
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 18
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h18.symm
    · show χ 18 = χ (18 + 3)
      rw [show (18 + 3 : ℕ) = 21 by decide, h18, h21_eq_12]
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 21
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h21_eq_16.symm
    · show χ 21 = χ (21 + 4)
      rw [show (21 + 4 : ℕ) = 25 by decide, h21_eq_16, ← h25_eq_16]
  have h21_eq_9 : χ 21 = χ 9 :=
    third_color_eq hχ21 hχ9 hχ12 hχ16 h12_ne_16 h21_ne_12 h21_ne_16 h9_ne_12 h9_ne_16
  -- S6: χ(26) = B unconditional. Via (20, 21, 26) ≠ A + (8, 24, 26) ≠ C.
  have h26_ne_9 : χ 26 ≠ χ 9 := by
    intro h26_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 21) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 21
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h21_eq_9]
    · show χ 21 = χ (21 + 5)
      rw [show (21 + 5 : ℕ) = 26 by decide, h21_eq_9, ← h26_eq_9]
  have h26_ne_16 : χ 26 ≠ χ 16 := by
    intro h26_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 24
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h24_eq_16]
    · show χ 24 = χ (24 + 2)
      rw [show (24 + 2 : ℕ) = 26 by decide, h24_eq_16, h26_eq_16]
  have h26_eq_12 : χ 26 = χ 12 :=
    third_color_eq hχ26 hχ12 hχ9 hχ16 h9_ne_16 h26_ne_9 h26_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S7: χ(23) = A unconditional. Via (12, 23, 26) ≠ B + (8, 23, 25) ≠ C.
  have h23_ne_12 : χ 23 ≠ χ 12 := by
    intro h23_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 23
      rw [show (4 * 3 : ℕ) = 12 by decide, h23_eq_12]
    · show χ 23 = χ (23 + 3)
      rw [show (23 + 3 : ℕ) = 26 by decide, h23_eq_12, ← h26_eq_12]
  have h23_ne_16 : χ 23 ≠ χ 16 := by
    intro h23_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 23
      rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h23_eq_16]
    · show χ 23 = χ (23 + 2)
      rw [show (23 + 2 : ℕ) = 25 by decide, h23_eq_16, ← h25_eq_16]
  have h23_eq_9 : χ 23 = χ 9 :=
    third_color_eq hχ23 hχ9 hχ12 hχ16 h12_ne_16 h23_ne_12 h23_ne_16 h9_ne_12 h9_ne_16
  -- S8: χ(28) = B unconditional. Via (20, 23, 28) ≠ A + (16, 24, 28) ≠ C.
  have h28_ne_9 : χ 28 ≠ χ 9 := by
    intro h28_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 23) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 23
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h23_eq_9]
    · show χ 23 = χ (23 + 5)
      rw [show (23 + 5 : ℕ) = 28 by decide, h23_eq_9, ← h28_eq_9]
  have h28_ne_16 : χ 28 ≠ χ 16 := by
    intro h28_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 24
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h24_eq_16.symm
    · show χ 24 = χ (24 + 4)
      rw [show (24 + 4 : ℕ) = 28 by decide, h24_eq_16, h28_eq_16]
  have h28_eq_12 : χ 28 = χ 12 :=
    third_color_eq hχ28 hχ12 hχ9 hχ16 h9_ne_16 h28_ne_9 h28_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S9: χ(29) = A unconditional. Via (28, 22, 29) ≠ B + (16, 25, 29) ≠ C.
  have h29_ne_12 : χ 29 ≠ χ 12 := by
    intro h29_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 22) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 22
      rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_12.trans h22_eq_12.symm
    · show χ 22 = χ (22 + 7)
      rw [show (22 + 7 : ℕ) = 29 by decide, h22_eq_12, h29_eq_12]
  have h29_ne_16 : χ 29 ≠ χ 16 := by
    intro h29_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 25) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 25
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h25_eq_16.symm
    · show χ 25 = χ (25 + 4)
      rw [show (25 + 4 : ℕ) = 29 by decide, h25_eq_16, h29_eq_16]
  have h29_eq_9 : χ 29 = χ 9 :=
    third_color_eq hχ29 hχ9 hχ12 hχ16 h12_ne_16 h29_ne_12 h29_ne_16 h9_ne_12 h9_ne_16
  -- S10: χ(31) = A unconditional. Via (12, 28, 31) ≠ B + (24, 25, 31) ≠ C.
  have h31_ne_12 : χ 31 ≠ χ 12 := by
    intro h31_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 28) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 28
      rw [show (4 * 3 : ℕ) = 12 by decide]; exact h28_eq_12.symm
    · show χ 28 = χ (28 + 3)
      rw [show (28 + 3 : ℕ) = 31 by decide, h28_eq_12, h31_eq_12]
  have h31_ne_16 : χ 31 ≠ χ 16 := by
    intro h31_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 25) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 25
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_16.trans h25_eq_16.symm
    · show χ 25 = χ (25 + 6)
      rw [show (25 + 6 : ℕ) = 31 by decide, h25_eq_16, h31_eq_16]
  have h31_eq_9 : χ 31 = χ 9 :=
    third_color_eq hχ31 hχ9 hχ12 hχ16 h12_ne_16 h31_ne_12 h31_ne_16 h9_ne_12 h9_ne_16
  -- Conjoin all forced positions.
  exact ⟨h10_eq_12, h24_eq_16, h22_eq_12, h25_eq_16, h21_eq_9, h26_eq_12,
         h23_eq_9, h28_eq_12, h29_eq_9, h31_eq_9⟩

/-! ### §130. — residual cell (3) d=5 (A,A) sub-case CLOSURE.

  **Sub-case**: cell (3) + χ(20) = χ(9) + χ(5) = χ(9) + χ(7) = χ(9).

  **CLOSED at n ≥ 32** via case split on χ(32):

  Key insight: self-loop m=8 ((32, 24, 32) using χ(24) = C from ) forces
  χ(32) ≠ C. Then by trichotomy χ(32) ∈ {A, B}, and BOTH lead to mono:
  - χ(32) = A: terminal **(32, 5, 13)** all A (uses χ(5)=A sub-case + χ(13)=A ).
  - χ(32) = B: terminal **(32, 4, 12)** all B (uses χ(4)=B + χ(12)=B trivial).

  Triples used:
  - (32, 24, 32): self-loop m=8, gives χ(32) ≠ χ(24) = C ✓
  - (32, 5, 13): 32 + 20 = 52 = 4·13 ✓ (A-mono terminal)
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓ (B-mono terminal)
-/

/-- ** (A, A) sub-case CLOSURE**: under cell (3) + χ(20) = χ(9) +
  χ(5) = χ(9) + χ(7) = χ(9), False at n ≥ 32. Case split on χ(32) using
  trichotomy — both terminal monos (32, 5, 13) and (32, 4, 12). -/
theorem residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_A_forces_False_continuation
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9)
    (h5_eq_9 : χ 5 = χ 9)
    (h7_eq_9 : χ 7 = χ 9) :
    False := by
  -- Get prefix for χ(13) = χ(9) (5th conjunct).
  obtain ⟨_, _, _, _, h13_eq_9, _, _, _⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  -- Get sub-case prefix for χ(24) = χ(16) (2nd conjunct).
  obtain ⟨_, h24_eq_16, _, _, _, _, _, _, _, _⟩ :=
    residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_A_forces_prefix χ h32 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9 h5_eq_9 h7_eq_9
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Self-loop m=8: χ(32) ≠ χ(24) = χ(16).
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide]
    exact h24_eq_16.trans h32_eq_16.symm
  -- Case split on χ(32).
  by_cases h32_eq_9 : χ 32 = χ 9
  · -- Case χ(32) = A: terminal (32, 5, 13) all A.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 5
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_9, ← h13_eq_9]
  · -- Case χ(32) ≠ A. Combined with χ(32) ≠ C → χ(32) = B.
    have h32_eq_12 : χ 32 = χ 12 :=
      third_color_eq hχ32 hχ12 hχ9 hχ16 h9_ne_16 h32_eq_9 h32_ne_16 (Ne.symm h9_ne_12) h12_ne_16
    -- Terminal (32, 4, 12) all B.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12

/-! ### §131. — residual cell (3) d=5 (A, C) sub-case CLOSURE.

  **Strategic insight**: 's proof for (A, A) sub-case never used the
  χ(7) = χ(9) hypothesis. The closure structure (χ(32) case split with
  terminals (32, 5, 13) and (32, 4, 12)) only needs χ(5) = A.

  Therefore the (A, C) sub-case closes by the SAME proof, with χ(7) = χ(16)
  appearing as an unused hypothesis (kept for sub-case structure clarity).

  This is a strong structural observation: **cell (3) d=5 closure depends on
  χ(5), not χ(7)**. Only sub-cases χ(5) = A vs χ(5) = C matter.

  Triples used (identical to ):
  - (24, 18, 24): self-loop m=6, forces χ(24) ≠ B (uses χ(18) = B from )
  - (32, 24, 32): self-loop m=8, forces χ(32) ≠ C (uses χ(24) = C derived)
  - (32, 5, 13): 32 + 20 = 52 = 4·13 ✓ (Case χ(32) = A terminal)
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓ (Case χ(32) = B terminal)
-/

/-- ** (A, C) sub-case CLOSURE**: under cell (3) + χ(20) = χ(9) +
  χ(5) = χ(9) + χ(7) = χ(16), False at n ≥ 32. Identical proof structure
  to ((A,A) closure) since χ(7) is not used. -/
theorem residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_C_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9)
    (h5_eq_9 : χ 5 = χ 9)
    (_h7_eq_16 : χ 7 = χ 16) :
    False := by
  -- Get prefix for χ(13) = A (5th conjunct) and χ(18) = B (6th conjunct).
  obtain ⟨_, _, _, _, h13_eq_9, h18_eq_12, _, _⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  -- Get prefix2 for χ(24) ≠ A (10th conjunct).
  obtain ⟨_, _, _, _, _, _, _, _, _, h24_ne_9⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix2 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Derive χ(24) = C: self-loop m=6 (24, 18, 24) forces χ(24) ≠ B via χ(18) = B.
  have h24_ne_12 : χ 24 ≠ χ 12 := by
    intro h24_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 18
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_12, ← h18_eq_12]
    · show χ 18 = χ (18 + 6)
      rw [show (18 + 6 : ℕ) = 24 by decide, h18_eq_12, h24_eq_12]
  have h24_eq_16 : χ 24 = χ 16 :=
    third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h24_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- Self-loop m=8: χ(32) ≠ χ(24) = χ(16).
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide]
    exact h24_eq_16.trans h32_eq_16.symm
  -- Case split on χ(32).
  by_cases h32_eq_9 : χ 32 = χ 9
  · -- Case χ(32) = A: terminal (32, 5, 13) all A.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 5
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_9, ← h13_eq_9]
  · -- Case χ(32) ≠ A. Combined with χ(32) ≠ C → χ(32) = B.
    have h32_eq_12 : χ 32 = χ 12 :=
      third_color_eq hχ32 hχ12 hχ9 hχ16 h9_ne_16 h32_eq_9 h32_ne_16 (Ne.symm h9_ne_12) h12_ne_16
    -- Terminal (32, 4, 12) all B.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12

/-! ### §132. — residual cell (3) hLayer d = 5 DIRECT CLOSURE (Deliverable A).

  **MAJOR STRATEGIC BREAKTHROUGH**: The χ(32) pivot from works
  WITHOUT any (χ(5), χ(7)) sub-case split. The A-case terminal can use
  **(32, 9, 17)** instead of (32, 5, 13) — and (32, 9, 17) uses only
  χ(9) (cell hypothesis) and χ(17) = A ( prefix), making it
  **independent of χ(5) and χ(7)**.

  **Proof structure**:
  1. prefix → χ(17) = A, χ(18) = B, χ(19) = A.
  2. χ(24) ≠ A via (20, 19, 24).
  3. χ(24) ≠ B via self-loop m=6 (24, 18, 24).
  4. third_color_eq → χ(24) = C.
  5. Self-loop m=8 (32, 24, 32) → χ(32) ≠ C.
  6. Trichotomy on χ(32):
     - χ(32) = A: terminal (32, 9, 17) all A — MONO.
     - χ(32) = B: terminal (32, 4, 12) all B — MONO.
     - χ(32) = C: contradicts step 5.

  This **subsumes all 4 sub-cases** (,, ) and gives the full
  cell (3) d=5 closure in a single direct proof.

  Triples used:
  - (20, 19, 24): 20 + 76 = 96 = 4·24 ✓ (χ(24) ≠ A)
  - (24, 18, 24): 24 + 72 = 96 ✓ (self-loop m=6: χ(24) ≠ B)
  - (32, 24, 32): self-loop m=8 ✓ (χ(32) ≠ C)
  - (32, 9, 17): 32 + 36 = 68 = 4·17 ✓ (A-mono terminal)
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓ (B-mono terminal)

  Cell (1) closed at n ≥ 20 (). Cell (2) closed at n ≥ 20 ().
  Cell (3) closes at **n ≥ 32** due to the χ(32) pivot — higher threshold
  reflecting cell (3)'s structural asymmetry, but still finite and tractable.
-/

/-- ** cell (3) d=5 DIRECT CLOSURE**: under cell (3) + χ(20) = χ(9),
  False at n ≥ 32. No (χ(5), χ(7)) sub-case split needed —
  the χ(32) pivot with terminal (32, 9, 17) for the A-case bypasses all
  sub-cases entirely. -/
theorem residual_cell_3_chi20_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h20_eq_9 : χ 20 = χ 9) :
    False := by
  -- Get prefix for χ(17) = A, χ(18) = B, χ(19) = A.
  obtain ⟨_, _, _, h17_eq_9, _, h18_eq_12, h19_eq_9, _⟩ :=
    residual_cell_3_chi20_eq_chi9_forces_prefix χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- χ(24) ≠ A via (20, 19, 24).
  have h24_ne_9 : χ 24 ≠ χ 9 := by
    intro h24_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 19) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 19
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_9, ← h19_eq_9]
    · show χ 19 = χ (19 + 5)
      rw [show (19 + 5 : ℕ) = 24 by decide, h19_eq_9, ← h24_eq_9]
  -- χ(24) ≠ B via self-loop (24, 18, 24).
  have h24_ne_12 : χ 24 ≠ χ 12 := by
    intro h24_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 18
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_12, ← h18_eq_12]
    · show χ 18 = χ (18 + 6)
      rw [show (18 + 6 : ℕ) = 24 by decide, h18_eq_12, h24_eq_12]
  -- χ(24) = C by trichotomy.
  have h24_eq_16 : χ 24 = χ 16 :=
    third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h24_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- Self-loop m=8: χ(32) ≠ χ(24) = χ(16).
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 8) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 8) = χ (4 * 8)
    rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
        show ((4 : ℕ) * 8) = 32 by decide]
    exact h24_eq_16.trans h32_eq_16.symm
  -- Case split on χ(32).
  by_cases h32_eq_9 : χ 32 = χ 9
  · -- Case χ(32) = A: terminal (32, 9, 17) all A.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 9
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
    · show χ 9 = χ (9 + 8)
      rw [show (9 + 8 : ℕ) = 17 by decide, ← h17_eq_9]
  · -- Case χ(32) ≠ A. With χ(32) ≠ C → χ(32) = B.
    have h32_eq_12 : χ 32 = χ 12 :=
      third_color_eq hχ32 hχ12 hχ9 hχ16 h9_ne_16 h32_eq_9 h32_ne_16 (Ne.symm h9_ne_12) h12_ne_16
    -- Terminal (32, 4, 12) all B.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12

/-- ** contrapositive** (cell 3): χ(20) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi20_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 20 ≠ χ 9 := by
  intro h20_eq_9
  exact residual_cell_3_chi20_eq_chi9_forces_False χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h20_eq_9

/-- ** layer compression d=5 (cell 3)**: χ(20) ∈ {χ(12), χ(16)} under
  residual cell (3). Feeds bridge as the d=5 hLayer case for cell (3).
  Threshold n ≥ 32 (higher than cell (1)/(2)'s n ≥ 20 due to cell (3)'s
  structural asymmetry — the χ(32) pivot requires deeper position). -/
theorem residual_cell_3_layer_compression_d5
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 20 = χ 12 ∨ χ 20 = χ 16 := by
  have h20_ne_9 : χ 20 ≠ χ 9 :=
    residual_cell_3_chi20_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  by_cases h_eq_12 : χ 20 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ20 hχ16 hχ9 hχ12 h9_ne_12 h20_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §133. — residual cell (3) hLayer d = 6.

  **Target.** Under cell (3) hypotheses, prove χ(24) ∈ {χ(12), χ(16)}.

  **4-step cascade + terminal (8, 3, 5) all C** under contradiction
  χ(24) = χ(9) = A. Threshold n ≥ 24.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | 1 | χ(15) = C | (24, 9, 15) [≠A] + (12, 12, 15) [≠B] |
  | 2 | χ(11) = A | (16, 11, 15) [≠C] + (4, 11, 12) [≠B] |
  | 3 | χ(5) = C | (24, 5, 11) [≠A; uses S2] + (4, 4, 5) [≠B] |
  | 4 | χ(3) = C | (24, 3, 9) [≠A] + (4, 3, 4) [≠B] |
  | T | **(8, 3, 5) mono** | χ(8) = χ(3) = χ(5) = C |

  All triples verified for b=4 (x + 4y = 4z):
  - (24, 9, 15): 24 + 36 = 60 = 4·15 ✓
  - (12, 12, 15): 12 + 48 = 60 ✓
  - (16, 11, 15): 16 + 44 = 60 ✓
  - (4, 11, 12): 4 + 44 = 48 = 4·12 ✓
  - (24, 5, 11): 24 + 20 = 44 = 4·11 ✓
  - (4, 4, 5): 4 + 16 = 20 = 4·5 ✓
  - (24, 3, 9): 24 + 12 = 36 = 4·9 ✓
  - (4, 3, 4): 4 + 12 = 16 = 4·4 ✓
  - (8, 3, 5): 8 + 12 = 20 ✓ (TERMINAL MONO with all C)
-/

set_option maxHeartbeats 400000 in
/-- ** chi(24) = chi(9) closure (cell 3)**: cell (3) + χ(24) = χ(9) ⟹
  False at n ≥ 24. 4-step cascade ending in terminal mono (8, 3, 5) all C. -/
theorem residual_cell_3_chi24_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h24_eq_9 : χ 24 = χ 9) :
    False := by
  have hχ3 : χ 3 < 3 := hχk 3 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- S1: χ(15) = C. Via (24, 9, 15) ≠A + (12, 12, 15) ≠B.
  have h15_ne_9 : χ 15 ≠ χ 9 := by
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 9
      rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_9
    · show χ 9 = χ (9 + 6)
      rw [show (9 + 6 : ℕ) = 15 by decide, h15_eq_9]
  have h15_ne_12 : χ 15 ≠ χ 12 := by
    intro h15_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 12
      rw [show (4 * 3 : ℕ) = 12 by decide]
    · show χ 12 = χ (12 + 3)
      rw [show (12 + 3 : ℕ) = 15 by decide, h15_eq_12]
  have h15_eq_16 : χ 15 = χ 16 :=
    third_color_eq hχ15 hχ16 hχ9 hχ12 h9_ne_12 h15_ne_9 h15_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(11) = A. Via (16, 11, 15) ≠C + (4, 11, 12) ≠B.
  have h11_ne_16 : χ 11 ≠ χ 16 := by
    intro h11_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 11
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h11_eq_16.symm
    · show χ 11 = χ (11 + 4)
      rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_16, ← h15_eq_16]
  have h11_ne_12 : χ 11 ≠ χ 12 := by
    intro h11_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 11) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 11
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h11_eq_12.symm
    · show χ 11 = χ (11 + 1)
      rw [show (11 + 1 : ℕ) = 12 by decide]; exact h11_eq_12
  have h11_eq_9 : χ 11 = χ 9 :=
    third_color_eq hχ11 hχ9 hχ12 hχ16 h12_ne_16 h11_ne_12 h11_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(5) = C. Via (24, 5, 11) ≠A + (4, 4, 5) ≠B.
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 5
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h5_eq_9]
    · show χ 5 = χ (5 + 6)
      rw [show (5 + 6 : ℕ) = 11 by decide, h5_eq_9, ← h11_eq_9]
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h4_eq_12, h5_eq_12]
  have h5_eq_16 : χ 5 = χ 16 :=
    third_color_eq hχ5 hχ16 hχ9 hχ12 h9_ne_12 h5_ne_9 h5_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S4: χ(3) = C. Via (24, 3, 9) ≠A + (4, 3, 4) ≠B.
  have h3_ne_9 : χ 3 ≠ χ 9 := by
    intro h3_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 3
      rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_9, ← h3_eq_9]
    · show χ 3 = χ (3 + 6)
      rw [show (3 + 6 : ℕ) = 9 by decide]; exact h3_eq_9
  have h3_ne_12 : χ 3 ≠ χ 12 := by
    intro h3_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 3) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 3
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h3_eq_12.symm
    · show χ 3 = χ (3 + 1)
      rw [show (3 + 1 : ℕ) = 4 by decide, h3_eq_12, ← h4_eq_12]
  have h3_eq_16 : χ 3 = χ 16 :=
    third_color_eq hχ3 hχ16 hχ9 hχ12 h9_ne_12 h3_ne_9 h3_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (8, 3, 5) mono with χ(8) = χ(3) = χ(5) = C.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 3) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 2) = χ 3
    rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h3_eq_16]
  · show χ 3 = χ (3 + 2)
    rw [show (3 + 2 : ℕ) = 5 by decide, h3_eq_16, ← h5_eq_16]

/-- ** contrapositive** (cell 3): χ(24) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi24_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 24 ≠ χ 9 := by
  intro h24_eq_9
  exact residual_cell_3_chi24_eq_chi9_forces_False χ h24 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h24_eq_9

/-- ** layer compression d=6 (cell 3)**: χ(24) ∈ {χ(12), χ(16)} under
  residual cell (3). Feeds bridge as the d=6 hLayer case for cell (3). -/
theorem residual_cell_3_layer_compression_d6
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 24 = χ 12 ∨ χ 24 = χ 16 := by
  have h24_ne_9 : χ 24 ≠ χ 9 :=
    residual_cell_3_chi24_ne_chi9 χ h24 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  by_cases h_eq_12 : χ 24 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ24 hχ16 hχ9 hχ12 h9_ne_12 h24_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §134. — residual cell (3) hLayer d = 7 at n ≥ 32.

  **Target.** Under cell (3) hypotheses, prove χ(28) ∈ {χ(12), χ(16)}.

  **Closure**: 3-branch case split at n ≥ 32:
  - Case χ(24) = B: cascade through χ(10)=A → χ(17)=C → χ(21)=B → terminal (4, 20, 21) all B.
  - Case χ(24) = C, χ(32) = A: χ(17)=C via (32, 9, 17) → χ(21)=B → terminal (4, 20, 21) all B.
  - Case χ(24) = C, χ(32) = B: terminal (32, 4, 12) all B.

  Uses (χ(20) = B unconditional under cell-3 + ≠C) and (χ(24) ∈ {B, C}).

  Key triples:
  - (16, 16, 20): 20 ≠ C ( partner)
  - (20, 12, 17): 17 ≠ B unconditional
  - self-loop m=7 (28, 21, 28): χ(21) ≠ A
  - (24, 4, 10): sub-case χ(24)=B forces χ(10) ≠ B
  - (8, 8, 10): χ(10) ≠ C unconditional
  - (28, 10, 17): forces χ(17) ≠ A when χ(10) = A
  - (32, 24, 32): self-loop m=8, sub-case χ(24)=C forces χ(32) ≠ C
  - (32, 9, 17): sub-case χ(32)=A forces χ(17) ≠ A
  - (16, 17, 21): χ(17)=C forces χ(21) ≠ C
  - (4, 20, 21): B-mono terminal
  - (32, 4, 12): B-mono terminal in sub-case χ(32)=B
-/

set_option maxHeartbeats 1600000 in
/-- ** chi(28) = chi(9) closure (cell 3)**: cell (3) + χ(28) = χ(9) ⟹
  False at n ≥ 32. 3-branch case split on (χ(24), χ(32)) — both lead to
  B-mono terminals (4, 20, 21) or (32, 4, 12). -/
theorem residual_cell_3_chi28_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h28_eq_9 : χ 28 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Preamble: χ(20) = B ( + ≠C).
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_3_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 := h20_disj.resolve_right h20_ne_16
  -- Preamble: χ(24) ∈ {B, C} ().
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_3_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  -- χ(17) ≠ B unconditional via (20, 12, 17).
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  -- χ(21) ≠ A via self-loop m=7.
  have h21_ne_9 : χ 21 ≠ χ 9 := by
    intro h21_eq_9
    have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
      (m := 7) (by omega) (by omega)
    apply h_self
    show χ ((4 - 1) * 7) = χ (4 * 7)
    rw [show ((4 - 1) * 7 : ℕ) = 21 by decide,
        show ((4 : ℕ) * 7) = 28 by decide, h21_eq_9, ← h28_eq_9]
  -- χ(10) ≠ C unconditional via (8, 8, 10).
  have h10_ne_16 : χ 10 ≠ χ 16 := by
    intro h10_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide, h8_eq_16, h10_eq_16]
  -- The shared closure subroutine: given χ(17) = C, derive (4, 20, 21) mono.
  -- We define this inline below since each branch has different proofs of χ(17) = C.
  -- Case split on χ(24).
  rcases h24_disj with h24_eq_12 | h24_eq_16
  · -- Case χ(24) = B.
    -- Force χ(10) = A via (24, 4, 10) ≠ B + (8, 8, 10) ≠ C.
    have h10_ne_12 : χ 10 ≠ χ 12 := by
      intro h10_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 6) = χ 4
        rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_12.trans h4_eq_12.symm
      · show χ 4 = χ (4 + 6)
        rw [show (4 + 6 : ℕ) = 10 by decide, h4_eq_12, h10_eq_12]
    have h10_eq_9 : χ 10 = χ 9 :=
      third_color_eq hχ10 hχ9 hχ12 hχ16 h12_ne_16 h10_ne_12 h10_ne_16 h9_ne_12 h9_ne_16
    -- Force χ(17) = C via (28, 10, 17) ≠ A.
    have h17_ne_9 : χ 17 ≠ χ 9 := by
      intro h17_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 10) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 10
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_9, ← h10_eq_9]
      · show χ 10 = χ (10 + 7)
        rw [show (10 + 7 : ℕ) = 17 by decide, h10_eq_9, ← h17_eq_9]
    have h17_eq_16 : χ 17 = χ 16 :=
      third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
    -- Force χ(21) = B via (16, 17, 21) ≠ C.
    have h21_ne_16 : χ 21 ≠ χ 16 := by
      intro h21_eq_16
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 17) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 17
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h17_eq_16.symm
      · show χ 17 = χ (17 + 4)
        rw [show (17 + 4 : ℕ) = 21 by decide, h17_eq_16, h21_eq_16]
    have h21_eq_12 : χ 21 = χ 12 :=
      third_color_eq hχ21 hχ12 hχ9 hχ16 h9_ne_16 h21_ne_9 h21_ne_16 (Ne.symm h9_ne_12) h12_ne_16
    -- Terminal (4, 20, 21) all B.
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  · -- Case χ(24) = C.
    -- Self-loop m=8: χ(32) ≠ χ(24) = C.
    have h32_ne_16 : χ 32 ≠ χ 16 := by
      intro h32_eq_16
      have h_self := bAdicEquation_self_loop_chi_diff (b := 4) (n := n) (by omega) χ hNoMono
        (m := 8) (by omega) (by omega)
      apply h_self
      show χ ((4 - 1) * 8) = χ (4 * 8)
      rw [show ((4 - 1) * 8 : ℕ) = 24 by decide,
          show ((4 : ℕ) * 8) = 32 by decide]
      exact h24_eq_16.trans h32_eq_16.symm
    -- Sub-case split on χ(32).
    by_cases h32_eq_9 : χ 32 = χ 9
    · -- Sub-case χ(32) = A.
      -- Force χ(17) = C via (32, 9, 17) ≠ A.
      have h17_ne_9 : χ 17 ≠ χ 9 := by
        intro h17_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 9
          rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
        · show χ 9 = χ (9 + 8)
          rw [show (9 + 8 : ℕ) = 17 by decide, ← h17_eq_9]
      have h17_eq_16 : χ 17 = χ 16 :=
        third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
      -- Force χ(21) = B via (16, 17, 21) ≠ C.
      have h21_ne_16 : χ 21 ≠ χ 16 := by
        intro h21_eq_16
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 4) (y := 17) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 4) = χ 17
          rw [show (4 * 4 : ℕ) = 16 by decide]; exact h17_eq_16.symm
        · show χ 17 = χ (17 + 4)
          rw [show (17 + 4 : ℕ) = 21 by decide, h17_eq_16, h21_eq_16]
      have h21_eq_12 : χ 21 = χ 12 :=
        third_color_eq hχ21 hχ12 hχ9 hχ16 h9_ne_16 h21_ne_9 h21_ne_16 (Ne.symm h9_ne_12) h12_ne_16
      -- Terminal (4, 20, 21) all B.
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 1) = χ 20
        rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
      · show χ 20 = χ (20 + 1)
        rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
    · -- Sub-case χ(32) ≠ A. With χ(32) ≠ C → χ(32) = B.
      have h32_eq_12 : χ 32 = χ 12 :=
        third_color_eq hχ32 hχ12 hχ9 hχ16 h9_ne_16 h32_eq_9 h32_ne_16 (Ne.symm h9_ne_12) h12_ne_16
      -- Terminal (32, 4, 12) all B.
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 4
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h4_eq_12]
      · show χ 4 = χ (4 + 8)
        rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12

/-- ** contrapositive** (cell 3): χ(28) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi28_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 28 ≠ χ 9 := by
  intro h28_eq_9
  exact residual_cell_3_chi28_eq_chi9_forces_False χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h28_eq_9

/-- ** layer compression d=7 (cell 3)**: χ(28) ∈ {χ(12), χ(16)} under
  residual cell (3). Threshold n ≥ 32 due to χ(32) pivot in sub-case χ(24) = C. -/
theorem residual_cell_3_layer_compression_d7
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 28 = χ 12 ∨ χ 28 = χ 16 := by
  have h28_ne_9 : χ 28 ≠ χ 9 :=
    residual_cell_3_chi28_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  by_cases h_eq_12 : χ 28 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ28 hχ16 hχ9 hχ12 h9_ne_12 h28_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §135. — residual cell (3) hLayer d = 8.

  **Target.** Under cell (3) hypotheses, prove χ(32) ∈ {χ(12), χ(16)}.

  **4-step cascade + terminal (16, 13, 17) all C** under contradiction
  χ(32) = χ(9). No case split needed (unlike 's 3-branch).

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P | χ(20) = B | + (16, 16, 20) [≠C] |
  | 1 | χ(17) = C | (32, 9, 17) [≠A] + (20, 12, 17) [≠B] |
  | 2 | χ(21) = A | (4, 20, 21) [≠B] + (16, 17, 21) [≠C] |
  | 3 | χ(13) = C | (32, 13, 21) [≠A; uses S2] + (4, 12, 13) [≠B] |
  | T | **(16, 13, 17) mono** | χ(16) = χ(13) = χ(17) = C |

  Threshold n ≥ 32 (uses hLayer d=5 + position 32).

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (32, 9, 17): 32 + 36 = 68 = 4·17 ✓
  - (20, 12, 17): 20 + 48 = 68 ✓
  - (4, 20, 21): 4 + 80 = 84 = 4·21 ✓
  - (16, 17, 21): 16 + 68 = 84 ✓
  - (32, 13, 21): 32 + 52 = 84 ✓
  - (4, 12, 13): 4 + 48 = 52 = 4·13 ✓
  - (16, 13, 17): 16 + 52 = 68 ✓ (TERMINAL MONO with all C)
-/

set_option maxHeartbeats 400000 in
/-- ** chi(32) = chi(9) closure (cell 3)**: cell (3) + χ(32) = χ(9) ⟹
  False at n ≥ 32. 4-step cascade ending in terminal mono (16, 13, 17) all C. -/
theorem residual_cell_3_chi32_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h32_eq_9 : χ 32 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  -- Preamble: χ(20) = B ( + (16, 16, 20) ≠ C).
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_3_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 := h20_disj.resolve_right h20_ne_16
  -- S1: χ(17) = χ(16) (C). Via (32, 9, 17) ≠ A + (20, 12, 17) ≠ B.
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 9
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
    · show χ 9 = χ (9 + 8)
      rw [show (9 + 8 : ℕ) = 17 by decide, ← h17_eq_9]
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 12
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_12
    · show χ 12 = χ (12 + 5)
      rw [show (12 + 5 : ℕ) = 17 by decide, h17_eq_12]
  have h17_eq_16 : χ 17 = χ 16 :=
    third_color_eq hχ17 hχ16 hχ9 hχ12 h9_ne_12 h17_ne_9 h17_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- S2: χ(21) = χ(9) (A). Via (4, 20, 21) ≠ B + (16, 17, 21) ≠ C.
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12.trans h20_eq_12.symm
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  have h21_ne_16 : χ 21 ≠ χ 16 := by
    intro h21_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 17
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h17_eq_16.symm
    · show χ 17 = χ (17 + 4)
      rw [show (17 + 4 : ℕ) = 21 by decide, h17_eq_16, h21_eq_16]
  have h21_eq_9 : χ 21 = χ 9 :=
    third_color_eq hχ21 hχ9 hχ12 hχ16 h12_ne_16 h21_ne_12 h21_ne_16 h9_ne_12 h9_ne_16
  -- S3: χ(13) = χ(16) (C). Via (32, 13, 21) ≠ A + (4, 12, 13) ≠ B.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 13
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h13_eq_9]
    · show χ 13 = χ (13 + 8)
      rw [show (13 + 8 : ℕ) = 21 by decide, h13_eq_9, ← h21_eq_9]
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 12) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 12
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12
    · show χ 12 = χ (12 + 1)
      rw [show (12 + 1 : ℕ) = 13 by decide, h13_eq_12]
  have h13_eq_16 : χ 13 = χ 16 :=
    third_color_eq hχ13 hχ16 hχ9 hχ12 h9_ne_12 h13_ne_9 h13_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (16, 13, 17) mono with χ(16) = χ(13) = χ(17) = C.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 13
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h13_eq_16.symm
  · show χ 13 = χ (13 + 4)
    rw [show (13 + 4 : ℕ) = 17 by decide, h13_eq_16, ← h17_eq_16]

/-- ** contrapositive** (cell 3): χ(32) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi32_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 32 ≠ χ 9 := by
  intro h32_eq_9
  exact residual_cell_3_chi32_eq_chi9_forces_False χ h32 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h32_eq_9

/-- ** layer compression d=8 (cell 3)**: χ(32) ∈ {χ(12), χ(16)} under
  residual cell (3). -/
theorem residual_cell_3_layer_compression_d8
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 32 = χ 12 ∨ χ 32 = χ 16 := by
  have h32_ne_9 : χ 32 ≠ χ 9 :=
    residual_cell_3_chi32_ne_chi9 χ h32 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  by_cases h_eq_12 : χ 32 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ32 hχ16 hχ9 hχ12 h9_ne_12 h32_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §136. — residual cell (3) hLayer d = 9.

  **Target.** Under cell (3) hypotheses, prove χ(36) ∈ {χ(12), χ(16)}.

  **Clean self-loop terminal cascade** using (χ(20)=B), (χ(24) ∈ {B,C})
  and (χ(32) ∈ {B,C}). No case split.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P | χ(20) = B | + (16, 16, 20) [≠C] |
  | S1 | χ(18) = B | (36, 9, 18) [≠A; uses h36_eq_9] + (8, 16, 18) [≠C] |
  | S2 | χ(32) = C | + (32, 4, 12) [≠B; uses h4_eq_12] |
  | S3 | χ(24) = B | + (32, 24, 32) [≠C; uses S2] |
  | T | (24, 18, 24) MONO B | χ(24) = χ(18) = χ(24) = B |

  Threshold n ≥ 36 (uses position 36 in (36, 9, 18)).

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓
  - (36, 9, 18): 36 + 36 = 72 = 4·18 ✓
  - (8, 16, 18): 8 + 64 = 72 ✓
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (32, 24, 32): 32 + 96 = 128 = 4·32 ✓ (self-loop)
  - (24, 18, 24): 24 + 72 = 96 = 4·24 ✓ (TERMINAL self-loop MONO B)
-/

set_option maxHeartbeats 400000 in
/-- ** chi(36) = chi(9) closure (cell 3)**: cell (3) + χ(36) = χ(9) ⟹
  False at n ≥ 36. Cascade ending in self-loop terminal (24, 18, 24) all B. -/
theorem residual_cell_3_chi36_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h36_eq_9 : χ 36 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  -- Preamble P: χ(20) = B ( d=5 + (16, 16, 20) ≠ C).
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_3_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 := h20_disj.resolve_right h20_ne_16
  -- S1: χ(18) = B. Via (36, 9, 18) ≠ A + (8, 16, 18) ≠ C.
  have h18_ne_9 : χ 18 ≠ χ 9 := by
    intro h18_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 9) = χ 9
      rw [show (4 * 9 : ℕ) = 36 by decide]; exact h36_eq_9
    · show χ 9 = χ (9 + 9)
      rw [show (9 + 9 : ℕ) = 18 by decide, ← h18_eq_9]
  have h18_ne_16 : χ 18 ≠ χ 16 := by
    intro h18_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 16
      rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16
    · show χ 16 = χ (16 + 2)
      rw [show (16 + 2 : ℕ) = 18 by decide, h18_eq_16]
  have h18_eq_12 : χ 18 = χ 12 :=
    third_color_eq hχ18 hχ12 hχ9 hχ16 h9_ne_16 h18_ne_9 h18_ne_16 (Ne.symm h9_ne_12) h12_ne_16
  -- S2: χ(32) = C. Via d=8 + (32, 4, 12) ≠ B.
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_3_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12]; exact h4_eq_12.symm
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- S3: χ(24) = B. Via d=6 + (32, 24, 32) ≠ C.
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_3_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 24
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h24_eq_16]
    · show χ 24 = χ (24 + 8)
      rw [show (24 + 8 : ℕ) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- TERMINAL: (24, 18, 24) self-loop mono with χ(24) = χ(18) = χ(24) = B.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 6) = χ 18
    rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_12, ← h18_eq_12]
  · show χ 18 = χ (18 + 6)
    rw [show (18 + 6 : ℕ) = 24 by decide, h18_eq_12, ← h24_eq_12]

/-- ** contrapositive** (cell 3): χ(36) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi36_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 36 ≠ χ 9 := by
  intro h36_eq_9
  exact residual_cell_3_chi36_eq_chi9_forces_False χ h36 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h36_eq_9

/-- ** layer compression d=9 (cell 3)**: χ(36) ∈ {χ(12), χ(16)} under
  residual cell (3). -/
theorem residual_cell_3_layer_compression_d9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 36 = χ 12 ∨ χ 36 = χ 16 := by
  have h36_ne_9 : χ 36 ≠ χ 9 :=
    residual_cell_3_chi36_ne_chi9 χ h36 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ36 : χ 36 < 3 := hχk 36 (by omega) (by omega)
  by_cases h_eq_12 : χ 36 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ36 hχ16 hχ9 hχ12 h9_ne_12 h36_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §137. — residual cell (3) hLayer d = 10.

  **Target.** Under cell (3) hypotheses, prove χ(40) ∈ {χ(12), χ(16)}.

  **Minimal sharpening cascade via χ(30) = C terminal.**
  Uses // (d=5/6/8) to sharpen B/C anchors, then derives χ(30) = C
  via two self-loops, terminating in (8, 30, 32) all C.
  Notable: (d=7) and (d=9) are NOT used.

  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | P1 | χ(20) = B | + (16, 16, 20) [self-loop x=y; ≠C] |
  | P2 | χ(32) = C | + (32, 4, 12) [≠B] |
  | P3 | χ(24) = B | + (32, 24, 32) [self-loop x=z; ≠C] |
  | S1 | χ(30) ≠ B | (24, 24, 30) [self-loop x=y; uses χ(24)=B] |
  | S2 | χ(30) ≠ A | (40, 30, 40) [self-loop x=z; uses h40_eq_9] |
  | S3 | χ(30) = C | trichotomy |
  | T | (8, 30, 32) MONO C | χ(8) = χ(30) = χ(32) = C |

  Threshold n ≥ 40 (uses position 40 in (40, 30, 40)).

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓ (self-loop x=y)
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓
  - (32, 24, 32): 32 + 96 = 128 = 4·32 ✓ (self-loop x=z)
  - (24, 24, 30): 24 + 96 = 120 = 4·30 ✓ (self-loop x=y)
  - (40, 30, 40): 40 + 120 = 160 = 4·40 ✓ (self-loop x=z)
  - (8, 30, 32): 8 + 120 = 128 = 4·32 ✓ (TERMINAL MONO C)
-/

set_option maxHeartbeats 400000 in
/-- ** chi(40) = chi(9) closure (cell 3)**: cell (3) + χ(40) = χ(9) ⟹
  False at n ≥ 40. Cascade through χ(30) = C, terminating in (8, 30, 32) all C. -/
theorem residual_cell_3_chi40_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (h40_eq_9 : χ 40 = χ 9) :
    False := by
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ30 : χ 30 < 3 := hχk 30 (by omega) (by omega)
  -- P1: χ(20) = B ( d=5 + (16, 16, 20) ≠ C).
  have h20_disj : χ 20 = χ 12 ∨ χ 20 = χ 16 :=
    residual_cell_3_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h20_ne_16 : χ 20 ≠ χ 16 := by
    intro h20_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 16
      rw [show (4 * 4 : ℕ) = 16 by decide]
    · show χ 16 = χ (16 + 4)
      rw [show (16 + 4 : ℕ) = 20 by decide, h20_eq_16]
  have h20_eq_12 : χ 20 = χ 12 := h20_disj.resolve_right h20_ne_16
  -- P2: χ(32) = C ( d=8 + (32, 4, 12) ≠ B).
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_3_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12]; exact h4_eq_12.symm
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  have h32_eq_16 : χ 32 = χ 16 := h32_disj.resolve_left h32_ne_12
  -- P3: χ(24) = B ( d=6 + (32, 24, 32) ≠ C).
  have h24_disj : χ 24 = χ 12 ∨ χ 24 = χ 16 :=
    residual_cell_3_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have h24_ne_16 : χ 24 ≠ χ 16 := by
    intro h24_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 24
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h24_eq_16]
    · show χ 24 = χ (24 + 8)
      rw [show (24 + 8 : ℕ) = 32 by decide, h24_eq_16, ← h32_eq_16]
  have h24_eq_12 : χ 24 = χ 12 := h24_disj.resolve_right h24_ne_16
  -- S1: χ(30) ≠ B. Via (24, 24, 30) [self-loop x=y; uses χ(24)=B].
  have h30_ne_12 : χ 30 ≠ χ 12 := by
    intro h30_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 6) = χ 24
      rw [show (4 * 6 : ℕ) = 24 by decide]
    · show χ 24 = χ (24 + 6)
      rw [show (24 + 6 : ℕ) = 30 by decide, h24_eq_12, h30_eq_12]
  -- S2: χ(30) ≠ A. Via (40, 30, 40) [self-loop x=z; uses h40_eq_9].
  have h30_ne_9 : χ 30 ≠ χ 9 := by
    intro h30_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 10) (y := 30) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 10) = χ 30
      rw [show (4 * 10 : ℕ) = 40 by decide, h40_eq_9, ← h30_eq_9]
    · show χ 30 = χ (30 + 10)
      rw [show (30 + 10 : ℕ) = 40 by decide, h30_eq_9, ← h40_eq_9]
  -- S3: χ(30) = C (third color via trichotomy).
  have h30_eq_16 : χ 30 = χ 16 :=
    third_color_eq hχ30 hχ16 hχ9 hχ12 h9_ne_12 h30_ne_9 h30_ne_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)
  -- TERMINAL: (8, 30, 32) all C, χ(8) = χ(30) = χ(32) = C.
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 2) (y := 30) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 2) = χ 30
    rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_16, ← h30_eq_16]
  · show χ 30 = χ (30 + 2)
    rw [show (30 + 2 : ℕ) = 32 by decide, h30_eq_16, ← h32_eq_16]

/-- ** contrapositive** (cell 3): χ(40) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi40_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 40 ≠ χ 9 := by
  intro h40_eq_9
  exact residual_cell_3_chi40_eq_chi9_forces_False χ h40 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h40_eq_9

/-- ** layer compression d=10 (cell 3)**: χ(40) ∈ {χ(12), χ(16)} under
  residual cell (3). -/
theorem residual_cell_3_layer_compression_d10
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 40 = χ 12 ∨ χ 40 = χ 16 := by
  have h40_ne_9 : χ 40 ≠ χ 9 :=
    residual_cell_3_chi40_ne_chi9 χ h40 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ40 : χ 40 < 3 := hχk 40 (by omega) (by omega)
  by_cases h_eq_12 : χ 40 = χ 12
  · exact Or.inl h_eq_12
  · right
    exact third_color_eq hχ40 hχ16 hχ9 hχ12 h9_ne_12 h40_ne_9 h_eq_12 (Ne.symm h9_ne_16) (Ne.symm h12_ne_16)

/-! ### §138. — SHORTCUT discovery + residual cell (3) hLayer d = 11.

  **AUDIT SHORTCUT.** Triple (32, 8, 16) is a valid bAdicEquation 4 triple
  (d=8, y=8, z=16; 32 + 32 = 64 = 4·16 ✓). The general Rado constraint
  forces NOT (χ(32) = χ(8) ∧ χ(8) = χ(16)). Under cell (3) hypothesis
  h8_eq_16 : χ(8) = χ(16), the second conjunct holds always, so the
  constraint forces χ(32) ≠ χ(8) = χ(16) = C.

  Combined with d=8 (χ(32) ∈ {B, C}) and (32, 4, 12) excluding B,
  this gives an immediate contradiction at n ≥ 32 —
  **residual cell (3) hypotheses + hNoMono ⟹ False at n ≥ 32**.

  This means cell (3) closes immediately at n ≥ 32, and all hLayer facts
  for d ≥ 5 become trivial via False.elim. We introduce:
  - `residual_cell_3_closed_directly_at_32`: the direct closure theorem.
  - standard 3-theorem suite for d=11: trivial wrappers over the closure.

  - are kept as historical cascade proofs (not refactored).
  - (d=12..d=16) will follow the same shortcut pattern.

  Triples in direct closure (b=4):
  - (32, 4, 12): 32 + 16 = 48 = 4·12 ✓ (excludes χ(32) = B; from proof)
  - (32, 8, 16): 32 + 32 = 64 = 4·16 ✓ (excludes χ(32) = C; the new shortcut)
-/

set_option maxHeartbeats 400000 in
/-- ** direct closure of cell (3) at n ≥ 32.** Cell (3) hypotheses
  + hNoMono ⟹ False. Uses d=8 + (32, 4, 12) [≠B] + (32, 8, 16) [≠C].
  This shortcut subsumes - closures and trivially gives all
  cell (3) hLayer facts for d ≥ 5 via False.elim. -/
theorem residual_cell_3_closed_directly_at_32
    {n : ℕ} (χ : ℕ → ℕ) (h32 : 32 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    False := by
  have h32_disj : χ 32 = χ 12 ∨ χ 32 = χ 16 :=
    residual_cell_3_layer_compression_d8 χ h32 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
  -- (32, 4, 12) excludes χ(32) = B.
  have h32_ne_12 : χ 32 ≠ χ 12 := by
    intro h32_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 4
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12]; exact h4_eq_12.symm
    · show χ 4 = χ (4 + 8)
      rw [show (4 + 8 : ℕ) = 12 by decide]; exact h4_eq_12
  -- (32, 8, 16) excludes χ(32) = C. This is the new shortcut.
  have h32_ne_16 : χ 32 ≠ χ 16 := by
    intro h32_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 8
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_16, ← h8_eq_16]
    · show χ 8 = χ (8 + 8)
      rw [show (8 + 8 : ℕ) = 16 by decide]; exact h8_eq_16
  -- Trichotomy: χ(32) is neither B nor C, contradicting 's disjunction.
  exact h32_disj.elim h32_ne_12 h32_ne_16

/-- ** chi(44) = chi(9) closure (cell 3)**: cell (3) + χ(44) = χ(9) ⟹
  False at n ≥ 44. Trivial via `residual_cell_3_closed_directly_at_32`
  — the χ(44) = χ(9) hypothesis is unused because the direct closure
  already gives False from cell (3) hypotheses at n ≥ 32. -/
theorem residual_cell_3_chi44_eq_chi9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16)
    (_h44_eq_9 : χ 44 = χ 9) :
    False :=
  residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16

/-- ** contrapositive** (cell 3): χ(44) ≠ χ(9) under cell (3) hypotheses. -/
theorem residual_cell_3_chi44_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 44 ≠ χ 9 := by
  intro h44_eq_9
  exact residual_cell_3_chi44_eq_chi9_forces_False χ h44 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16 h44_eq_9

/-- ** layer compression d=11 (cell 3)**: χ(44) ∈ {χ(12), χ(16)} under
  residual cell (3). Trivially derived via the direct closure since
  cell (3) hypotheses imply False at n ≥ 32 (≤ 44). -/
theorem residual_cell_3_layer_compression_d11
    {n : ℕ} (χ : ℕ → ℕ) (h44 : 44 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 44 = χ 12 ∨ χ 44 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-! ### §139. — residual cell (3) hLayer d = 12..16 + full integration.

  **All five remaining hLayer disjuncts are trivial False.elim wrappers**
  over `residual_cell_3_closed_directly_at_32` ( SHORTCUT). They preserve
  API symmetry with - and cell (1)/(2) layer compression theorems.

  No cascade is needed for d=12..16 because cell (3) is already False at n ≥ 32.

  Following the same architecture as `residual_cell_2_full_layer_compression`,
  `residual_cell_3_full_layer_compression` dispatches via `interval_cases` on d:
  - d=1..4: direct from cell (3) anchor hypotheses + rfl.
  - d=5..10: existing cascade proofs (..).
  - d=11..16: False.elim wrappers via the SHORTCUT.
-/

/-- ** layer compression d=12 (cell 3)**: trivial via direct closure. -/
theorem residual_cell_3_layer_compression_d12
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 48 = χ 12 ∨ χ 48 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-- ** layer compression d=13 (cell 3)**: trivial via direct closure. -/
theorem residual_cell_3_layer_compression_d13
    {n : ℕ} (χ : ℕ → ℕ) (h52 : 52 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 52 = χ 12 ∨ χ 52 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-- ** layer compression d=14 (cell 3)**: trivial via direct closure. -/
theorem residual_cell_3_layer_compression_d14
    {n : ℕ} (χ : ℕ → ℕ) (h56 : 56 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 56 = χ 12 ∨ χ 56 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-- ** layer compression d=15 (cell 3)**: trivial via direct closure. -/
theorem residual_cell_3_layer_compression_d15
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 60 = χ 12 ∨ χ 60 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-- ** layer compression d=16 (cell 3)**: trivial via direct closure. -/
theorem residual_cell_3_layer_compression_d16
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    χ 64 = χ 12 ∨ χ 64 = χ 16 :=
  False.elim
    (residual_cell_3_closed_directly_at_32 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-- ** cell (3) full layer compression**: assembles the bridge interface
  `∀ d, 1 ≤ d → d ≤ 16 → χ(4·d) = χ(12) ∨ χ(4·d) = χ(16)` from cell (3)
  hypotheses. Mirrors `residual_cell_2_full_layer_compression`.

  Dispatch:
  - d=1: h4_eq_12 (left). - d=2: h8_eq_16 (right).
  - d=3: χ(12) = χ(12) rfl. - d=4: χ(16) = χ(16) rfl.
  - d=5..10:.. cascade proofs.
  - d=11..16:.. False.elim shortcuts.
-/
theorem residual_cell_3_full_layer_compression
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16 := by
  intro d hd1 hd16
  interval_cases d
  · -- d = 1: χ(4) = χ(12) by h4_eq_12 (left branch).
    exact Or.inl (show χ (4 * 1) = χ 12 by rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_12)
  · -- d = 2: χ(8) = χ(16) by h8_eq_16 (right branch).
    exact Or.inr (show χ (4 * 2) = χ 16 by rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_16)
  · -- d = 3: χ(12) = χ(12) by rfl.
    exact Or.inl (show χ (4 * 3) = χ 12 by rw [show (4 * 3 : ℕ) = 12 by decide])
  · -- d = 4: χ(16) = χ(16) by rfl.
    exact Or.inr (show χ (4 * 4) = χ 16 by rw [show (4 * 4 : ℕ) = 16 by decide])
  · -- d = 5:.
    have h := residual_cell_3_layer_compression_d5 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 5 : ℕ) = 20 by decide]; exact h
  · -- d = 6:.
    have h := residual_cell_3_layer_compression_d6 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 6 : ℕ) = 24 by decide]; exact h
  · -- d = 7:.
    have h := residual_cell_3_layer_compression_d7 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 7 : ℕ) = 28 by decide]; exact h
  · -- d = 8:.
    have h := residual_cell_3_layer_compression_d8 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 8 : ℕ) = 32 by decide]; exact h
  · -- d = 9:.
    have h := residual_cell_3_layer_compression_d9 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 9 : ℕ) = 36 by decide]; exact h
  · -- d = 10:.
    have h := residual_cell_3_layer_compression_d10 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 10 : ℕ) = 40 by decide]; exact h
  · -- d = 11: (SHORTCUT wrapper).
    have h := residual_cell_3_layer_compression_d11 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 11 : ℕ) = 44 by decide]; exact h
  · -- d = 12: SHORTCUT wrapper.
    have h := residual_cell_3_layer_compression_d12 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 12 : ℕ) = 48 by decide]; exact h
  · -- d = 13: SHORTCUT wrapper.
    have h := residual_cell_3_layer_compression_d13 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 13 : ℕ) = 52 by decide]; exact h
  · -- d = 14: SHORTCUT wrapper.
    have h := residual_cell_3_layer_compression_d14 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 14 : ℕ) = 56 by decide]; exact h
  · -- d = 15: SHORTCUT wrapper.
    have h := residual_cell_3_layer_compression_d15 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 15 : ℕ) = 60 by decide]; exact h
  · -- d = 16: SHORTCUT wrapper.
    have h := residual_cell_3_layer_compression_d16 χ (by omega) hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    rw [show (4 * 16 : ℕ) = 64 by decide]; exact h

end RadoNumbers.General
