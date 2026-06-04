/-
  RadoNumbers/General/Bridge.lean

  BRIDGE between general LinearEquation framework and project-specific
  Rado triple predicates (RadoNumbers.IsRadoTriple, RadoNumbers.HasMonoSolution).

  Specifically, for the b-adic equation x + b·y - b·z = 0:
  - General's `HasMonoSolution (bAdicEquation b) n χ` is equivalent to
    project's `HasMonoSolution b n χ` (for the same b).

  This lets us specialize general theorems (eventually Rado's theorem) to
  prove project-specific results without case enumeration.
-/

import RadoNumbers.General.BAdicEquation
import RadoNumbers.General.BasicResults
import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.Foundational
-- R246: removed `import RadoNumbers.K3B3` to break the cycle
-- (Bridge.lean now provides kernel-pure `thm_k3b3_kernel_pure` in §40.5,
--  which K3B3.lean uses to define `RadoNumbers.thm_k3b3` kernel-pure).
import RadoNumbers.K4B3
import RadoNumbers.SAT
import RadoNumbers.Breakdown
import RadoNumbers.DPLStructure
import RadoNumbers.K3General
import RadoNumbers.Pillar3Structural

namespace RadoNumbers.General

/--
  **General-to-project bridge** for b-adic equation:
  if there's a general-form mono solution to `bAdicEquation b`, then
  there's a project-form mono Rado triple.

  Direction: ← (general → project).
-/
theorem hasMonoSolution_bAdicEquation_to_project (b n : ℕ) (χ : ℕ → ℕ)
    (hg : HasMonoSolution (bAdicEquation b) n χ) :
    RadoNumbers.HasMonoSolution b n χ := by
  obtain ⟨f, hbound, hpos, hcolor⟩ := hg
  -- Variables: f 0, f 1, f 2 (corresponding to x, y, z).
  refine ⟨f 0, f 1, f 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbound 0 (by simp [bAdicEquation, LinearEquation.numVars])
  · exact hbound 1 (by simp [bAdicEquation, LinearEquation.numVars])
  · exact hbound 2 (by simp [bAdicEquation, LinearEquation.numVars])
  · -- IsRadoTriple b (f 0) (f 1) (f 2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hpos.1 0 (by simp [bAdicEquation, LinearEquation.numVars])
    · exact hpos.1 1 (by simp [bAdicEquation, LinearEquation.numVars])
    · exact hpos.1 2 (by simp [bAdicEquation, LinearEquation.numVars])
    · -- f 0 + b · f 1 = b · f 2 from eval = 0.
      have heval := hpos.2
      -- heval : eval (bAdicEquation b) (fun i => (f i : ℤ)) = 0.
      -- Need: f 0 + b * f 1 = b * f 2 in ℕ.
      -- Unfold eval bAdicEquation:
      have : ((f 0 : ℤ) + (b : ℤ) * (f 1 : ℤ) - (b : ℤ) * (f 2 : ℤ)) = 0 := by
        have := heval
        unfold bAdicEquation LinearEquation.eval at this
        simp [List.zipIdx] at this
        linarith
      -- Convert ℤ equation to ℕ equation.
      have hzeq : (f 0 : ℤ) + (b : ℤ) * (f 1 : ℤ) = (b : ℤ) * (f 2 : ℤ) := by linarith
      exact_mod_cast hzeq
  · -- χ (f 0) = χ (f 1)
    exact hcolor 0 1 (by simp [bAdicEquation, LinearEquation.numVars])
                       (by simp [bAdicEquation, LinearEquation.numVars])
  · -- χ (f 1) = χ (f 2)
    exact hcolor 1 2 (by simp [bAdicEquation, LinearEquation.numVars])
                       (by simp [bAdicEquation, LinearEquation.numVars])

/--
  **Project-to-general bridge** for b-adic equation:
  given a project-form mono Rado triple, construct a general-form
  mono solution.

  Direction: → (project → general).

  Construction: encode the 3-tuple (x, y, z) as f : ℕ → ℕ with
  f 0 = x, f 1 = y, f 2 = z (other values irrelevant).
-/
theorem hasMonoSolution_bAdicEquation_from_project (b n : ℕ) (χ : ℕ → ℕ)
    (hp : RadoNumbers.HasMonoSolution b n χ) :
    HasMonoSolution (bAdicEquation b) n χ := by
  obtain ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩ := hp
  refine ⟨fun i => if i = 0 then x else if i = 1 then y else z, ?_, ?_, ?_⟩
  · -- ∀ i < numVars, f i ≤ n
    intro i hi
    simp [bAdicEquation, LinearEquation.numVars] at hi
    interval_cases i <;> simp [hxn, hyn, hzn]
  · -- IsPositiveSolution
    refine ⟨?_, ?_⟩
    · -- ∀ i < numVars, 0 < f i
      intro i hi
      simp [bAdicEquation, LinearEquation.numVars] at hi
      interval_cases i <;> simp [hx, hy, hz]
    · -- eval = 0
      have hzeq : ((x : ℤ) + (b : ℤ) * (y : ℤ)) = ((b : ℤ) * (z : ℤ)) := by
        exact_mod_cast heq
      unfold bAdicEquation LinearEquation.eval
      simp [List.zipIdx]
      linarith
  · -- All colors equal: χ (f i) = χ (f j) for i, j < 3.
    intro i j hi hj
    simp [bAdicEquation, LinearEquation.numVars] at hi hj
    -- Reduce to 9 cases for (i, j) ∈ {0,1,2}².
    have hxz : χ x = χ z := hxy.trans hyz
    interval_cases i <;> interval_cases j <;> simp
    · -- (0, 1): χ x = χ y
      exact hxy
    · -- (0, 2): χ x = χ z
      exact hxz
    · -- (1, 0): χ y = χ x
      exact hxy.symm
    · -- (1, 2): χ y = χ z
      exact hyz
    · -- (2, 0): χ z = χ x
      exact hxz.symm
    · -- (2, 1): χ z = χ y
      exact hyz.symm

/--
  **Full bridge equivalence** for b-adic equation HasMonoSolution.
-/
theorem hasMonoSolution_bAdicEquation_iff (b n : ℕ) (χ : ℕ → ℕ) :
    HasMonoSolution (bAdicEquation b) n χ ↔ RadoNumbers.HasMonoSolution b n χ :=
  ⟨hasMonoSolution_bAdicEquation_to_project b n χ,
   hasMonoSolution_bAdicEquation_from_project b n χ⟩

/-! ### §35. Bridge from project's RadoNumberAtLeast to general's failure of IsKPartitionRegularAt. -/

/--
  **Project IsValidColoring = General IsKColoring** (definitionally equal).
-/
theorem isValidColoring_eq_isKColoring (n k : ℕ) (χ : ℕ → ℕ) :
    RadoNumbers.IsValidColoring n k χ ↔ IsKColoring n k χ := by
  unfold RadoNumbers.IsValidColoring IsKColoring
  rfl

/--
  **Project RadoNumberAtLeast → General ¬ IsKPartitionRegularAt.**

  If project's lower bound says R_k(b) ≥ N (via `RadoNumberAtLeast b k N`),
  then in general framework, bAdicEquation b is NOT k-partition-regular
  at bound N - 1.

  This bridges project's `thm_lower : RadoNumberAtLeast 3 3 (3^3)` to
  the general framework's "no partition regularity at 26" for radoEq_3.
-/
theorem not_isKPartitionRegularAt_of_radoNumberAtLeast
    (b k N : ℕ) (h : RadoNumbers.RadoNumberAtLeast b k N) :
    ¬ IsKPartitionRegularAt (bAdicEquation b) k (N - 1) := by
  intro hPR
  obtain ⟨χ, hValid, hAvoid⟩ := h
  have hχColoring : IsKColoring (N - 1) k χ :=
    (isValidColoring_eq_isKColoring (N - 1) k χ).mp hValid
  have hMono := hPR χ hχColoring
  -- hMono : HasMonoSolution (bAdicEquation b) (N - 1) χ.
  have hProjectMono := hasMonoSolution_bAdicEquation_to_project b (N - 1) χ hMono
  exact hAvoid hProjectMono

/--
  **General `IsKPartitionRegularAt` for b-adic equation ↔ project: "no
  mono-free coloring of [1, N] in k colors".**

  Combines the Bridge equivalence with definition unfolding.
-/
theorem isKPartitionRegularAt_bAdicEquation_iff (b k N : ℕ) :
    IsKPartitionRegularAt (bAdicEquation b) k N ↔
    ∀ χ : ℕ → ℕ, RadoNumbers.IsValidColoring N k χ →
      ¬ RadoNumbers.AvoidsMonoSolution b N χ := by
  constructor
  · intro hPR χ hValid hAvoid
    have hχColoring : IsKColoring N k χ :=
      (isValidColoring_eq_isKColoring N k χ).mp hValid
    have hMono := hPR χ hχColoring
    have hProjectMono := hasMonoSolution_bAdicEquation_to_project b N χ hMono
    exact hAvoid hProjectMono
  · intro h χ hχColoring
    have hValid : RadoNumbers.IsValidColoring N k χ :=
      (isValidColoring_eq_isKColoring N k χ).mpr hχColoring
    -- AvoidsMono = ¬ HasMono. ¬ (¬ HasMono) requires Classical for general χ.
    have hProjMono : RadoNumbers.HasMonoSolution b N χ := by
      by_contra hNoMono
      exact h χ hValid hNoMono
    exact hasMonoSolution_bAdicEquation_from_project b N χ hProjMono

/--
  **GENERAL LOWER BOUND** `R_b(k) ≥ b^k` for b-adic equation:
  bAdicEquation b is NOT k-partition-regular at bound b^k - 1.

  Direct generalization via thm_lower (valuation coloring) + bridge.

  This is the lower bound direction of the threshold conjecture:
  R_k(b) ≥ b^k for any b ≥ 2, k ≥ 1.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one
    (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ¬ IsKPartitionRegularAt (bAdicEquation b) k (b ^ k - 1) := by
  apply not_isKPartitionRegularAt_of_radoNumberAtLeast b k (b ^ k)
  exact RadoNumbers.thm_lower b k hb hk

/--
  **R_3(3) ≥ 27 in general framework** (specialization of general bound).
-/
theorem not_isKPartitionRegularAt_radoEq_3_at_26 :
    ¬ IsKPartitionRegularAt radoEq_3 3 26 := by
  have h := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one 3 3 (by omega) (by omega)
  -- h : ¬ IsKPartitionRegularAt (bAdicEquation 3) 3 (3^3 - 1).
  show ¬ IsKPartitionRegularAt (bAdicEquation 3) 3 26
  have h26 : (3 : ℕ)^3 - 1 = 26 := by decide
  rw [← h26]
  exact h

/--
  **R_3(3) = 27 reduces to the upper bound only**: given the lower bound
  R_3(3) ≥ 27 (already proven), `IsRadoNumber radoEq_3 3 27` is equivalent
  to `IsKPartitionRegularAt radoEq_3 3 27` (= Pillar 3 upper bound).

  Uses monotonicity: ¬ partition-regular at 26 implies ¬ partition-regular
  at any M < 27 (by isKPartitionRegularAt_mono contrapositive).
-/
theorem isRadoNumber_radoEq_3_27_iff_pillar3 :
    IsRadoNumber radoEq_3 3 27 ↔ IsKPartitionRegularAt radoEq_3 3 27 := by
  constructor
  · intro ⟨h, _⟩; exact h
  · intro hUpper
    refine ⟨hUpper, ?_⟩
    intro M hM
    -- M < 27, so M ≤ 26.
    intro hPR
    apply not_isKPartitionRegularAt_radoEq_3_at_26
    exact isKPartitionRegularAt_mono radoEq_3 3 M 26 (by omega) hPR

/--
  **R_3(3) = 27 from Pillar 3** (conditional final theorem).

  Assuming the Pillar 3 upper bound (IsKPartitionRegularAt radoEq_3 3 27),
  the Rado number is EXACTLY 27 — combining with the already-proven lower
  bound (not partition-regular at 26).

  This is the FINAL conditional reduction. Once Pillar 3 is proven (via
  structural insight or general Rado theorem application), R_3(3) = 27
  follows immediately.
-/
theorem isRadoNumber_radoEq_3_27_from_pillar3
    (hPillar3 : IsKPartitionRegularAt radoEq_3 3 27) :
    IsRadoNumber radoEq_3 3 27 :=
  (isRadoNumber_radoEq_3_27_iff_pillar3).mpr hPillar3

/-! ### §36. Concrete instance: R_1(b) = b (1-color Rado number). -/

/--
  **R_1(b) = b**: for b ≥ 2, the 1-color Rado number of x + b·y - b·z = 0
  is exactly b.

  Lower bound: at b - 1 = b^1 - 1, valuation coloring (trivial since k=1)
    gives no mono solution.

  Upper bound: at b, the positive solution (b, 1, 2) lies in [1, b]^3
    (since b ≥ 2). With k=1, all colors are 0, so this solution is mono.
-/
theorem isRadoNumber_bAdicEquation_one (b : ℕ) (hb : 2 ≤ b) :
    IsRadoNumber (bAdicEquation b) 1 b := by
  apply isRadoNumber_of_bounds _ _ _ (by omega)
  · -- Upper bound: IsKPartitionRegularAt at b.
    apply isKPartitionRegularAt_one_of_hasPosSolution
    refine ⟨fun i => if i = 0 then b else if i = 1 then 1 else 2, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · -- ∀ i < numVars, 0 < f i.
      intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      interval_cases i <;> simp <;> omega
    · -- eval = 0.
      rw [eval_bAdicEquation]
      simp
      ring
    · -- ∀ i < numVars, f i ≤ b.
      intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      interval_cases i <;> simp <;> omega
  · -- Lower bound: ¬ IsKPartitionRegularAt at b - 1 = b^1 - 1.
    have h := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one b 1 hb (by omega)
    have hbm : b ^ 1 = b := pow_one b
    rw [hbm] at h
    exact h

/-! ### §36.5. Bridge: project's IsRadoNumber ↔ general's IsRadoNumber. -/

/--
  **Project's RadoNumberAtMost ↔ general's IsKPartitionRegularAt** for b-adic eq.
-/
theorem radoNumberAtMost_iff_isKPartitionRegularAt (b k N : ℕ) :
    RadoNumbers.RadoNumberAtMost b k N ↔
    IsKPartitionRegularAt (bAdicEquation b) k N := by
  unfold RadoNumbers.RadoNumberAtMost IsKPartitionRegularAt
  constructor
  · intro h χ hχk
    have hValid : RadoNumbers.IsValidColoring N k χ :=
      (isValidColoring_eq_isKColoring N k χ).mpr hχk
    have hMono := h χ hValid
    exact (hasMonoSolution_bAdicEquation_iff b N χ).mpr hMono
  · intro h χ hValid
    have hχk : IsKColoring N k χ := (isValidColoring_eq_isKColoring N k χ).mp hValid
    have hMono := h χ hχk
    exact (hasMonoSolution_bAdicEquation_iff b N χ).mp hMono

/--
  **General's `IsRadoNumber (bAdicEquation b) k N` → project's `IsRadoNumber b k N`.**

  General's notion (partition-regular at N + not at smaller M) plus
  monotonicity implies project's (partition-regular at N + has mono-free
  coloring at N-1).
-/
theorem isRadoNumber_project_of_general (b k N : ℕ) (hN : 1 ≤ N)
    (h : IsRadoNumber (bAdicEquation b) k N) :
    RadoNumbers.IsRadoNumber b k N := by
  obtain ⟨hUpper, hMin⟩ := h
  refine ⟨?_, ?_⟩
  · -- RadoNumberAtLeast b k N: ∃ χ mono-free coloring of [1, N-1].
    -- From hMin at M = N - 1: ¬ IsKPartitionRegularAt eq k (N - 1).
    -- Unfold: ∃ χ IsKColoring (N-1) k χ ∧ ¬ HasMonoSolution.
    have hNotAt : ¬ IsKPartitionRegularAt (bAdicEquation b) k (N - 1) :=
      hMin (N - 1) (by omega)
    -- Extract counterexample.
    classical
    by_contra hNoCounter
    apply hNotAt
    intro χ hχk
    -- hNoCounter says no χ with IsValidColoring (N-1) k ∧ AvoidsMono. Equivalent to:
    -- ∀ χ IsValidColoring (N-1) k → HasMono.
    have hValid : RadoNumbers.IsValidColoring (N - 1) k χ :=
      (isValidColoring_eq_isKColoring (N - 1) k χ).mpr hχk
    have : ¬ (RadoNumbers.IsValidColoring (N - 1) k χ ∧
              RadoNumbers.AvoidsMonoSolution b (N - 1) χ) := by
      intro hAnd
      exact hNoCounter ⟨χ, hAnd.1, hAnd.2⟩
    have hHasMono : RadoNumbers.HasMonoSolution b (N - 1) χ := by
      by_contra hh
      exact this ⟨hValid, hh⟩
    exact (hasMonoSolution_bAdicEquation_iff b (N - 1) χ).mpr hHasMono
  · -- RadoNumberAtMost b k N from hUpper.
    exact (radoNumberAtMost_iff_isKPartitionRegularAt b k N).mpr hUpper

/-! ### §37. R_2(2) = 4 (b=2, k=2 case of threshold conjecture). -/

/--
  **R_2(2) = 4**: the 2-color Rado number for equation x + 2y - 2z = 0 is 4.

  Lower bound: at 3 = 2^2 - 1, valuation coloring χ_v(n) = bAdicVal 2 n mod 2
    gives mono-free coloring.

  Upper bound: at 4, structural constraint propagation forces mono:
    - Self-loop (2, 1, 2): χ(1) ≠ χ(2). Else mono.
    - Triple (2, 2, 3): χ(2) ≠ χ(3). Else mono.
    - Self-loop (4, 2, 4): χ(2) ≠ χ(4). Else mono.
    - With k=2 colors, χ(1) = χ(3) = χ(4) (all ≠ χ(2)).
    - Triple (4, 1, 3): χ(4) = χ(1) = χ(3). MONO!

  Verifies threshold conjecture at (b, k) = (2, 2): 2 ≤ 2(2-1) = 2 ✓.
-/
theorem isRadoNumber_bAdicEquation_two_two :
    IsRadoNumber (bAdicEquation 2) 2 4 := by
  apply isRadoNumber_of_bounds _ _ _ (by omega)
  · -- Upper bound: IsKPartitionRegularAt (bAdicEquation 2) 2 4.
    intro χ hχk
    have hχ1 : χ 1 < 2 := hχk 1 (by omega) (by omega)
    have hχ2 : χ 2 < 2 := hχk 2 (by omega) (by omega)
    have hχ3 : χ 3 < 2 := hχk 3 (by omega) (by omega)
    have hχ4 : χ 4 < 2 := hχk 4 (by omega) (by omega)
    -- Helper: construct HasMonoSolution from explicit (x, y, z).
    have mkMono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
        x ≤ 4 → y ≤ 4 → z ≤ 4 →
        (x : ℤ) + 2 * (y : ℤ) = 2 * (z : ℤ) →
        χ x = χ y → χ y = χ z → HasMonoSolution (bAdicEquation 2) 4 χ := by
      intro x y z hx hy hz hxn hyn hzn heq hxy hyz
      refine ⟨fun i => if i = 0 then x else if i = 1 then y else z, ?_, ?_, ?_⟩
      · intro i hi
        have hnv : (bAdicEquation 2).numVars = 3 := bAdicEquation_numVars 2
        rw [hnv] at hi
        interval_cases i <;> simp <;> omega
      · refine ⟨?_, ?_⟩
        · intro i hi
          have hnv : (bAdicEquation 2).numVars = 3 := bAdicEquation_numVars 2
          rw [hnv] at hi
          interval_cases i <;> simp <;> assumption
        · rw [eval_bAdicEquation]
          simp
          linarith
      · intro i j hi hj
        have hnv : (bAdicEquation 2).numVars = 3 := bAdicEquation_numVars 2
        rw [hnv] at hi hj
        have hxz : χ x = χ z := hxy.trans hyz
        interval_cases i <;> interval_cases j <;> simp
        · exact hxy
        · exact hxz
        · exact hxy.symm
        · exact hyz
        · exact hxz.symm
        · exact hyz.symm
    -- Constraint propagation:
    by_cases h12 : χ 1 = χ 2
    · -- Mono via (2, 1, 2) self-loop.
      exact mkMono 2 1 2 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by norm_num)
        h12.symm h12
    · by_cases h23 : χ 2 = χ 3
      · -- Mono via (2, 2, 3): χ(2) = χ(2) = χ(3).
        exact mkMono 2 2 3 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by norm_num)
          rfl h23
      · by_cases h24 : χ 2 = χ 4
        · -- Mono via (4, 2, 4) self-loop.
          exact mkMono 4 2 4 (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by norm_num)
            h24.symm h24
        · -- All χ(1), χ(3), χ(4) ≠ χ(2). With 2 colors, all = the OTHER color.
          -- So χ(1) = χ(3) = χ(4). Mono via (4, 1, 3).
          have h13 : χ 1 = χ 3 := by omega
          have h34 : χ 1 = χ 4 := by omega
          exact mkMono 4 1 3 (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by norm_num)
            h34.symm h13
  · -- Lower bound: ¬ IsKPartitionRegularAt at 3 = 2^2 - 1.
    have h := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one 2 2
      (by omega) (by omega)
    have hbm : (2 : ℕ) ^ 2 - 1 = 3 := by decide
    rw [hbm] at h
    exact h

/-! ### §37.5. R_2(3) = 9 (b=3, k=2 case of threshold conjecture). -/

/--
  **R_2(3) = 9**: the 2-color Rado number for equation x + 3y - 3z = 0 is 9.

  Structural constraint propagation (no brute case enum):
  - WLOG chi(1) = 0 OR 1 (case split on chi(1)).
  - For each value of chi(1), self-loops (chi(2)≠chi(3), chi(3)≠chi(4),
    chi(4)≠chi(6), chi(6)≠chi(9), chi(6)≠chi(8)) plus the constraint
    (3,1,2) chi(3)=chi(1)=chi(2)=0 forbidden propagate to force chi values.
  - In each branch, a specific Rado triple (9,1,4) or (6,3,5) gives mono.

  Verifies threshold conjecture at (b, k) = (3, 2): 2 ≤ 2(3-1) = 4 ✓.
-/
theorem isRadoNumber_bAdicEquation_two_three :
    IsRadoNumber (bAdicEquation 3) 2 9 := by
  apply isRadoNumber_of_bounds _ _ _ (by omega)
  · -- Upper bound: IsKPartitionRegularAt (bAdicEquation 3) 2 9.
    intro χ hχk
    have hχ1 : χ 1 < 2 := hχk 1 (by omega) (by omega)
    have hχ2 : χ 2 < 2 := hχk 2 (by omega) (by omega)
    have hχ3 : χ 3 < 2 := hχk 3 (by omega) (by omega)
    have hχ4 : χ 4 < 2 := hχk 4 (by omega) (by omega)
    have hχ5 : χ 5 < 2 := hχk 5 (by omega) (by omega)
    have hχ6 : χ 6 < 2 := hχk 6 (by omega) (by omega)
    have hχ8 : χ 8 < 2 := hχk 8 (by omega) (by omega)
    have hχ9 : χ 9 < 2 := hχk 9 (by omega) (by omega)
    -- Helper: construct HasMonoSolution from explicit (x, y, z).
    have mkMono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
        x ≤ 9 → y ≤ 9 → z ≤ 9 →
        (x : ℤ) + 3 * (y : ℤ) = 3 * (z : ℤ) →
        χ x = χ y → χ y = χ z → HasMonoSolution (bAdicEquation 3) 9 χ := by
      intro x y z hx hy hz hxn hyn hzn heq hxy hyz
      refine ⟨fun i => if i = 0 then x else if i = 1 then y else z, ?_, ?_, ?_⟩
      · intro i hi
        have hnv : (bAdicEquation 3).numVars = 3 := bAdicEquation_numVars 3
        rw [hnv] at hi
        interval_cases i <;> simp <;> omega
      · refine ⟨?_, ?_⟩
        · intro i hi
          have hnv : (bAdicEquation 3).numVars = 3 := bAdicEquation_numVars 3
          rw [hnv] at hi
          interval_cases i <;> simp <;> assumption
        · rw [eval_bAdicEquation]
          simp
          linarith
      · intro i j hi hj
        have hnv : (bAdicEquation 3).numVars = 3 := bAdicEquation_numVars 3
        rw [hnv] at hi hj
        have hxz : χ x = χ z := hxy.trans hyz
        interval_cases i <;> interval_cases j <;> simp
        · exact hxy
        · exact hxz
        · exact hxy.symm
        · exact hyz
        · exact hxz.symm
        · exact hyz.symm
    -- Constraint chain:
    -- (3, 1, 2) mono iff chi(3) = chi(1) = chi(2). chi(2) ≠ chi(3) self-loop.
    -- So chi(2) = chi(1) = chi(3) impossible. But (3, 1, 2) needs all equal.
    -- Actually self-loop (3, 2, 3) gives chi(2) ≠ chi(3) directly.
    by_cases h23 : χ 2 = χ 3
    · -- mono via (3, 2, 3): chi(3) = chi(2) = chi(3).
      exact mkMono 3 2 3 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by norm_num)
        h23.symm h23
    · -- chi(2) ≠ chi(3). Continue.
      by_cases h34 : χ 3 = χ 4
      · -- mono via self-loop (3, 3, 4): chi(3) = chi(3) = chi(4).
        exact mkMono 3 3 4 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by norm_num)
          rfl h34
      · by_cases h46 : χ 4 = χ 6
        · -- mono via (6, 4, 6) self-loop: chi(6) = chi(4) = chi(6).
          exact mkMono 6 4 6 (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by norm_num)
            h46.symm h46
        · by_cases h69 : χ 6 = χ 9
          · -- mono via (9, 6, 9) self-loop.
            exact mkMono 9 6 9 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by norm_num)
              h69.symm h69
          · by_cases h13 : χ 1 = χ 3
            · -- (6, 1, 3) check: chi(6) = chi(1) = chi(3). chi(1) = chi(3).
              -- For mono need chi(6) = chi(1) = chi(3). With 2 colors, chi(6) ∈ {0, 1}.
              -- chi(4) ≠ chi(3) and chi(4) ≠ chi(6). So chi(6) = chi(3) (other than chi(4)).
              -- Thus chi(6) = chi(1) = chi(3). Mono via (6, 1, 3).
              have h16 : χ 1 = χ 6 := by omega
              exact mkMono 6 1 3 (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega) (by norm_num)
                h16.symm h13
            · -- chi(1) ≠ chi(3). With 2 colors and chi(2) ≠ chi(3), chi(1) = chi(2).
              -- Then chi(4) ≠ chi(3) → chi(4) = chi(1). chi(6) ≠ chi(4) → chi(6) = chi(3).
              -- chi(9) ≠ chi(6) → chi(9) = chi(4) = chi(1).
              -- (9, 1, 4): chi(9) = chi(1) = chi(4). All equal. MONO.
              have h14 : χ 1 = χ 4 := by omega
              have h94 : χ 9 = χ 4 := by omega
              have h19 : χ 1 = χ 9 := by omega
              exact mkMono 9 1 4 (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega) (by norm_num)
                h19.symm h14
  · -- Lower bound: ¬ IsKPartitionRegularAt at 8 = 3^2 - 1.
    have h := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one 3 2
      (by omega) (by omega)
    have hbm : (3 : ℕ) ^ 2 - 1 = 8 := by decide
    rw [hbm] at h
    exact h

/-! ### §38. Project-level Rado number corollaries. -/

/--
  **R_1(b) = b in project's IsRadoNumber notation** for b ≥ 2.

  Direct corollary of general's `isRadoNumber_bAdicEquation_one` + bridge.
-/
theorem isRadoNumber_project_one (b : ℕ) (hb : 2 ≤ b) :
    RadoNumbers.IsRadoNumber b 1 b :=
  isRadoNumber_project_of_general b 1 b (by omega)
    (isRadoNumber_bAdicEquation_one b hb)

/--
  **R_2(2) = 4 in project's IsRadoNumber notation**.

  Direct corollary of general's `isRadoNumber_bAdicEquation_two_two` + bridge.
-/
theorem isRadoNumber_project_two_two :
    RadoNumbers.IsRadoNumber 2 2 4 :=
  isRadoNumber_project_of_general 2 2 4 (by omega)
    isRadoNumber_bAdicEquation_two_two

/--
  **R_2(3) = 9 in project's IsRadoNumber notation**.

  Direct corollary of general's `isRadoNumber_bAdicEquation_two_three` + bridge.
  Third unconditional Rado number proven in the framework, validates
  threshold conjecture at (b, k) = (3, 2) since 2 ≤ 2(3-1) = 4 ✓.
-/
theorem isRadoNumber_project_two_three :
    RadoNumbers.IsRadoNumber 3 2 9 :=
  isRadoNumber_project_of_general 3 2 9 (by omega)
    isRadoNumber_bAdicEquation_two_three

/-! ### §39. Reverse bridge: project's IsRadoNumber → general's IsRadoNumber. -/

/--
  **Project IsRadoNumber → General IsRadoNumber** for b-adic equation (reverse
  bridge to `isRadoNumber_project_of_general`).

  Construction:
  - General's upper bound (`IsKPartitionRegularAt eq k N`) comes from project's
    `RadoNumberAtMost b k N` via `radoNumberAtMost_iff_isKPartitionRegularAt`.
  - General's minimality (`∀ M < N, ¬ IsKPartitionRegularAt eq k M`) comes
    from project's `RadoNumberAtLeast b k N`: the witness χ at level N - 1 also
    witnesses at any M ≤ N - 1 (restriction preserves k-coloring and avoidance).
-/
theorem isRadoNumber_general_of_project (b k N : ℕ) (hN : 1 ≤ N)
    (h : RadoNumbers.IsRadoNumber b k N) :
    IsRadoNumber (bAdicEquation b) k N := by
  obtain ⟨hAtLeast, hAtMost⟩ := h
  refine ⟨?_, ?_⟩
  · -- IsKPartitionRegularAt (bAdicEquation b) k N from RadoNumberAtMost.
    exact (radoNumberAtMost_iff_isKPartitionRegularAt b k N).mp hAtMost
  · -- ∀ M < N, ¬ IsKPartitionRegularAt at M.
    -- Step 1: ¬ IsKPartitionRegularAt at N - 1 (from RadoNumberAtLeast witness).
    have hNotAt_N_minus_one : ¬ IsKPartitionRegularAt (bAdicEquation b) k (N - 1) := by
      intro hPR
      obtain ⟨χ, hValid, hAvoid⟩ := hAtLeast
      have hχk : IsKColoring (N - 1) k χ :=
        (isValidColoring_eq_isKColoring (N - 1) k χ).mp hValid
      have hMono := hPR χ hχk
      have hProjectMono :=
        hasMonoSolution_bAdicEquation_to_project b (N - 1) χ hMono
      exact hAvoid hProjectMono
    -- Step 2: monotonicity (contrapositive) — ¬ at N - 1 → ¬ at any M ≤ N - 1.
    intro M hM hPR_M
    apply hNotAt_N_minus_one
    exact isKPartitionRegularAt_mono _ _ M (N - 1) (by omega) hPR_M

/--
  **Full equivalence**: project's IsRadoNumber ↔ general's IsRadoNumber
  for the b-adic equation.
-/
theorem isRadoNumber_bAdicEquation_iff_project (b k N : ℕ) (hN : 1 ≤ N) :
    IsRadoNumber (bAdicEquation b) k N ↔ RadoNumbers.IsRadoNumber b k N :=
  ⟨isRadoNumber_project_of_general b k N hN,
   isRadoNumber_general_of_project b k N hN⟩

/-! ### §40. UNIVERSAL R_2(b) = b^2 in general framework (b ≥ 2). -/

/--
  **UNIVERSAL R_2(b) = b^2** in general framework for all b ≥ 2.

  Bridges the project's analytic proof `RadoNumbers.R2_b_eq_b_sq_all` to
  the General framework via `isRadoNumber_general_of_project`. Verifies
  threshold conjecture at k = 2 for all b ≥ 2.

  This subsumes `isRadoNumber_bAdicEquation_two_two` (b = 2 case) and
  `isRadoNumber_bAdicEquation_two_three` (b = 3 case) as special cases.
-/
theorem isRadoNumber_bAdicEquation_two_universal (b : ℕ) (hb : 2 ≤ b) :
    IsRadoNumber (bAdicEquation b) 2 (b ^ 2) := by
  apply isRadoNumber_general_of_project b 2 (b ^ 2)
  · have : 1 ≤ b ^ 2 := Nat.one_le_pow 2 b (by omega)
    exact this
  · exact RadoNumbers.R2_b_eq_b_sq_all hb

/-! ### §40.5. **R_3(3) = 27 KERNEL-PURE** via Branch I-V + I-W closure (R238-R245).

  Moved from later in this file (was §55) to provide kernel-pure R_3(3) = 27
  BEFORE the bridge §41 that historically used the axiom-dependent
  `RadoNumbers.thm_k3b3`. This allows §41 to use the kernel-pure version,
  breaking the Bridge.lean → K3B3.lean import cycle for the b = 3 case.

  Combines:
  - `bAdicEquation_3_no_mono_free_at_27` (R245, §86 of BasicResults.lean).
  - Project bridge `hasMonoSolution_bAdicEquation_to_project` (§34 above).
  - `isValidColoring_eq_isKColoring` (§35 above).
  - `RadoNumbers.thm_lower` (kernel-pure).
-/

/-- **R_3(3) ≤ 27 KERNEL-PURE** via vacuous compression at n = 27. -/
theorem thm_k3b3_upper_kernel_pure : RadoNumbers.RadoNumberAtMost 3 3 27 := by
  intro χ hValid
  have hχk : IsKColoring 27 3 χ := (isValidColoring_eq_isKColoring 27 3 χ).mp hValid
  by_contra hNoMonoProj
  have hNoMonoGen : ¬ HasMonoSolution (bAdicEquation 3) 27 χ := fun h =>
    hNoMonoProj (hasMonoSolution_bAdicEquation_to_project 3 27 χ h)
  exact bAdicEquation_3_no_mono_free_at_27 χ (le_refl 27) hχk hNoMonoGen

/-- **R_3(3) = 27 KERNEL-PURE**. Combines kernel-pure lower bound (`thm_lower`)
  with kernel-pure upper bound (`thm_k3b3_upper_kernel_pure`).

  Replaces the old axiom-dependent `RadoNumbers.thm_k3b3` (which used
  `lem_compress3_general`). After R246, downstream consumers point at
  this kernel-pure version.
-/
theorem thm_k3b3_kernel_pure : RadoNumbers.IsRadoNumber 3 3 27 :=
  ⟨RadoNumbers.thm_lower 3 3 (by norm_num) (by norm_num), thm_k3b3_upper_kernel_pure⟩

/-! ### §41. R_3(3) = 27 in general framework (now kernel-pure via §40.5). -/

/--
  **R_3(3) = 27 in general framework**.

  R246: now uses `thm_k3b3_kernel_pure` (kernel-pure) instead of the legacy
  axiom-dependent `RadoNumbers.thm_k3b3`. This eliminates the `lem_compress3_general`
  dependency from this bridge for the b = 3 case.
-/
theorem isRadoNumber_bAdicEquation_three_three :
    IsRadoNumber (bAdicEquation 3) 3 27 :=
  isRadoNumber_general_of_project 3 3 27 (by omega) thm_k3b3_kernel_pure

/--
  **R_3(3) = 27 expressed for `radoEq_3`** (= `bAdicEquation 3`).

  Same content as `isRadoNumber_bAdicEquation_three_three`, just using the
  abbreviation `radoEq_3`. Useful for direct citation in downstream work.
-/
theorem isRadoNumber_radoEq_3_three_27 :
    IsRadoNumber radoEq_3 3 27 :=
  isRadoNumber_bAdicEquation_three_three

/-! ### §42. R_4(3) = 81 in general framework (conditional on G*-tree SAT). -/

/--
  **R_4(3) = 81 in general framework**, bridging the project's
  `thm_k4b3 : IsRadoNumber 3 4 81` (verified modulo the G*-tree atom
  `lem_gstartree`).
-/
theorem isRadoNumber_bAdicEquation_four_three :
    IsRadoNumber (bAdicEquation 3) 4 81 :=
  isRadoNumber_general_of_project 3 4 81 (by omega) RadoNumbers.thm_k4b3

/-! ### §43. Cumulative summary of threshold conjecture verifications. -/

/--
  **Threshold conjecture verified at (b, k) = (3, 1)** (general framework).
  Specialization of `isRadoNumber_bAdicEquation_one` to b = 3, k = 1.
  Note: 1 ≤ 2(3-1) = 4 ✓.
-/
theorem isRadoNumber_bAdicEquation_three_one :
    IsRadoNumber (bAdicEquation 3) 1 3 :=
  isRadoNumber_bAdicEquation_one 3 (by omega)

/-! ### §44. SAT-verified R_k(b) = b^k for the verified set
    (k = 3, 3 ≤ b ≤ 10; k = 4, 3 ≤ b ≤ 5). -/

/--
  **R_k(b) = b^k in general framework, SAT-verified set** (via the
  Distance Pair Lemma).

  Bridges `RadoNumbers.thm_sat` to the general framework. The result is
  conditional on `lem_keypair_sat` (Cat 2 SAT-verified axiom). The
  hypothesis `hbk` encodes EXACTLY the $(b, k)$ pairs SAT-verified in
  Li 2026 Table `table:sat`:
  - $k = 3$, $b \in \{3, 4, 5, 6, 7, 8, 9, 10\}$;
  - $k = 4$, $b \in \{3, 4, 5\}$.
-/
theorem isRadoNumber_bAdicEquation_sat_range
    (b k : ℕ)
    (hbk : (k = 3 ∧ 3 ≤ b ∧ b ≤ 10) ∨ (k = 4 ∧ 3 ≤ b ∧ b ≤ 5)) :
    IsRadoNumber (bAdicEquation b) k (b ^ k) := by
  have hb : 3 ≤ b := by rcases hbk with ⟨_, hb, _⟩ | ⟨_, hb, _⟩ <;> exact hb
  apply isRadoNumber_general_of_project b k (b ^ k)
  · exact Nat.one_le_pow k b (by omega)
  · exact RadoNumbers.thm_sat b k hbk

/--
  **Specialization R_3(4) = 64** in general framework (b = 4, k = 3).
  Verifies threshold conjecture: 3 ≤ 2(4-1) = 6 ✓.
-/
theorem isRadoNumber_bAdicEquation_three_four :
    IsRadoNumber (bAdicEquation 4) 3 64 := by
  have h := isRadoNumber_bAdicEquation_sat_range 4 3 (by omega)
  have h64 : (4 : ℕ) ^ 3 = 64 := by decide
  rw [← h64]
  exact h

/--
  **Specialization R_3(5) = 125** in general framework (b = 5, k = 3).
  Verifies threshold conjecture: 3 ≤ 2(5-1) = 8 ✓.
-/
theorem isRadoNumber_bAdicEquation_three_five :
    IsRadoNumber (bAdicEquation 5) 3 125 := by
  have h := isRadoNumber_bAdicEquation_sat_range 5 3 (by omega)
  have h125 : (5 : ℕ) ^ 3 = 125 := by decide
  rw [← h125]
  exact h

/--
  **Specialization R_4(4) = 256** in general framework (b = 4, k = 4).
  Verifies threshold conjecture: 4 ≤ 2(4-1) = 6 ✓.
-/
theorem isRadoNumber_bAdicEquation_four_four :
    IsRadoNumber (bAdicEquation 4) 4 256 := by
  have h := isRadoNumber_bAdicEquation_sat_range 4 4 (by omega)
  have h256 : (4 : ℕ) ^ 4 = 256 := by decide
  rw [← h256]
  exact h

/-! ### §45. Threshold BREAKDOWN: R_k(b) > b^k for k > 2(b-1). -/

/--
  **Breakdown at (b, k) = (2, 3)**: R_3(2) > 8 (= 2^3) in general framework.

  Bridges project's `thm_r3_2_breakdown : RadoNumberAtLeast 2 3 9` to the
  general framework via `not_isKPartitionRegularAt_of_radoNumberAtLeast`.

  Verifies the BREAKDOWN side of the threshold conjecture at (2, 3) since
  k = 3 > 2(b-1) = 2(2-1) = 2.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_three_at_eight :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 3 8 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 3 9
    RadoNumbers.thm_r3_2_breakdown
  simpa using h

/--
  **Breakdown at (b, k) = (2, 4)**: R_4(2) > 16 (= 2^4) in general framework.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_four_at_sixteen :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 4 16 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 4 17
    RadoNumbers.thm_r4_2_breakdown
  simpa using h

/--
  **Breakdown at (b, k) = (2, 5)**: R_5(2) > 32 (= 2^5) in general framework.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_five_at_thirtytwo :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 5 32 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 5 33
    RadoNumbers.thm_r5_2_breakdown
  simpa using h

/--
  **Breakdown at (b, k) = (2, 6)**: R_6(2) > 64 (= 2^6) in general framework.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_six_at_sixtyfour :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 6 64 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 6 65
    RadoNumbers.thm_r6_2_breakdown
  simpa using h

/--
  **Breakdown at (b, k) = (2, 7)**: R_7(2) > 128 (= 2^7) in general framework.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_seven_at_onetwoeight :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 7 128 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 7 129
    RadoNumbers.thm_r7_2_breakdown
  simpa using h

/--
  **Breakdown at (b, k) = (2, 8)**: R_8(2) > 256 (= 2^8) in general framework.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_eight_at_twofivesix :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 8 256 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 8 257
    RadoNumbers.thm_r8_2_breakdown
  simpa using h

/--
  **Stronger breakdown at (b, k) = (2, 3)**: R_3(2) > 9 (project's
  non-block-and-echo coloring extends the witness to level 9).

  Stronger than the basic 8-level breakdown — establishes R_3(2) ≥ 10.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_two_three_at_nine :
    ¬ IsKPartitionRegularAt (bAdicEquation 2) 3 9 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 2 3 10
    RadoNumbers.thm_r3_2_breakdown_strong
  simpa using h

/--
  **Breakdown at (b, k) = (3, 5)**: R_5(3) > 243 (= 3^5) in general framework.

  Bridges project's `RadoNumbers.thm_r5_243 : RadoNumberAtLeast 3 5 244`
  (depends on `r5_witness_valid_sat`). Verifies threshold conjecture's
  breakdown side at (3, 5) since 5 > 2(3-1) = 4.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_three_five_at_243 :
    ¬ IsKPartitionRegularAt (bAdicEquation 3) 5 243 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 3 5 244
    RadoNumbers.thm_r5_243
  simpa using h

/--
  **Auxiliary lower bound at (b, k) = (3, 5)**: R_5(3) > 296 in general framework.

  Bridges project's `RadoNumbers.thm_r5_296` (depends on `r5_296_sat`).
  This is a lower-bound bridge for the general framework; it does not
  claim the exact value of `R_5(3)`.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_three_five_at_296 :
    ¬ IsKPartitionRegularAt (bAdicEquation 3) 5 296 := by
  have h := not_isKPartitionRegularAt_of_radoNumberAtLeast 3 5 297
    RadoNumbers.thm_r5_296
  simpa using h

/-! ### §47. CONDITIONAL THRESHOLD capstone (kernel-pure modulo hypotheses). -/

/--
  **CONDITIONAL THRESHOLD R_k(b) = b^k for b ≥ 3, k ≥ 2** in general framework.

  Bridges the project's kernel-pure conditional capstone
  `RadoNumbers.thm_threshold_conditional` to the general framework:
  if for every level 2 ≤ j ≤ k the Compression hypothesis and Omitted-Pair
  hypothesis both hold, then `R_k(bAdicEquation b) = b^k`.

  This is the deepest result currently bridged: it isolates the ENTIRE
  remaining content of the threshold conjecture into two per-level
  hypothesis families (CompressionHyp / OmittedPairHyp), with no project
  axioms in the derivation chain.

  Axiom profile: same as project's thm_threshold_conditional, i.e.
  Lean kernel ONLY (propext, Classical.choice, Quot.sound) — fully
  kernel-pure modulo the explicit hypotheses.
-/
theorem isRadoNumber_bAdicEquation_threshold_conditional
    (b : ℕ) (hb : 3 ≤ b) (k : ℕ) (hk : 2 ≤ k)
    (hHyps : ∀ j, 2 ≤ j → j ≤ k →
      RadoNumbers.CompressionHyp b j ∧ RadoNumbers.OmittedPairHyp b j) :
    IsRadoNumber (bAdicEquation b) k (b ^ k) := by
  apply isRadoNumber_general_of_project b k (b ^ k) (Nat.one_le_pow k b (by omega))
  exact RadoNumbers.thm_threshold_conditional b hb k hk hHyps

/-! ### §48. Pillar 3 reduction in general framework. -/

/--
  **R_3(3) ≤ 27 under IsLocalShiftConstant for chi(1) = 0** in general
  framework.

  Bridges project's `RadoNumbers.R_3_3_le_27_under_localShift_constant`
  to general's HasMonoSolution: any 3-coloring chi of [1, 27] with chi(1) = 0
  and constant local shift has a mono solution to bAdicEquation 3.

  This is the central PILLAR 3 reduction step: closing R_3(3) ≤ 27 in
  general framework reduces to showing IsLocalShiftConstant holds for
  every mono-free 3-coloring of [1, 27].

  Axiom profile: same as project's `R_3_3_le_27_under_localShift_constant`
  — FULLY KERNEL-PURE (no project axioms).
-/
theorem hasMonoSolution_bAdicEquation_three_27_under_localShift_constant
    (χ : ℕ → ℕ)
    (hχk : IsKColoring 27 3 χ)
    (hχ1 : χ 1 = 0)
    (hLocalConst : RadoNumbers.IsLocalShiftConstant χ 27) :
    HasMonoSolution (bAdicEquation 3) 27 χ := by
  -- Project version returns ¬ AvoidsMonoSolution = HasMonoSolution.
  have hValid : RadoNumbers.IsValidColoring 27 3 χ :=
    (isValidColoring_eq_isKColoring 27 3 χ).mpr hχk
  have hProjMono : RadoNumbers.HasMonoSolution 3 27 χ := by
    by_contra hNoMono
    -- hNoMono : ¬ HasMonoSolution, i.e., AvoidsMonoSolution.
    exact RadoNumbers.R_3_3_le_27_under_localShift_constant χ hValid hχ1 hLocalConst hNoMono
  exact hasMonoSolution_bAdicEquation_from_project 3 27 χ hProjMono

/-! ### §49. Mono-free structural constraints (general framework). -/

/--
  **Self-loop constraint for bAdicEquation b**: for any mono-free k-coloring χ
  of [1, n] and any m with 3m ≤ n (so the self-loop triple fits), we have
  χ(b·m) ≠ χ((b+1)·m)... no wait. Let me redo.

  For bAdicEquation b coefs (1, b, -b): positive solution requires
  x + b·y = b·z, i.e., x = b·(z-y). Setting y = b·m', z = (b+1)·m':
  x = b·m'. So (b·m', b·m', (b+1)·m') is a solution... wait that's not
  positive unless m' ≥ 1. Setting y = m, z = 2m: x = b·m. Solution
  (b·m, m, 2·m) gives x + b·m = 2b·m ✓. This is a positive solution.

  For mono: χ(b·m) = χ(m) = χ(2m). Avoidance: NOT all three equal.

  Specifically when m, 2m, b·m all ≤ n.
-/
theorem chi_constraint_canonical_triple_of_no_mono
    {b n : ℕ} {χ : ℕ → ℕ}
    (hb : 2 ≤ b)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation b) n χ)
    {m : ℕ} (hm : 0 < m) (hbm : b * m ≤ n) (h2m : 2 * m ≤ n) :
    ¬ (χ (b * m) = χ m ∧ χ m = χ (2 * m)) := by
  intro ⟨h_xy, h_yz⟩
  apply hNoMono
  -- Construct f : ℕ → ℕ with f 0 = b·m, f 1 = m, f 2 = 2m.
  refine ⟨fun i => if i = 0 then b * m else if i = 1 then m else 2 * m, ?_, ?_, ?_⟩
  · intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    interval_cases i <;> simp <;> omega
  · refine ⟨?_, ?_⟩
    · intro i hi
      have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
      rw [hnv] at hi
      interval_cases i <;> simp <;> omega
    · rw [eval_bAdicEquation]
      simp
      ring
  · intro i j hi hj
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi hj
    have hxz : χ (b * m) = χ (2 * m) := h_xy.trans h_yz
    interval_cases i <;> interval_cases j <;> simp
    · exact h_xy
    · exact hxz
    · exact h_xy.symm
    · exact h_yz
    · exact hxz.symm
    · exact h_yz.symm

/-! ### §50. Explicit k=2 corollaries (clean API surface for downstream). -/

/--
  **R_2(4) = 16** in general framework (explicit corollary of universal k=2).
-/
theorem isRadoNumber_bAdicEquation_two_four :
    IsRadoNumber (bAdicEquation 4) 2 16 := by
  have h := isRadoNumber_bAdicEquation_two_universal 4 (by omega)
  have h16 : (4 : ℕ) ^ 2 = 16 := by decide
  rw [← h16]; exact h

/--
  **R_2(5) = 25** in general framework (explicit corollary of universal k=2).
-/
theorem isRadoNumber_bAdicEquation_two_five :
    IsRadoNumber (bAdicEquation 5) 2 25 := by
  have h := isRadoNumber_bAdicEquation_two_universal 5 (by omega)
  have h25 : (5 : ℕ) ^ 2 = 25 := by decide
  rw [← h25]; exact h

/--
  **R_2(10) = 100** in general framework (explicit corollary).
-/
theorem isRadoNumber_bAdicEquation_two_ten :
    IsRadoNumber (bAdicEquation 10) 2 100 := by
  have h := isRadoNumber_bAdicEquation_two_universal 10 (by omega)
  have h100 : (10 : ℕ) ^ 2 = 100 := by decide
  rw [← h100]; exact h

/-! ### §51. Explicit k = 3 corollaries via SAT range (3 ≤ b ≤ 10). -/

/--
  **R_3(6) = 216** in general framework (via SAT-range bridge).
-/
theorem isRadoNumber_bAdicEquation_three_six :
    IsRadoNumber (bAdicEquation 6) 3 216 := by
  have h := isRadoNumber_bAdicEquation_sat_range 6 3 (by omega)
  have h216 : (6 : ℕ) ^ 3 = 216 := by decide
  rw [← h216]; exact h

/--
  **R_3(7) = 343** in general framework (via SAT-range bridge).
-/
theorem isRadoNumber_bAdicEquation_three_seven :
    IsRadoNumber (bAdicEquation 7) 3 343 := by
  have h := isRadoNumber_bAdicEquation_sat_range 7 3 (by omega)
  have h343 : (7 : ℕ) ^ 3 = 343 := by decide
  rw [← h343]; exact h

/--
  **R_3(10) = 1000** in general framework (via SAT-range bridge).
-/
theorem isRadoNumber_bAdicEquation_three_ten :
    IsRadoNumber (bAdicEquation 10) 3 1000 := by
  have h := isRadoNumber_bAdicEquation_sat_range 10 3 (by omega)
  have h1000 : (10 : ℕ) ^ 3 = 1000 := by decide
  rw [← h1000]; exact h

/-! ### §52. Cascade compression equivalence bridged. -/

/--
  **Cascade compression iff upper bound** in general framework: given the
  inductive hypothesis R_{k-1}(b) ≤ b^{k-1} (as `IsKPartitionRegularAt eq
  (k-1) (b^(k-1))`), the CascadeCompressionHyp at level k is equivalent to
  R_k(b) ≤ b^k.

  Bridges project's `cascade_compression_iff_upper_bound` to the general
  framework via `radoNumberAtMost_iff_isKPartitionRegularAt`. This is the
  STRUCTURAL EQUIVALENCE underlying the cascade compression machinery:
  proving the cascade-step compression hypothesis at level k closes the
  upper bound at level k (modulo the inductive hypothesis at level k-1).

  Kernel-pure (same axiom profile as project's
  cascade_compression_iff_upper_bound).
-/
theorem cascadeCompression_iff_isKPartitionRegularAt
    (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hInd : IsKPartitionRegularAt (bAdicEquation b) (k - 1) (b ^ (k - 1))) :
    RadoNumbers.CascadeCompressionHyp b k ↔
    IsKPartitionRegularAt (bAdicEquation b) k (b ^ k) := by
  have hIndProj : RadoNumbers.RadoNumberAtMost b (k - 1) (b ^ (k - 1)) :=
    (radoNumberAtMost_iff_isKPartitionRegularAt b (k - 1) (b ^ (k - 1))).mpr hInd
  constructor
  · intro hHyp
    have h := (RadoNumbers.cascade_compression_iff_upper_bound b k hb hk hIndProj).mp hHyp
    exact (radoNumberAtMost_iff_isKPartitionRegularAt b k (b ^ k)).mp h
  · intro hUpper
    have hProj : RadoNumbers.RadoNumberAtMost b k (b ^ k) :=
      (radoNumberAtMost_iff_isKPartitionRegularAt b k (b ^ k)).mpr hUpper
    exact (RadoNumbers.cascade_compression_iff_upper_bound b k hb hk hIndProj).mpr hProj

/-! ### §53. Per-level Compression / Omitted-Pair hypotheses (k = 2 closed). -/

/--
  **CompressionHyp b 2 holds unconditionally for b ≥ 3** (kernel-pure).

  Direct bridge from project's `RadoNumbers.compression_hyp_k2`. For any
  b ≥ 3, the Compression Hypothesis at level k = 2 is closed analytically
  by the project — no SAT axioms needed.

  Significance: closes the base case of the cascade ladder. Combined with
  `isRadoNumber_bAdicEquation_threshold_conditional` at k = 2, gives an
  alternative kernel-pure path to R_2(b) = b^2 (besides the direct
  R2_b_eq_b_sq_all bridge).
-/
theorem compressionHyp_unconditional_k2 (b : ℕ) (hb : 3 ≤ b) :
    RadoNumbers.CompressionHyp b 2 :=
  RadoNumbers.compression_hyp_k2 b hb

/--
  **OmittedPairHyp b 2 holds unconditionally for b ≥ 3** (kernel-pure).

  Direct bridge from project's `RadoNumbers.omitted_pair_hyp_k2`. Closure
  at k = 2 via the Distance Pair Lemma analytic argument.
-/
theorem omittedPairHyp_unconditional_k2 (b : ℕ) (hb : 3 ≤ b) :
    RadoNumbers.OmittedPairHyp b 2 :=
  RadoNumbers.omitted_pair_hyp_k2 b hb

/--
  **Combined hypothesis closure at k = 2** for use in
  `isRadoNumber_bAdicEquation_threshold_conditional`.

  Wraps `compressionHyp_unconditional_k2` and `omittedPairHyp_unconditional_k2`
  into the single hypothesis form `CompressionHyp b 2 ∧ OmittedPairHyp b 2`
  needed by the conditional capstone.
-/
theorem compressionAndOmittedPair_k2 (b : ℕ) (hb : 3 ≤ b) :
    RadoNumbers.CompressionHyp b 2 ∧ RadoNumbers.OmittedPairHyp b 2 :=
  ⟨compressionHyp_unconditional_k2 b hb, omittedPairHyp_unconditional_k2 b hb⟩

/--
  **R_2(b) = b^2 for b ≥ 3 via CASCADE ROUTE** (end-to-end demonstration).

  Closes R_2(b) = b^2 for b ≥ 3 using ONLY the General/ framework's
  cascade machinery:
  1. `compressionAndOmittedPair_k2` discharges the (j = 2) hypothesis.
  2. `isRadoNumber_bAdicEquation_threshold_conditional` applies the cascade
     capstone.

  This is a structural alternative to `isRadoNumber_bAdicEquation_two_universal`
  (which bridges from the project's analytic R2_b_eq_b_sq_all proof).
  Same result, different derivation — demonstrates that the cascade
  architecture in General/ is sound and self-contained for the k = 2
  case.

  FULLY KERNEL-PURE.
-/
theorem isRadoNumber_bAdicEquation_two_via_cascade (b : ℕ) (hb : 3 ≤ b) :
    IsRadoNumber (bAdicEquation b) 2 (b ^ 2) := by
  apply isRadoNumber_bAdicEquation_threshold_conditional b hb 2 (le_refl 2)
  intro j hj2 hjk
  have hj_eq : j = 2 := by omega
  subst hj_eq
  exact compressionAndOmittedPair_k2 b hb

/-! ### §54. R_3(3) = 27 KERNEL-PURE conditional on two open hypotheses. -/

/--
  **R_3(3) = 27 from CompressionHyp 3 3 + OmittedPairHyp 3 3** (kernel-pure
  conditional closure of the central case).

  Given both per-level k=3 hypotheses as inputs (currently open: project's
  `lem_compress3_general` SAT-verified the compression hypothesis; the
  omitted pair hypothesis at k=3 is similarly only verified by SAT), the
  cascade capstone closes R_3(3) = 27 kernel-pure.

  Significance: ISOLATES the entire remaining content of "R_3(3) = 27
  kernel-pure" into the two open per-level hypotheses
    CompressionHyp 3 3 and OmittedPairHyp 3 3.
  This is the deepest conditional reduction. Any future kernel-pure proof
  of these two hypotheses immediately gives kernel-pure R_3(3) = 27 via
  this theorem.

  Compare with isRadoNumber_radoEq_3_three_27 (depends on lem_compress3_general
  which is SAT-verified Cat 2 axiom). This theorem REPLACES the SAT
  dependency with two CLEAN hypothesis assumptions, sharpening the open
  problem statement.

  FULLY KERNEL-PURE (modulo the explicit hypotheses).
-/
theorem isRadoNumber_radoEq_3_three_27_from_hypotheses
    (hComp : RadoNumbers.CompressionHyp 3 3)
    (hOmit : RadoNumbers.OmittedPairHyp 3 3) :
    IsRadoNumber (bAdicEquation 3) 3 27 := by
  have h := isRadoNumber_bAdicEquation_threshold_conditional 3 (by omega) 3 (by omega)
    (fun j hj2 hj3 => by
      -- j ∈ [2, 3]. Two cases.
      interval_cases j
      · exact compressionAndOmittedPair_k2 3 (by omega)
      · exact ⟨hComp, hOmit⟩)
  have h27 : (3 : ℕ) ^ 3 = 27 := by decide
  rw [← h27]
  exact h

/-! ### §55. (R_3(3) = 27 kernel-pure was moved to §40.5 to break the
  Bridge.lean → K3B3.lean import cycle. See §40.5 for the kernel-pure
  derivation and §41 for its use in the project-to-general bridge.)
-/

/-! ### §56. **PARAMETERIZED UPPER-BOUND SCHEMA** (R247).

  Extracts the reusable abstraction from the R238-R246 architecture:
  given a kernel-pure proof that no mono-free k-coloring exists at n = b^k,
  the schema produces the kernel-pure `IsRadoNumber b k (b^k)` result.

  This generalizes the (3, 3, 27) closure to ANY (b, k) for which the
  "no mono-free at b^k" obligation can be discharged.

  **Strategic role**: extracts the reusable upper-bound interface for the
  ThresholdConjecture(b, k) schema. The lower-bound side
  (`not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one`) is already
  general. Combined with this schema, ANY future kernel-pure no-mono-free
  derivation at n = b^k immediately yields kernel-pure R_k(b) = b^k.
-/

/-- **General no-mono-free upper bound (schema A)**: if no mono-free
  k-coloring of [1, b^k] exists for `bAdicEquation b`, then the equation
  is k-partition regular at b^k. Kernel-pure parameterized schema.
-/
theorem isKPartitionRegularAt_bpow_of_no_mono_free
    {b k : ℕ} (_hb : 2 ≤ b) (_hk : 1 ≤ k)
    (hNoFree : ∀ χ : ℕ → ℕ,
        IsKColoring (b^k) k χ →
        ¬ HasMonoSolution (bAdicEquation b) (b^k) χ → False) :
    IsKPartitionRegularAt (bAdicEquation b) k (b^k) := by
  intro χ hχk
  by_contra hNoMono
  exact hNoFree χ hχk hNoMono

/-- **General Rado-number exactness (schema B)**: combining the kernel-pure
  valuation lower bound (R_k(b) ≥ b^k for any b ≥ 2, k ≥ 1) with the
  no-mono-free upper bound, derives the exact `IsRadoNumber b k (b^k)`.

  This is the **reusable upper-bound schema** for ThresholdConjecture(b, k).
  Instantiating it at any (b, k) reduces the kernel-pure threshold result
  to a SINGLE obligation: derive `no_mono_free_at_bpow` for that (b, k).
-/
theorem isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow
    {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hNoFree : ∀ χ : ℕ → ℕ,
        IsKColoring (b^k) k χ →
        ¬ HasMonoSolution (bAdicEquation b) (b^k) χ → False) :
    IsRadoNumber (bAdicEquation b) k (b^k) := by
  have hUpper := isKPartitionRegularAt_bpow_of_no_mono_free hb hk hNoFree
  have hLower := not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one b k hb hk
  -- IsRadoNumber needs N = b^k ≥ 1.
  have hbk_pos : 1 ≤ b^k := Nat.one_le_pow k b (by omega)
  exact isRadoNumber_of_bounds (bAdicEquation b) k (b^k) hbk_pos hUpper hLower

/-! ### §57. **Regression check**: recover R_3(3) = 27 from the schema.

  Confirms that the new parameterized schema correctly produces the
  R_3(3) = 27 result when instantiated at (b, k) = (3, 3) with the
  kernel-pure `bAdicEquation_3_no_mono_free_at_27` obligation.

  This is the regression check: kernel-pure derivation of R_3(3) = 27
  via the SCHEMA (not via the R246 direct bridge).
-/

/-- **R_3(3) = 27 KERNEL-PURE via the general schema** (regression check). -/
theorem thm_k3b3_via_general_no_mono_free_schema :
    IsRadoNumber (bAdicEquation 3) 3 (3^3) :=
  isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow (b := 3) (k := 3)
    (by omega) (by omega)
    (fun χ hχk hNoMono => by
      have h27 : (3:ℕ)^3 = 27 := by decide
      rw [h27] at hχk hNoMono
      exact bAdicEquation_3_no_mono_free_at_27 χ (le_refl 27) hχk hNoMono)

/-- **R_3(3) = 27 in project namespace via the schema** (regression check). -/
theorem thm_k3b3_project_via_general_no_mono_free_schema :
    RadoNumbers.IsRadoNumber 3 3 27 := by
  have h := thm_k3b3_via_general_no_mono_free_schema
  have h27 : (3:ℕ)^3 = 27 := by decide
  rw [h27] at h
  exact (isRadoNumber_bAdicEquation_iff_project 3 3 27 (by omega)).mp h

/-! ### §58. Roadmap for next instance: b = 4, k = 3.

  **Strategic target**: extend the schema to (b, k) = (4, 3) to test
  generalization beyond b = 3.

  **Threshold point**: b^k = 4^3 = 64. Multiples-of-4 layer: {4·d | 1 ≤ d ≤ 16}.

  **Required theorem**: `bAdicEquation_4_no_mono_free_at_64`
  (the (4, 3) analogue of `bAdicEquation_3_no_mono_free_at_27`).

  Statement target:
  ```
  ∀ χ : ℕ → ℕ, IsKColoring 64 3 χ →
    ¬ HasMonoSolution (bAdicEquation 4) 64 χ → False
  ```

  Once proven kernel-pure:
  ```
  theorem thm_k3b4_kernel_pure : IsRadoNumber (bAdicEquation 4) 3 (4^3) :=
    isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow (b := 4) (k := 3)
      (by omega) (by omega) bAdicEquation_4_no_mono_free_at_64
  ```

  **Reusable infrastructure from (3, 3)**:
  - Valuation lower bound: `not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one`
    works for any (b, k). [Type C]
  - Schema theorems §56 (this round). [Type C]
  - Color trichotomy / third_color_eq machinery: reusable because k = 3. [Type B]
  - Cascade-to-mono template: reusable conceptually. [Type B]
  - `bAdicEquation_general_rado_constraint` (general Rado triple): works for any b. [Type C]
  - `bAdicEquation_self_loop_chi_diff` (self-loops): works for any b. [Type C]
  - `multiples_subcoloring_mono_free`: works for any b. [Type C]

  **NOT directly reusable** (b = 3-specific):
  - Branch I-V / I-W case-split structure: depends on b = 3 specific
    chi(6), chi(9), chi(12) etc. roles.
  - The specific Rado triples used in cascades — different for b = 4
    (e.g., (4, y, y+1) instead of (3, y, y+1)).
  - The §73-§75 propagation lemmas: specific to b = 3 positions and triples.
  - `bAdicEquation_3_chi_*` named lemmas: all (b = 3)-specific.

  **First attack obstruction for b = 4, k = 3**:
  Identify the analogue of "Branch I structure" — the forced equalities
  at multiples of 4. For b = 4:
  - Self-loops: χ((b-1)·m) ≠ χ(b·m), i.e., χ(3m) ≠ χ(4m).
  - For m = 4: χ(12) ≠ χ(16). For m = 8: χ(24) ≠ χ(32). Etc.
  - Multiples of 4 in [1, 64]: {4, 8, 12, ..., 64}, 16 positions.
  - 3-coloring with these constraints — first goal: force some structural
    equalities among multiples (analogous to χ(6) = χ(12) for b=3).

  **Estimated first concrete sub-theorem**:
  ```
  theorem bAdicEquation_4_chi_8_eq_chi_16_in_monoFree :
      ∀ χ : ℕ → ℕ, IsKColoring 64 3 χ →
      ¬ HasMonoSolution (bAdicEquation 4) 64 χ → χ 8 = χ 16
  ```
  (Or whatever specific equality is the first forced by the b=4 self-loops
  and pigeonhole on a small initial segment.)

  This roadmap is documentation only — not an axiom, not a placeholder.
  Concrete (4, 3) work begins in a future round.
-/

/-! ### §95. R254 — SCALE-BY-4 BRIDGE for residual cells.

  **Strategic context (R254)**: of the 9 trichotomy cells of
  `bAdicEquation_4_no_chi_9_12_16_all_distinct`, R249-R253 closed 6 cells
  at n ≥ 20. The 3 surviving cells (§93 + §94) are:
    (1) χ(8) = χ(12), χ(4) = χ(12)   [admits n=20 witness]
    (2) χ(8) = χ(12), χ(4) = χ(16)   [admits n=20 witness]
    (3) χ(8) = χ(16), χ(4) = χ(12)   [admits n=20 witness]

  All three surviving cells share the feature χ(4), χ(8) ∈ {χ(12), χ(16)}.
  At n = 64, IF additionally all multiples-of-4 are constrained into
  {χ(12), χ(16)} (the "layer compression" property), then thm_k2 (R(4,2)=16)
  applied to the scale-by-4 sub-coloring forces a mono.

  **This section builds the Type B BRIDGE** that takes layer compression as
  a HYPOTHESIS and derives False. The layer compression itself (for residual
  cells without the hypothesis) requires further cascade work and is left for
  R255+. See §95 obstruction analysis below.

  **Bridge structure**:
  - Input: hLayer : ∀ d ∈ [1, 16], χ(4d) ∈ {χ(12), χ(16)}. + h12_ne_16 + h64 + hNoMono.
  - Re-map: ψ(d) := if χ(4d) = χ(12) then 0 else 1. Yields 2-coloring of [1, 16].
  - Apply thm_k2 b=4: every 2-coloring of [1, 16] for bAdicEquation 4 has a mono.
  - Lift via scale-by-4: ψ-mono (x, y, z) → χ-mono (4x, 4y, 4z) at level 4·16 = 64.
  - Contradicts hNoMono.

  **§95 layer-compression OBSTRUCTION analysis** (Deliverable C documentation):

  For cell (1) [χ(8)=B, χ(4)=B] with the additional assumption χ(20) = A:
    - The cascade forces χ(14)=C, χ(10)=A, χ(15)=C, χ(11)=A, χ(6)=C, χ(2)≠C,
      χ(3)=A (in some sub-case), χ(7)=A, χ(13)=A or C, χ(17)=A, χ(18)=B,
      χ(19)=A. At n=20, this admits a witness.
    - Extending to n ≥ 28: χ(24)=C (from self-loop m=6 + (20,19,24)), χ(28)=B
      (from self-loop m=7 + (16,24,28)), χ(32)=B (from (20,27,32) + self-loop m=8),
      χ(36)=C (from (32,28,36) + self-loop m=9).
    - At n=40: chi(40) excluded from A (self-loop m=10, chi(30)=A), from B
      (anchor self-rado m=8, chi(32)=B), AND from C (16,36,40 with chi(36)=C).
      CONTRADICTION — χ(40) has no valid color. Hence cell (1) with χ(20) = A
      yields False at n ≥ 40 via a kernel-pure cascade.
    - Conclusion for cell (1): the surviving witness at n=20 does NOT extend
      to n ≥ 40. Cell (1) closes via the χ(20) ∈ {B, C} → layer-compression
      route AT n ≥ 40 + additional cascading. R255 should formalize.

  For cell (2) [χ(8)=B, χ(4)=C] with χ(20)=A: cascade forces χ(5)=A,
    χ(10)=C, χ(14)=A, then (20,9,14) mono A=A=A. CLOSES at n ≥ 20.

  For cell (3) [χ(8)=C, χ(4)=B] with χ(20)=A: case split on (χ(11), χ(13)).
    Sub-case (χ(11), χ(13)) = (A, A): admits witness up to n=20 (and beyond);
    further forced χ(22) ≠ A from (20, 17, 22), and cascade continues —
    OBSTRUCTION not closed in this round.
    Other sub-cases close at n ≥ 20 via various mono triples.

  **R254 DELIVERABLE B**: the bridge theorem below assumes hLayer. Future
  rounds (R255+) should prove hLayer for each residual cell separately,
  completing the schema migration.
-/

/-- **R254 SCALE-BY-4 BRIDGE** (Type B reusable infrastructure).
  Given a 3-coloring χ of [1, n] (n ≥ 64) that is mono-free for `bAdicEquation 4`,
  and the LAYER COMPRESSION hypothesis that all multiples-of-4 in [4, 64] use
  only the two colors {χ(12), χ(16)}, derive False via `RadoNumbers.thm_k2`
  (R(4, 2) = 16) lifted by scale-by-4.

  Proof: define ψ(d) := if χ(4d) = χ(12) then 0 else 1. ψ is a 2-coloring of
  [1, 16] for bAdicEquation 4 (uses hLayer + h12_ne_16). By thm_k2, ψ has a
  mono solution (x, y, z). Lift to (4x, 4y, 4z) which is a valid Rado triple
  for bAdicEquation 4 at level 64 ≤ n; lifted positions are mono-colored by
  χ (via hLayer); contradicts hNoMono.

  **Kernel-pure**: only Lean kernel axioms (propext, Classical.choice, Quot.sound).
  Reusable for future b=4 work and (with parameterization) for general b. -/
theorem scale4_two_color_subcoloring_lifts_mono_solution
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (hLayer : ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16) :
    False := by
  -- Define ψ via re-mapping χ(4d) into {0, 1}.
  let ψ : ℕ → ℕ := fun d => if χ (4 * d) = χ 12 then 0 else 1
  -- ψ is a 2-coloring of [1, 16].
  have hψk : IsKColoring 16 2 ψ := by
    intro d _ _
    show (if χ (4 * d) = χ 12 then 0 else 1) < 2
    split <;> norm_num
  -- thm_k2 at b=4 yields IsKPartitionRegularAt (bAdicEquation 4) 2 16.
  have hThmK2_proj : RadoNumbers.RadoNumberAtMost 4 2 (4 ^ 2) :=
    (RadoNumbers.thm_k2 4 (by norm_num)).2
  have hThmK2 : RadoNumbers.RadoNumberAtMost 4 2 16 := by
    have h16 : (4 : ℕ) ^ 2 = 16 := by decide
    rw [h16] at hThmK2_proj
    exact hThmK2_proj
  have hPR : IsKPartitionRegularAt (bAdicEquation 4) 2 16 :=
    (radoNumberAtMost_iff_isKPartitionRegularAt 4 2 16).mp hThmK2
  -- ψ has a mono solution at level 16.
  obtain ⟨f, hbound, hpos, hcolor⟩ := hPR ψ hψk
  -- Lift to χ at scale 4: positions (4·f 0, 4·f 1, 4·f 2) at level 64 ≤ n.
  apply hNoMono
  refine ⟨fun i => 4 * f i, ?_, ?_, ?_⟩
  · -- All positions ≤ n.
    intro i hi
    have hfi : f i ≤ 16 := hbound i hi
    calc 4 * f i ≤ 4 * 16 := Nat.mul_le_mul_left 4 hfi
      _ = 64 := by decide
      _ ≤ n := h64
  · -- Positive solution of bAdicEquation 4.
    exact LinearEquation.isPositiveSolution_const_mul (bAdicEquation 4) (by omega) f hpos
  · -- Mono color: χ(4·f i) = χ(4·f j) via hLayer + ψ-mono.
    intro i j hi hj
    show χ (4 * f i) = χ (4 * f j)
    have hψij : ψ (f i) = ψ (f j) := hcolor i j hi hj
    -- f i, f j ∈ [1, 16].
    have hfi_pos : 1 ≤ f i := hpos.1 i hi
    have hfj_pos : 1 ≤ f j := hpos.1 j hj
    have hfi : f i ≤ 16 := hbound i hi
    have hfj : f j ≤ 16 := hbound j hj
    have hL_i := hLayer (f i) hfi_pos hfi
    have hL_j := hLayer (f j) hfj_pos hfj
    rcases hL_i with hi12 | hi16
    · rcases hL_j with hj12 | hj16
      · -- Both = χ 12.
        rw [hi12, hj12]
      · -- ψ(f i) = 0, ψ(f j) = 1 — contradicts hψij.
        exfalso
        have hψi : ψ (f i) = 0 := by
          show (if χ (4 * f i) = χ 12 then 0 else 1) = 0
          exact if_pos hi12
        have hj_ne_12 : χ (4 * f j) ≠ χ 12 := by rw [hj16]; exact h12_ne_16.symm
        have hψj : ψ (f j) = 1 := by
          show (if χ (4 * f j) = χ 12 then 0 else 1) = 1
          exact if_neg hj_ne_12
        rw [hψi, hψj] at hψij
        exact absurd hψij (by norm_num)
    · rcases hL_j with hj12 | hj16
      · -- ψ(f i) = 1, ψ(f j) = 0 — contradicts hψij.
        exfalso
        have hi_ne_12 : χ (4 * f i) ≠ χ 12 := by rw [hi16]; exact h12_ne_16.symm
        have hψi : ψ (f i) = 1 := by
          show (if χ (4 * f i) = χ 12 then 0 else 1) = 1
          exact if_neg hi_ne_12
        have hψj : ψ (f j) = 0 := by
          show (if χ (4 * f j) = χ 12 then 0 else 1) = 0
          exact if_pos hj12
        rw [hψi, hψj] at hψij
        exact absurd hψij (by norm_num)
      · -- Both = χ 16.
        rw [hi16, hj16]

/-- **R254 RESIDUAL-CELL REDUCTION** at the n=64 threshold, conditional on
  the layer-compression hypothesis. This is the user-requested theorem;
  it depends on `scale4_two_color_subcoloring_lifts_mono_solution` plus
  hLayer as an explicit hypothesis.

  For the unconditional form (layer compression PROVED for each residual
  cell), future rounds R255+ must establish hLayer from the residual
  branch hypotheses (e.g., χ(4)=χ(12), χ(8)∈{χ(12),χ(16)} + the all-distinct
  + mono-free constraints). The §95 docstring documents the cascade structure
  required for this proof, which appears to take ~50-100 forced positions
  to push the layer compression from d ≤ 4 (given) to d ≤ 16. -/
theorem bAdicEquation_4_multiples_of_4_two_color_reduction_in_residual_cells
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (hLayer : ∀ d, 1 ≤ d → d ≤ 16 → χ (4 * d) = χ 12 ∨ χ (4 * d) = χ 16) :
    False :=
  scale4_two_color_subcoloring_lifts_mono_solution χ h64 hNoMono h12_ne_16 hLayer

/-- **R272 cell (1) closed by R254 bridge**: under residual cell (1)
  hypotheses + mono-free `bAdicEquation 4` at n ≥ 64, derive False directly
  by applying `scale4_two_color_subcoloring_lifts_mono_solution` (R254
  bridge) to the assembled full hLayer compression from R272. **Completes
  residual cell (1) closure** — the entire b=4, k=3 path through cell (1)
  is sealed. -/
theorem residual_cell_1_closed_by_scale4_bridge
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    False :=
  scale4_two_color_subcoloring_lifts_mono_solution χ h64 hNoMono h12_ne_16
    (residual_cell_1_full_layer_compression χ h64 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12)

/-- **R285 cell (2) closed by R254 bridge**: under residual cell (2)
  hypotheses + mono-free `bAdicEquation 4` at n ≥ 64, derive False directly
  by applying `scale4_two_color_subcoloring_lifts_mono_solution` (R254
  bridge) to the assembled full hLayer compression from R285. **Completes
  residual cell (2) closure** — the entire b=4, k=3 path through cell (2)
  is sealed.

  Cell (2) hypotheses: χ(4) = χ(16) (C anchor) and χ(8) = χ(12) (B anchor). -/
theorem residual_cell_2_closed_by_scale4_bridge
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_16 : χ 4 = χ 16)
    (h8_eq_12 : χ 8 = χ 12) :
    False :=
  scale4_two_color_subcoloring_lifts_mono_solution χ h64 hNoMono h12_ne_16
    (residual_cell_2_full_layer_compression χ h64 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12)

/-- **R298 cell (3) closed by R254 bridge**: under residual cell (3)
  hypotheses + mono-free `bAdicEquation 4` at n ≥ 64, derive False by
  applying `scale4_two_color_subcoloring_lifts_mono_solution` (R254 bridge)
  to the assembled full hLayer compression from R298. **Completes residual
  cell (3) closure via the bridge interface**, uniformly with cell (1)/(2).

  Cell (3) hypotheses: χ(4) = χ(12) (B anchor) and χ(8) = χ(16) (C anchor).

  Note: An alternative shorter proof exists via `residual_cell_3_closed_directly_at_32`
  (R297 SHORTCUT), which already gives False at n ≥ 32. We retain this bridge form
  for architectural symmetry with cell (1)/(2). -/
theorem residual_cell_3_closed_by_scale4_bridge
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_16 : χ 8 = χ 16) :
    False :=
  scale4_two_color_subcoloring_lifts_mono_solution χ h64 hNoMono h12_ne_16
    (residual_cell_3_full_layer_compression χ h64 hχk hNoMono
      h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16)

/-! ### §140. R299 — all-distinct 9-cell integration.

  **Target.** Under `χ(9), χ(12), χ(16)` all distinct + `hNoMono` + `n ≥ 64`,
  derive False. This integrates the 9 (χ4, χ8) cases via trichotomy:
  - 6 direct cells: closed by individual subcase theorems (R249/R250-R251/
    R252-at-64/R253-at-64/§§subcase_8_eq_*_4_eq_*).
  - 3 residual cells: closed by `residual_cell_{1,2,3}_closed_by_scale4_bridge`.

  | (χ8, χ4) | Cell type | Closure theorem |
  |----------|-----------|-----------------|
  | (A, A) | direct | subcase_8_eq_9_4_eq_9 |
  | (A, B) | direct | subcase_8_eq_9_4_eq_12 |
  | (A, C) | direct | R250_witness_branch_no_extend_to_64 |
  | (B, A) | direct | subcase_8_eq_12_4_eq_9_at_64 |
  | (B, B) | **cell (1)** | residual_cell_1_closed_by_scale4_bridge |
  | (B, C) | **cell (2)** | residual_cell_2_closed_by_scale4_bridge |
  | (C, A) | direct | subcase_8_eq_16_4_eq_9_at_64 |
  | (C, B) | **cell (3)** | residual_cell_3_closed_by_scale4_bridge |
  | (C, C) | direct | subcase_8_eq_16_4_eq_16 |

  Mirrors `bAdicEquation_3_no_chi_6_9_12_all_distinct` (b=3 dispatcher
  with 4 cases). Threshold n ≥ 64 forced by bridge closures.
-/

/-- **R299 b=4 all-distinct branch closed**: under χ(9), χ(12), χ(16) all
  distinct, mono-free, k-coloring, and `n ≥ 64`, derive False by trichotomy
  on `(χ8, χ4)` and dispatch to 6 direct subcases + 3 residual bridges. -/
theorem bAdicEquation_4_no_chi_9_12_16_all_distinct
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_12 : χ 9 ≠ χ 12)
    (h9_ne_16 : χ 9 ≠ χ 16)
    (h12_ne_16 : χ 12 ≠ χ 16) :
    False := by
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  -- χ4 ∈ {A=χ9, B=χ12, C=χ16}: only 3 values < 3, and {χ9, χ12, χ16} distinct.
  have h4_disj : χ 4 = χ 9 ∨ χ 4 = χ 12 ∨ χ 4 = χ 16 := by omega
  -- χ8 ∈ {A, B, C} by the same argument.
  have h8_disj : χ 8 = χ 9 ∨ χ 8 = χ 12 ∨ χ 8 = χ 16 := by omega
  rcases h8_disj with h8_eq_9 | h8_eq_12 | h8_eq_16
  · -- χ8 = A (= χ9).
    rcases h4_disj with h4_eq_9 | h4_eq_12 | h4_eq_16
    · -- (A, A) direct.
      exact bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_9
        χ (by omega) hNoMono h8_eq_9 h4_eq_9
    · -- (A, B) direct.
      exact bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_12
        χ (by omega) hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_9 h4_eq_12
    · -- (A, C) direct (R250/R251 witness branch).
      exact bAdicEquation_4_R250_witness_branch_no_extend_to_64
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_9 h4_eq_16
  · -- χ8 = B (= χ12).
    rcases h4_disj with h4_eq_9 | h4_eq_12 | h4_eq_16
    · -- (B, A) direct (R252 at n≥64).
      exact bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9_at_64
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_12 h4_eq_9
    · -- (B, B) = cell (1): χ(4) = χ(12), χ(8) = χ(12).
      exact residual_cell_1_closed_by_scale4_bridge
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_12
    · -- (B, C) = cell (2): χ(4) = χ(16), χ(8) = χ(12).
      exact residual_cell_2_closed_by_scale4_bridge
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_16 h8_eq_12
  · -- χ8 = C (= χ16).
    rcases h4_disj with h4_eq_9 | h4_eq_12 | h4_eq_16
    · -- (C, A) direct (R253 at n≥64).
      exact bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9_at_64
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_16 h4_eq_9
    · -- (C, B) = cell (3): χ(4) = χ(12), χ(8) = χ(16).
      exact residual_cell_3_closed_by_scale4_bridge
        χ h64 hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h4_eq_12 h8_eq_16
    · -- (C, C) direct.
      exact bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_16
        χ (by omega) hχk hNoMono h9_ne_12 h9_ne_16 h12_ne_16 h8_eq_16 h4_eq_16

/-! ### §141. R300 — not-all-distinct branch — Case A and Case C closures + auto-distinctness.

  Under `hNoMono + n ≥ 16`, two of three distinctness conditions among
  {χ(9), χ(12), χ(16)} are AUTOMATIC via self-loop Rado triples:
  - **Case A (χ(9) = χ(12)) → False** via self-loop (12, 9, 12).
  - **Case C (χ(12) = χ(16)) → False** via self-loop (16, 12, 16).

  Therefore `χ(9) ≠ χ(12)` and `χ(12) ≠ χ(16)` are automatic facts in
  mono-free b=4 colorings (at n ≥ 16). Only `χ(9) ≠ χ(16)` requires
  a separate hypothesis or independent proof.

  **Case B (χ(9) = χ(16)) remains OPEN.** It cannot be closed via single
  self-loop, because no `bAdicEquation 4` self-loop involves both
  positions 9 and 16 simultaneously. Closure requires multi-step
  cascade — see audit details in final report. The partial final theorem
  `bAdicEquation_4_no_mono_free_at_64_when_chi9_ne_chi16` covers the
  all-distinct branch by routing through R299.

  Self-loop triples used:
  - (12, 9, 12):  12 + 36 = 48 = 4·12 ✓ (x = z = 12, y = 9, d = 3)
  - (16, 12, 16): 16 + 48 = 64 = 4·16 ✓ (x = z = 16, y = 12, d = 4)
-/

/-- **R300 Case A closure**: `χ(9) = χ(12) → False` under `hNoMono` at n ≥ 12.
  Self-loop (12, 9, 12) forces χ(12) = χ(9) violation. -/
theorem bAdicEquation_4_chi_9_eq_chi_12_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h12 : 12 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_12 : χ 9 = χ 12) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 3) = χ 9
    rw [show (4 * 3 : ℕ) = 12 by decide]; exact h9_eq_12.symm
  · show χ 9 = χ (9 + 3)
    rw [show (9 + 3 : ℕ) = 12 by decide]; exact h9_eq_12

/-- **R300 Case C closure**: `χ(12) = χ(16) → False` under `hNoMono` at n ≥ 16.
  Self-loop (16, 12, 16) forces χ(16) = χ(12) violation. -/
theorem bAdicEquation_4_chi_12_eq_chi_16_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h16 : 16 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h12_eq_16 : χ 12 = χ 16) :
    False := by
  have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 4) (y := 12) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (4 * 4) = χ 12
    rw [show (4 * 4 : ℕ) = 16 by decide]; exact h12_eq_16.symm
  · show χ 12 = χ (12 + 4)
    rw [show (12 + 4 : ℕ) = 16 by decide]; exact h12_eq_16

/-- **R300 partial final theorem (all-distinct branch closure)**: at n ≥ 64 with
  mono-free 3-coloring, if additionally `χ(9) ≠ χ(16)`, then False.

  Routes through R299 (`bAdicEquation_4_no_chi_9_12_16_all_distinct`).
  The `χ(9) ≠ χ(12)` and `χ(12) ≠ χ(16)` distinctness are derived automatically.

  **Unconditional `bAdicEquation_4_no_mono_free_at_64` requires closing the
  remaining `χ(9) = χ(16)` obstruction (Case B).** -/
theorem bAdicEquation_4_no_mono_free_at_64_when_chi9_ne_chi16
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_ne_16 : χ 9 ≠ χ 16) :
    False := by
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  have h12_ne_16 : χ 12 ≠ χ 16 :=
    bAdicEquation_4_chi_12_ne_chi_16_in_monoFree χ (by omega) hNoMono
  exact bAdicEquation_4_no_chi_9_12_16_all_distinct χ h64 hχk hNoMono
    h9_ne_12 h9_ne_16 h12_ne_16

/-! ### §142. R301 — Case B (h9_eq_16) sub-case (χ4=A, χ8=B) closure.

  **Setup.** Under residual `h9_eq_16 : χ(9) = χ(16)` together with `h4_eq_9`
  and `h8_eq_12`, derive False at n ≥ 64. This is one of 8 sub-cases of
  Case B (h9_eq_16); the (A, A) sub-case is auto-impossible via (16, 4, 8).

  **Repaired cascade (avoids χ13 / χ32)**:
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | S1 | χ(5) = C   | (16, 5, 9) [≠A; h9_eq_16] + (12, 5, 8) [≠B; h8_eq_12] |
  | S2 | χ(10) = C  | (4, 9, 10) [≠A; h4_eq_9] + (8, 8, 10) [self-loop x=y; ≠B] |
  | S3 | χ(5) = χ(10) (third color) | third_color_eq |
  | S4 | χ(20) = B  | (16, 16, 20) [self-loop; ≠A] + (20, 5, 10) [≠C; uses χ5=χ10] |
  | S5 | χ(17) = χ(5) (= C) | (4, 16, 17) [≠A; h4_eq_16] + (12, 17, 20) [≠B; uses χ20=χ12] + third_color_eq |
  | S6 | χ(48) = χ(5) (= C) | (48, 4, 16) [≠A; h4_eq_16] + (48, 8, 20) [≠B; uses χ20=χ12, h8_eq_12] + third_color_eq |
  | T  | (48, 5, 17) MONO C | χ(48) = χ(5) = χ(17) all same value |

  No χ(13) or χ(32) needed — terminal (48, 5, 17) closes directly.

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 5, 9):   16 + 20 = 36 = 4·9 ✓
  - (12, 5, 8):   12 + 20 = 32 = 4·8 ✓
  - (4, 9, 10):   4 + 36 = 40 = 4·10 ✓
  - (8, 8, 10):   8 + 32 = 40 = 4·10 ✓ (self-loop x=y)
  - (16, 16, 20): 16 + 64 = 80 = 4·20 ✓ (self-loop x=y)
  - (20, 5, 10):  20 + 20 = 40 = 4·10 ✓
  - (4, 16, 17):  4 + 64 = 68 = 4·17 ✓
  - (12, 17, 20): 12 + 68 = 80 = 4·20 ✓
  - (48, 4, 16):  48 + 16 = 64 = 4·16 ✓
  - (48, 8, 20):  48 + 32 = 80 = 4·20 ✓
  - (48, 5, 17):  48 + 20 = 68 = 4·17 ✓ (TERMINAL MONO with all χ = χ(5))

  Threshold n ≥ 48 (forced by (48, ...) triples); we use h64 for compatibility.
-/

set_option maxHeartbeats 800000 in
/-- **R301 Case B sub-case (χ4=A, χ8=B) closure**: under h9_eq_16 +
  h4_eq_9 + h8_eq_12, derive False at n ≥ 64.
  Terminal (48, 5, 17) all third color C via 11 explicit triples. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_eq_12_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_eq_9 : χ 4 = χ 9)
    (h8_eq_12 : χ 8 = χ 12) :
    False := by
  -- Setup hχ values for trichotomy.
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ48 : χ 48 < 3 := hχk 48 (by omega) (by omega)
  -- Auto-distinctness: χ(9) ≠ χ(12), χ(12) ≠ χ(16).
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  -- Composite: h4_eq_16 (χ4 = χ16 via h4_eq_9 + h9_eq_16).
  have h4_eq_16 : χ 4 = χ 16 := h4_eq_9.trans h9_eq_16
  ------------------------------------------------------------
  -- S1: χ(5) = third color.
  ------------------------------------------------------------
  -- (16, 5, 9): χ(5) ≠ χ(9). Via h9_eq_16 (χ16 = χ9), so χ16 = χ5 AND χ5 = χ9 gives mono.
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  -- (12, 5, 8): χ(5) ≠ χ(12). Via h8_eq_12, the second conjunct always holds when χ5 = χ12.
  have h5_ne_12 : χ 5 ≠ χ 12 := by
    intro h5_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 5
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h5_eq_12]
    · show χ 5 = χ (5 + 3)
      rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]
  ------------------------------------------------------------
  -- S2: χ(10) = third color.
  ------------------------------------------------------------
  -- (4, 9, 10): χ(10) ≠ χ(9). Via h4_eq_9 (first conjunct trivial).
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 9
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_9
    · show χ 9 = χ (9 + 1)
      rw [show (9 + 1 : ℕ) = 10 by decide]; exact h10_eq_9.symm
  -- (8, 8, 10): χ(10) ≠ χ(12). Self-loop x=y; under h8_eq_12, χ8 = χ12, so χ10 = χ12 → mono.
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
  ------------------------------------------------------------
  -- S3: χ(5) = χ(10) (third color via trichotomy).
  ------------------------------------------------------------
  have h5_eq_10 : χ 5 = χ 10 := by
    -- Trichotomy: χ5 < 3, χ10 < 3, both ≠ χ9, both ≠ χ12, χ9 ≠ χ12.
    -- Therefore χ5 = χ10 = third color (omega-decidable).
    omega
  ------------------------------------------------------------
  -- S4: χ(20) = χ(12) (= B).
  ------------------------------------------------------------
  -- (16, 16, 20) self-loop: χ(20) ≠ χ(16).
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
  -- χ(20) ≠ χ(9) (via h9_eq_16).
  have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h20_ne_16 (h.trans h9_eq_16)
  -- (20, 5, 10): χ(20) ≠ χ(5) (using χ5 = χ10).
  have h20_ne_5 : χ 20 ≠ χ 5 := by
    intro h20_eq_5
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 5
      rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_5
    · show χ 5 = χ (5 + 5)
      rw [show (5 + 5 : ℕ) = 10 by decide]; exact h5_eq_10
  -- Trichotomy: χ20 ≠ χ9 (A), χ20 ≠ χ5 (C). With χ9 ≠ χ5 (h5_ne_9.symm),
  -- and χ12 ≠ χ9, χ12 ≠ χ5, conclude χ20 = χ12.
  have h20_eq_12 : χ 20 = χ 12 := by omega
  ------------------------------------------------------------
  -- S5: χ(17) = χ(5) (= C).
  ------------------------------------------------------------
  -- (4, 16, 17): χ(17) ≠ χ(16). Via h4_eq_16 (first conjunct trivial).
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
  have h17_ne_9 : χ 17 ≠ χ 9 := fun h => h17_ne_16 (h.trans h9_eq_16)
  -- (12, 17, 20): χ(17) ≠ χ(12). Via h20_eq_12 (second conjunct becomes χ17 = χ20 = χ12).
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 17
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h17_eq_12]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_12, ← h20_eq_12]
  -- Trichotomy: χ17 ≠ χ9, χ17 ≠ χ12 → χ17 = third color = χ5.
  have h17_eq_5 : χ 17 = χ 5 := by omega
  ------------------------------------------------------------
  -- S6: χ(48) = χ(5) (= C).
  ------------------------------------------------------------
  -- (48, 4, 16): χ(48) ≠ χ(16). Via h4_eq_16 (second conjunct trivial).
  have h48_ne_16 : χ 48 ≠ χ 16 := by
    intro h48_eq_16
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 4
      rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_16, ← h4_eq_16]
    · show χ 4 = χ (4 + 12)
      rw [show (4 + 12 : ℕ) = 16 by decide]; exact h4_eq_16
  have h48_ne_9 : χ 48 ≠ χ 9 := fun h => h48_ne_16 (h.trans h9_eq_16)
  -- (48, 8, 20): χ(48) ≠ χ(12). Via h8_eq_12 + h20_eq_12.
  have h48_ne_12 : χ 48 ≠ χ 12 := by
    intro h48_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 8
      rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_12, ← h8_eq_12]
    · show χ 8 = χ (8 + 12)
      rw [show (8 + 12 : ℕ) = 20 by decide, h8_eq_12, ← h20_eq_12]
  -- Trichotomy: χ48 = third color = χ5.
  have h48_eq_5 : χ 48 = χ 5 := by omega
  ------------------------------------------------------------
  -- TERMINAL: (48, 5, 17) all χ = χ(5).
  ------------------------------------------------------------
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 12) = χ 5
    rw [show (4 * 12 : ℕ) = 48 by decide]; exact h48_eq_5
  · show χ 5 = χ (5 + 12)
    rw [show (5 + 12 : ℕ) = 17 by decide, ← h17_eq_5]

/-! ### §143. R302 — Case B sub-case (χ4=B, χ8=A) closure.

  **Setup.** Under `h9_eq_16 + h4_eq_12 + h8_eq_9`, derive False at n ≥ 64.
  Short cascade: force `χ(32) = A`, then terminal (32, 8, 16) mono A.

  Notation: A := χ(9) = χ(16) = χ(8) (via h8_eq_9 + h9_eq_16);
            B := χ(12) = χ(4); C := third color.

  **Cascade**:
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | S1 | χ(5) = C   | (16, 5, 9) [≠A] + (4, 4, 5) [self-loop x=y; ≠B] |
  | S2 | χ(13) = C  | (16, 9, 13) [≠A] + (4, 12, 13) [≠B; uses h4_eq_12] |
  | S3 | χ(5) = χ(13) | omega trichotomy |
  | S4 | χ(32) ≠ B  | (32, 4, 12) [uses h4_eq_12] |
  | S5 | χ(32) ≠ χ(5) (= C) | (32, 5, 13) [uses S3] |
  | S6 | χ(32) = A  | omega trichotomy |
  | T  | (32, 8, 16) MONO A | χ(32) = χ(8) = χ(16) all A |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 5, 9):    16 + 20 = 36 = 4·9 ✓
  - (4, 4, 5):     4 + 16 = 20 = 4·5 ✓ (self-loop x=y)
  - (16, 9, 13):   16 + 36 = 52 = 4·13 ✓
  - (4, 12, 13):   4 + 48 = 52 = 4·13 ✓
  - (32, 4, 12):   32 + 16 = 48 = 4·12 ✓
  - (32, 5, 13):   32 + 20 = 52 = 4·13 ✓
  - (32, 8, 16):   32 + 32 = 64 = 4·16 ✓ (TERMINAL MONO A)

  Threshold n ≥ 32 (forced by (32, ...) triples); we use h64 for compatibility.
-/

set_option maxHeartbeats 400000 in
/-- **R302 Case B sub-case (χ4=B, χ8=A) closure**: under h9_eq_16 +
  h4_eq_12 + h8_eq_9, derive False at n ≥ 64.
  Terminal (32, 8, 16) all χ(9) = A via 7 explicit triples. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_9 : χ 8 = χ 9) :
    False := by
  -- Setup hχ values for omega trichotomy.
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- S1: χ(5) = third color (≠ A, ≠ B).
  ------------------------------------------------------------
  -- (16, 5, 9): χ(5) ≠ χ(9). Via h9_eq_16.
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  -- (4, 4, 5) self-loop x=y: χ(5) ≠ χ(4). Under h4_eq_12, χ(5) ≠ χ(12).
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
  ------------------------------------------------------------
  -- S2: χ(13) = third color.
  ------------------------------------------------------------
  -- (16, 9, 13): χ(13) ≠ χ(9). Via h9_eq_16.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 9
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
    · show χ 9 = χ (9 + 4)
      rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
  -- (4, 12, 13): χ(13) ≠ χ(12). Via h4_eq_12 (first conjunct trivial).
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
  ------------------------------------------------------------
  -- S3: χ(5) = χ(13) (both third color via omega trichotomy).
  ------------------------------------------------------------
  have h5_eq_13 : χ 5 = χ 13 := by omega
  ------------------------------------------------------------
  -- S4: χ(32) ≠ χ(12). Via (32, 4, 12) + h4_eq_12.
  ------------------------------------------------------------
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
  ------------------------------------------------------------
  -- S5: χ(32) ≠ χ(5). Via (32, 5, 13) using h5_eq_13.
  ------------------------------------------------------------
  have h32_ne_5 : χ 32 ≠ χ 5 := by
    intro h32_eq_5
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 5
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_5
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide]; exact h5_eq_13
  ------------------------------------------------------------
  -- S6: χ(32) = χ(9) (= A). By omega trichotomy.
  ------------------------------------------------------------
  have h32_eq_9 : χ 32 = χ 9 := by omega
  ------------------------------------------------------------
  -- TERMINAL: (32, 8, 16). χ(32) = χ(9), χ(8) = χ(9), χ(16) = χ(9). All A.
  ------------------------------------------------------------
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 8) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 8) = χ 8
    rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h8_eq_9]
  · show χ 8 = χ (8 + 8)
    rw [show (8 + 8 : ℕ) = 16 by decide, h8_eq_9, ← h9_eq_16]

/-! ### §144. R303 — Case B sub-case (χ4=A, χ8=C) closure — SHORTEST so far.

  **Setup.** Under `h9_eq_16 + h4_eq_9 + h8_ne_9 + h8_ne_12` (so χ8 = third
  color C by omega), derive False at n ≥ 64.

  Notation: A := χ(9) = χ(16) = χ(4); B := χ(12); C := χ(8).

  **5-triple cascade + terminal (4, 15, 16) MONO A**:
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | S1 | χ(10) = B  | (4, 9, 10) [≠A; uses h4_eq_9] + (8, 8, 10) [self-loop x=y; ≠C] + omega |
  | S2 | χ(13) = C  | (16, 9, 13) [≠A; uses h9_eq_16] + (12, 10, 13) [≠B; uses S1] + omega |
  | S3 | χ(15) = A  | (12, 12, 15) [self-loop x=y; ≠B] + (8, 13, 15) [≠C; uses S2] + omega |
  | T  | (4, 15, 16) MONO A | χ(4) = χ(15) = χ(16) all A |

  Only 6 explicit triples — **shortest Case B sub-case closure**.

  All triples verified for b=4 (x + 4y = 4z):
  - (4, 9, 10):    4 + 36 = 40 = 4·10 ✓
  - (8, 8, 10):    8 + 32 = 40 = 4·10 ✓ (self-loop x=y)
  - (16, 9, 13):   16 + 36 = 52 = 4·13 ✓
  - (12, 10, 13):  12 + 40 = 52 = 4·13 ✓
  - (12, 12, 15):  12 + 48 = 60 = 4·15 ✓ (self-loop x=y)
  - (8, 13, 15):   8 + 52 = 60 = 4·15 ✓
  - (4, 15, 16):   4 + 60 = 64 = 4·16 ✓ (TERMINAL MONO A)

  Threshold n ≥ 16 (forced by (4, 15, 16)). Use h64 for compatibility.
-/

set_option maxHeartbeats 400000 in
/-- **R303 Case B sub-case (χ4=A, χ8=C) closure**: under h9_eq_16 +
  h4_eq_9 + h8_ne_9 + h8_ne_12, derive False at n ≥ 64.
  Terminal (4, 15, 16) all A via 6 triples + 3 omega trichotomies. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_third_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_eq_9 : χ 4 = χ 9)
    (h8_ne_9 : χ 8 ≠ χ 9)
    (h8_ne_12 : χ 8 ≠ χ 12) :
    False := by
  -- Setup hχ values for omega trichotomy.
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- S1: χ(10) = χ(12) (= B).
  ------------------------------------------------------------
  -- (4, 9, 10): χ(10) ≠ χ(9). Via h4_eq_9.
  have h10_ne_9 : χ 10 ≠ χ 9 := by
    intro h10_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 9
      rw [show (4 * 1 : ℕ) = 4 by decide]; exact h4_eq_9
    · show χ 9 = χ (9 + 1)
      rw [show (9 + 1 : ℕ) = 10 by decide]; exact h10_eq_9.symm
  -- (8, 8, 10) self-loop x=y: χ(10) ≠ χ(8).
  have h10_ne_8 : χ 10 ≠ χ 8 := by
    intro h10_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide]; exact h10_eq_8.symm
  -- Trichotomy: χ10 ≠ χ9, χ10 ≠ χ8. Three distinct anchors {χ8, χ9, χ12}.
  have h10_eq_12 : χ 10 = χ 12 := by omega
  ------------------------------------------------------------
  -- S2: χ(13) = χ(8) (= C).
  ------------------------------------------------------------
  -- (16, 9, 13): χ(13) ≠ χ(9). Via h9_eq_16.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 9
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
    · show χ 9 = χ (9 + 4)
      rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
  -- (12, 10, 13): χ(13) ≠ χ(12). Via h10_eq_12.
  have h13_ne_12 : χ 13 ≠ χ 12 := by
    intro h13_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 10
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h10_eq_12]
    · show χ 10 = χ (10 + 3)
      rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_12, h13_eq_12]
  -- Trichotomy: χ13 ≠ χ9, χ13 ≠ χ12 → χ13 = χ8 (third color = C).
  have h13_eq_8 : χ 13 = χ 8 := by omega
  ------------------------------------------------------------
  -- S3: χ(15) = χ(9) (= A).
  ------------------------------------------------------------
  -- (12, 12, 15) self-loop x=y: χ(15) ≠ χ(12).
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
  -- (8, 13, 15): χ(15) ≠ χ(8). Via h13_eq_8.
  have h15_ne_8 : χ 15 ≠ χ 8 := by
    intro h15_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 13
      rw [show (4 * 2 : ℕ) = 8 by decide, ← h13_eq_8]
    · show χ 13 = χ (13 + 2)
      rw [show (13 + 2 : ℕ) = 15 by decide, h13_eq_8, h15_eq_8]
  -- Trichotomy: χ15 ≠ χ12, χ15 ≠ χ8 → χ15 = χ9 (= A).
  have h15_eq_9 : χ 15 = χ 9 := by omega
  ------------------------------------------------------------
  -- TERMINAL: (4, 15, 16). All A.
  ------------------------------------------------------------
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 1) (y := 15) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 1) = χ 15
    rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_9, ← h15_eq_9]
  · show χ 15 = χ (15 + 1)
    rw [show (15 + 1 : ℕ) = 16 by decide, h15_eq_9, ← h9_eq_16]

/-! ### §145. R304 — Case B sub-case (χ4=B, χ8=C) closure — no-color-left on χ(7).

  **Setup.** Under `h9_eq_16 + h4_eq_12 + h8_ne_9 + h8_ne_12` (so χ8 = C),
  derive False at n ≥ 64. Distinct closure pattern: instead of MONO terminal,
  we derive a **no-color-left contradiction** on χ(7).

  Notation: A := χ(9) = χ(16); B := χ(12) = χ(4); C := χ(8).

  **4-step force + no-color-left**:
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | S1 | χ(5) = C   | (16, 5, 9) [≠A; h9_eq_16] + (4, 4, 5) [self-loop x=y; ≠B] + omega |
  | S2 | χ(13) = C  | (16, 9, 13) [≠A] + (4, 12, 13) [≠B; h4_eq_12] + omega |
  | S3 | χ(15) = A  | (12, 12, 15) [self-loop x=y; ≠B] + (8, 13, 15) [≠C; uses S2] + omega |
  | S4 | χ(32) = A  | (32, 4, 12) [≠B; h4_eq_12] + (32, 5, 13) [≠C; uses S1+S2] + omega |
  | **T** | **χ(7) no-color-left** | (8, 5, 7) [≠C] + (12, 4, 7) [≠B] + (32, 7, 15) [≠A] |

  **No-color-left contradiction**: χ(7) < 3, ≠ χ(8) = C, ≠ χ(12) = B,
  ≠ χ(9) = A — impossible since A, B, C span {0, 1, 2}. omega closes.

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 5, 9):    16 + 20 = 36 = 4·9 ✓
  - (4, 4, 5):     4 + 16 = 20 = 4·5 ✓ (self-loop x=y)
  - (16, 9, 13):   16 + 36 = 52 = 4·13 ✓
  - (4, 12, 13):   4 + 48 = 52 = 4·13 ✓
  - (12, 12, 15):  12 + 48 = 60 = 4·15 ✓ (self-loop x=y)
  - (8, 13, 15):   8 + 52 = 60 = 4·15 ✓
  - (32, 4, 12):   32 + 16 = 48 = 4·12 ✓
  - (32, 5, 13):   32 + 20 = 52 = 4·13 ✓
  - (8, 5, 7):     8 + 20 = 28 = 4·7 ✓
  - (12, 4, 7):    12 + 16 = 28 = 4·7 ✓
  - (32, 7, 15):   32 + 28 = 60 = 4·15 ✓

  Max position 32. n ≥ 64 used for compatibility with sub-case API.
-/

set_option maxHeartbeats 400000 in
/-- **R304 Case B sub-case (χ4=B, χ8=C) closure**: under h9_eq_16 +
  h4_eq_12 + h8_ne_9 + h8_ne_12, derive False at n ≥ 64.
  No-color-left contradiction on χ(7) via 11 triples + 4 omega trichotomies. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_third_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_ne_9 : χ 8 ≠ χ 9)
    (h8_ne_12 : χ 8 ≠ χ 12) :
    False := by
  -- Setup hχ values.
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ7 : χ 7 < 3 := hχk 7 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- S1: χ(5) = χ(8) (= C).
  ------------------------------------------------------------
  -- (16, 5, 9): χ(5) ≠ χ(9). Via h9_eq_16.
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  -- (4, 4, 5) self-loop x=y: χ(5) ≠ χ(12). Via h4_eq_12.
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
  have h5_eq_8 : χ 5 = χ 8 := by omega
  ------------------------------------------------------------
  -- S2: χ(13) = χ(8) (= C).
  ------------------------------------------------------------
  -- (16, 9, 13): χ(13) ≠ χ(9). Via h9_eq_16.
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 9
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
    · show χ 9 = χ (9 + 4)
      rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
  -- (4, 12, 13): χ(13) ≠ χ(12). Via h4_eq_12.
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
  have h13_eq_8 : χ 13 = χ 8 := by omega
  ------------------------------------------------------------
  -- S3: χ(15) = χ(9) (= A).
  ------------------------------------------------------------
  -- (12, 12, 15) self-loop x=y: χ(15) ≠ χ(12).
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
  -- (8, 13, 15): χ(15) ≠ χ(8). Via h13_eq_8.
  have h15_ne_8 : χ 15 ≠ χ 8 := by
    intro h15_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 13) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 13
      rw [show (4 * 2 : ℕ) = 8 by decide, ← h13_eq_8]
    · show χ 13 = χ (13 + 2)
      rw [show (13 + 2 : ℕ) = 15 by decide, h13_eq_8, h15_eq_8]
  have h15_eq_9 : χ 15 = χ 9 := by omega
  ------------------------------------------------------------
  -- S4: χ(32) = χ(9) (= A).
  ------------------------------------------------------------
  -- (32, 4, 12): χ(32) ≠ χ(12). Via h4_eq_12.
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
  -- (32, 5, 13): χ(32) ≠ χ(8). Via h5_eq_8 + h13_eq_8.
  have h32_ne_8 : χ 32 ≠ χ 8 := by
    intro h32_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 5
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_8, ← h5_eq_8]
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_8, ← h13_eq_8]
  have h32_eq_9 : χ 32 = χ 9 := by omega
  ------------------------------------------------------------
  -- TERMINAL: no-color-left on χ(7).
  ------------------------------------------------------------
  -- (8, 5, 7): χ(7) ≠ χ(8). Via h5_eq_8.
  have h7_ne_8 : χ 7 ≠ χ 8 := by
    intro h7_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 5
      rw [show (4 * 2 : ℕ) = 8 by decide, ← h5_eq_8]
    · show χ 5 = χ (5 + 2)
      rw [show (5 + 2 : ℕ) = 7 by decide, h5_eq_8, h7_eq_8]
  -- (12, 4, 7): χ(7) ≠ χ(12). Via h4_eq_12.
  have h7_ne_12 : χ 7 ≠ χ 12 := by
    intro h7_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 4
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h4_eq_12]
    · show χ 4 = χ (4 + 3)
      rw [show (4 + 3 : ℕ) = 7 by decide, h4_eq_12, h7_eq_12]
  -- (32, 7, 15): χ(7) ≠ χ(9). Via h32_eq_9 + h15_eq_9.
  have h7_ne_9 : χ 7 ≠ χ 9 := by
    intro h7_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 7) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 7
      rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_9, ← h7_eq_9]
    · show χ 7 = χ (7 + 8)
      rw [show (7 + 8 : ℕ) = 15 by decide, h7_eq_9, ← h15_eq_9]
  -- No-color-left: χ(7) < 3, ≠ χ(8), ≠ χ(12), ≠ χ(9). A, B, C span {0,1,2}. omega.
  omega

/-! ### §146. R305 — Case B sub-case (χ4=C, χ8=B) closure — SHORTEST overall.

  **Setup.** Under `h9_eq_16 + h4_ne_9 + h4_ne_12 + h8_eq_12` (so χ4 = C),
  derive False at n ≥ 64. **Just 3 explicit triples** — currently the
  shortest Case B sub-case.

  Notation: A := χ(9) = χ(16); B := χ(8) = χ(12); C := χ(4).

  **Cascade**:
  | Step | Position | Triple(s) |
  |------|----------|-----------|
  | S1 | χ(5) = B   | (16, 5, 9) [≠A] + (4, 4, 5) [self-loop; ≠C] + omega |
  | T  | (12, 5, 8) MONO B | χ(12) = χ(5) = χ(8) all B |

  All triples verified for b=4 (x + 4y = 4z):
  - (16, 5, 9):    16 + 20 = 36 = 4·9 ✓
  - (4, 4, 5):     4 + 16 = 20 = 4·5 ✓ (self-loop x=y)
  - (12, 5, 8):    12 + 20 = 32 = 4·8 ✓ (TERMINAL MONO B)

  Max position 12. n ≥ 64 used for compatibility.
-/

set_option maxHeartbeats 400000 in
/-- **R305 Case B sub-case (χ4=C, χ8=B) closure**: under h9_eq_16 +
  h4_ne_9 + h4_ne_12 + h8_eq_12, derive False at n ≥ 64.
  Just 3 triples — shortest Case B sub-case. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_12_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_ne_9 : χ 4 ≠ χ 9)
    (h4_ne_12 : χ 4 ≠ χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    False := by
  -- Setup hχ values for omega trichotomy.
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- S1: χ(5) = χ(12) (= B).
  ------------------------------------------------------------
  -- (16, 5, 9): χ(5) ≠ χ(9). Via h9_eq_16.
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  -- (4, 4, 5) self-loop x=y: χ(5) ≠ χ(4).
  have h5_ne_4 : χ 5 ≠ χ 4 := by
    intro h5_eq_4
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h5_eq_4]
  -- Trichotomy: {χ4, χ9, χ12} three distinct values < 3, χ5 ≠ χ9, χ5 ≠ χ4.
  -- So χ5 = χ12.
  have h5_eq_12 : χ 5 = χ 12 := by omega
  ------------------------------------------------------------
  -- TERMINAL: (12, 5, 8). All B (= χ(12)).
  ------------------------------------------------------------
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 3) = χ 5
    rw [show (4 * 3 : ℕ) = 12 by decide, ← h5_eq_12]
  · show χ 5 = χ (5 + 3)
    rw [show (5 + 3 : ℕ) = 8 by decide, h5_eq_12, ← h8_eq_12]

/-! ### §147. R306 — Case B sub-case (χ4=C, χ8=A) closure — 3-way branch.

  **Setup.** Under `h9_eq_16 + h4_ne_9 + h4_ne_12 + h8_eq_9`, derive False
  at n ≥ 64. Most complex Case B sub-case so far: requires nested branching
  on χ(10) ∈ {B, C} and (within χ(10) = C) on χ(13) ∈ {B, C}.

  Notation: A := χ(9) = χ(16) = χ(8); B := χ(12); C := χ(4).

  **Universal forced colors** (under (C, A)):
  - χ(5) = B (via (16, 5, 9) + (4, 4, 5) self-loop + omega)
  - χ(28) ≠ A (via (28, 9, 16))
  - χ(10) ≠ A (via (8, 8, 10) self-loop)

  **Branch I (χ(10) = B)**:
  - χ(20) = C (via (20, 5, 10) + (16, 16, 20) + omega)
  - χ(13) = C (via (12, 10, 13) + (16, 9, 13) + omega)
  - χ(28) = B (via (28, 13, 20) + omega)
  - Terminal (28, 5, 12) all B → MONO.

  **Branch II (χ(10) = C)**: χ(28) = C (via (28, 5, 12) excl B + omega).
  - Sub-branch II.A (χ(13) = B):
    - χ(32) = C, χ(18) = B, χ(20) = C.
    - Terminal (32, 20, 28) all C → MONO.
  - Sub-branch II.B (χ(13) = C):
    - χ(20) = B, χ(32) = C, χ(18) = B, χ(21) = A, χ(23) = C,
    - χ(17) = A, χ(15) = C.
    - Terminal (32, 15, 23) all C → MONO.

  All triples verified for b=4 (x + 4y = 4z).
-/

set_option maxHeartbeats 1600000 in
/-- **R306 Case B sub-case (χ4=C, χ8=A) closure**: under h9_eq_16 +
  h4_ne_9 + h4_ne_12 + h8_eq_9, derive False at n ≥ 64.
  Nested branch on χ(10) and (within χ(10) = C) on χ(13). -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_9_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_ne_9 : χ 4 ≠ χ 9)
    (h4_ne_12 : χ 4 ≠ χ 12)
    (h8_eq_9 : χ 8 = χ 9) :
    False := by
  -- Setup hχ values.
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ18 : χ 18 < 3 := hχk 18 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ23 : χ 23 < 3 := hχk 23 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- UNIVERSAL: χ(5) = χ(12) (= B).
  ------------------------------------------------------------
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  have h5_ne_4 : χ 5 ≠ χ 4 := by
    intro h5_eq_4
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h5_eq_4]
  have h5_eq_12 : χ 5 = χ 12 := by omega
  ------------------------------------------------------------
  -- UNIVERSAL: χ(28) ≠ χ(9), χ(10) ≠ χ(9) (≠ A).
  ------------------------------------------------------------
  have h28_ne_9 : χ 28 ≠ χ 9 := by
    intro h28_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 9
      rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_9
    · show χ 9 = χ (9 + 7)
      rw [show (9 + 7 : ℕ) = 16 by decide]; exact h9_eq_16
  have h10_ne_8 : χ 10 ≠ χ 8 := by
    intro h10_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide]; exact h10_eq_8.symm
  have h10_ne_9 : χ 10 ≠ χ 9 := fun h => h10_ne_8 (h.trans h8_eq_9.symm)
  -- (16, 16, 20) self-loop: χ(20) ≠ A.
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
  have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h20_ne_16 (h.trans h9_eq_16)
  ------------------------------------------------------------
  -- BRANCH on χ(10) ∈ {B, C}.
  ------------------------------------------------------------
  by_cases h10_eq_12 : χ 10 = χ 12
  · ----------------------------------------------------------
    -- BRANCH I: χ(10) = B.
    ----------------------------------------------------------
    -- (20, 5, 10): χ(20) ≠ χ(12).
    have h20_ne_12 : χ 20 ≠ χ 12 := by
      intro h20_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 5
        rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 5)
        rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_12, ← h10_eq_12]
    have h20_eq_4 : χ 20 = χ 4 := by omega
    -- (12, 10, 13): χ(13) ≠ χ(12).
    have h13_ne_12 : χ 13 ≠ χ 12 := by
      intro h13_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 3) = χ 10
        rw [show (4 * 3 : ℕ) = 12 by decide, ← h10_eq_12]
      · show χ 10 = χ (10 + 3)
        rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_12, h13_eq_12]
    -- (16, 9, 13): χ(13) ≠ χ(9).
    have h13_ne_9 : χ 13 ≠ χ 9 := by
      intro h13_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 9
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
      · show χ 9 = χ (9 + 4)
        rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
    have h13_eq_4 : χ 13 = χ 4 := by omega
    -- (28, 13, 20): χ(28) ≠ χ(4) (= χ13 = χ20).
    have h28_ne_4 : χ 28 ≠ χ 4 := by
      intro h28_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 13) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 13
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_4, ← h13_eq_4]
      · show χ 13 = χ (13 + 7)
        rw [show (13 + 7 : ℕ) = 20 by decide, h13_eq_4, ← h20_eq_4]
    have h28_eq_12 : χ 28 = χ 12 := by omega
    -- TERMINAL (28, 5, 12): all B.
    have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 7) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRadoT
    refine ⟨?_, ?_⟩
    · show χ (4 * 7) = χ 5
      rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_12, ← h5_eq_12]
    · show χ 5 = χ (5 + 7)
      rw [show (5 + 7 : ℕ) = 12 by decide]; exact h5_eq_12
  · ----------------------------------------------------------
    -- BRANCH II: χ(10) ≠ B. So χ(10) = C.
    ----------------------------------------------------------
    have h10_eq_4 : χ 10 = χ 4 := by omega
    -- (28, 5, 12): χ(28) ≠ χ(12).
    have h28_ne_12 : χ 28 ≠ χ 12 := by
      intro h28_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 5
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 7)
        rw [show (5 + 7 : ℕ) = 12 by decide]; exact h5_eq_12
    have h28_eq_4 : χ 28 = χ 4 := by omega
    -- (32, 8, 16): χ(32) ≠ χ(8) (= A).
    have h32_ne_8 : χ 32 ≠ χ 8 := by
      intro h32_eq_8
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 8
        rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_8
      · show χ 8 = χ (8 + 8)
        rw [show (8 + 8 : ℕ) = 16 by decide]; exact h8_eq_9.trans h9_eq_16
    have h32_ne_9 : χ 32 ≠ χ 9 := fun h => h32_ne_8 (h.trans h8_eq_9.symm)
    -- (8, 16, 18): χ(18) ≠ A.
    have h18_ne_16 : χ 18 ≠ χ 16 := by
      intro h18_eq_16
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 2) (y := 16) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 2) = χ 16
        rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_9.trans h9_eq_16
      · show χ 16 = χ (16 + 2)
        rw [show (16 + 2 : ℕ) = 18 by decide, h18_eq_16]
    have h18_ne_9 : χ 18 ≠ χ 9 := fun h => h18_ne_16 (h.trans h9_eq_16)
    ----------------------------------------------------------
    -- Sub-branch on χ(13) ∈ {B, C}.
    ----------------------------------------------------------
    by_cases h13_eq_12 : χ 13 = χ 12
    · --------------------------------------------------------
      -- BRANCH II.A: χ(13) = B.
      --------------------------------------------------------
      -- (32, 5, 13): χ(32) ≠ χ(12).
      have h32_ne_12 : χ 32 ≠ χ 12 := by
        intro h32_eq_12
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 5
          rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h5_eq_12]
        · show χ 5 = χ (5 + 8)
          rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_12, ← h13_eq_12]
      have h32_eq_4 : χ 32 = χ 4 := by omega
      -- (32, 10, 18): χ(18) ≠ χ(4).
      have h18_ne_4 : χ 18 ≠ χ 4 := by
        intro h18_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 10) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 10
          rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h10_eq_4]
        · show χ 10 = χ (10 + 8)
          rw [show (10 + 8 : ℕ) = 18 by decide, h10_eq_4, h18_eq_4]
      have h18_eq_12 : χ 18 = χ 12 := by omega
      -- (20, 13, 18): χ(20) ≠ χ(12).
      have h20_ne_12 : χ 20 ≠ χ 12 := by
        intro h20_eq_12
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 5) (y := 13) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 5) = χ 13
          rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, ← h13_eq_12]
        · show χ 13 = χ (13 + 5)
          rw [show (13 + 5 : ℕ) = 18 by decide, h13_eq_12, ← h18_eq_12]
      have h20_eq_4 : χ 20 = χ 4 := by omega
      -- TERMINAL (32, 20, 28): all C.
      have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 20) (by omega) (by omega) (by omega) (by omega)
      apply hRadoT
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 20
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h20_eq_4]
      · show χ 20 = χ (20 + 8)
        rw [show (20 + 8 : ℕ) = 28 by decide, h20_eq_4, ← h28_eq_4]
    · --------------------------------------------------------
      -- BRANCH II.B: χ(13) ≠ B. So χ(13) = C.
      --------------------------------------------------------
      -- (16, 9, 13): χ(13) ≠ A.
      have h13_ne_9 : χ 13 ≠ χ 9 := by
        intro h13_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 4) = χ 9
          rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
        · show χ 9 = χ (9 + 4)
          rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
      have h13_eq_4 : χ 13 = χ 4 := by omega
      -- (28, 13, 20): χ(20) ≠ χ(4).
      have h20_ne_4 : χ 20 ≠ χ 4 := by
        intro h20_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 7) (y := 13) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 7) = χ 13
          rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_4, ← h13_eq_4]
        · show χ 13 = χ (13 + 7)
          rw [show (13 + 7 : ℕ) = 20 by decide, h13_eq_4, h20_eq_4]
      have h20_eq_12 : χ 20 = χ 12 := by omega
      -- (32, 12, 20): χ(32) ≠ χ(12).
      have h32_ne_12 : χ 32 ≠ χ 12 := by
        intro h32_eq_12
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 12) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 12
          rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_12
        · show χ 12 = χ (12 + 8)
          rw [show (12 + 8 : ℕ) = 20 by decide]; exact h20_eq_12.symm
      have h32_eq_4 : χ 32 = χ 4 := by omega
      -- (32, 10, 18): χ(18) ≠ χ(4).
      have h18_ne_4 : χ 18 ≠ χ 4 := by
        intro h18_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 10) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 10
          rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h10_eq_4]
        · show χ 10 = χ (10 + 8)
          rw [show (10 + 8 : ℕ) = 18 by decide, h10_eq_4, h18_eq_4]
      have h18_eq_12 : χ 18 = χ 12 := by omega
      -- (12, 18, 21): χ(21) ≠ χ(12).
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
      -- (32, 13, 21): χ(21) ≠ χ(4).
      have h21_ne_4 : χ 21 ≠ χ 4 := by
        intro h21_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 8) (y := 13) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 8) = χ 13
          rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h13_eq_4]
        · show χ 13 = χ (13 + 8)
          rw [show (13 + 8 : ℕ) = 21 by decide, h13_eq_4, h21_eq_4]
      have h21_eq_9 : χ 21 = χ 9 := by omega
      -- (8, 21, 23): χ(23) ≠ χ(9).
      have h23_ne_9 : χ 23 ≠ χ 9 := by
        intro h23_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 2) (y := 21) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 2) = χ 21
          rw [show (4 * 2 : ℕ) = 8 by decide]; exact h8_eq_9.trans h21_eq_9.symm
        · show χ 21 = χ (21 + 2)
          rw [show (21 + 2 : ℕ) = 23 by decide, h21_eq_9, ← h23_eq_9]
      -- (20, 18, 23): χ(23) ≠ χ(12).
      have h23_ne_12 : χ 23 ≠ χ 12 := by
        intro h23_eq_12
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 5) (y := 18) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 5) = χ 18
          rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, ← h18_eq_12]
        · show χ 18 = χ (18 + 5)
          rw [show (18 + 5 : ℕ) = 23 by decide, h18_eq_12, h23_eq_12]
      have h23_eq_4 : χ 23 = χ 4 := by omega
      -- (28, 10, 17): χ(17) ≠ χ(4).
      have h17_ne_4 : χ 17 ≠ χ 4 := by
        intro h17_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 7) (y := 10) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 7) = χ 10
          rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_4, ← h10_eq_4]
        · show χ 10 = χ (10 + 7)
          rw [show (10 + 7 : ℕ) = 17 by decide, h10_eq_4, h17_eq_4]
      -- (12, 17, 20): χ(17) ≠ χ(12).
      have h17_ne_12 : χ 17 ≠ χ 12 := by
        intro h17_eq_12
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 3) = χ 17
          rw [show (4 * 3 : ℕ) = 12 by decide, ← h17_eq_12]
        · show χ 17 = χ (17 + 3)
          rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_12, ← h20_eq_12]
      have h17_eq_9 : χ 17 = χ 9 := by omega
      -- (12, 12, 15) self-loop: χ(15) ≠ χ(12).
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
      -- (8, 15, 17): χ(15) ≠ χ(9).
      have h15_ne_9 : χ 15 ≠ χ 9 := by
        intro h15_eq_9
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 2) (y := 15) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 2) = χ 15
          rw [show (4 * 2 : ℕ) = 8 by decide, h8_eq_9, ← h15_eq_9]
        · show χ 15 = χ (15 + 2)
          rw [show (15 + 2 : ℕ) = 17 by decide, h15_eq_9, ← h17_eq_9]
      have h15_eq_4 : χ 15 = χ 4 := by omega
      -- TERMINAL (32, 15, 23): all C.
      have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 15) (by omega) (by omega) (by omega) (by omega)
      apply hRadoT
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 15
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h15_eq_4]
      · show χ 15 = χ (15 + 8)
        rw [show (15 + 8 : ℕ) = 23 by decide, h15_eq_4, ← h23_eq_4]

/-! ### §148. R307 — Case B sub-case (χ4=B, χ8=B) closure — 3-way branch + shared downstream.

  **Setup.** Under `h9_eq_16 + h4_eq_12 + h8_eq_12`, derive False at n ≥ 64.
  Cell-(1)-shape under h9_eq_16: complex 3-way branching on χ(10) and (within
  one branch) χ(11), all converging at χ(20) = B, then shared downstream
  cascade to terminal (64, 5, 21) all C.

  Notation: A := χ(9) = χ(16); B := χ(4) = χ(8) = χ(12); C := third color.

  **Universal forced** (under (B, B)):
  - χ(5) = C, χ(13) = C, χ(32) = A.

  **χ(20) = B via 3-way branch** (all converge):
  - Branch I (χ(10) = C): (20, 5, 10) → χ(20) ≠ C; +χ(20) ≠ A → χ(20) = B.
  - Branch II (χ(10) = A): χ(6) = C, then:
    - II.B (χ(11) = C): (20, 6, 11) → χ(20) ≠ C → χ(20) = B.
    - II.A (χ(11) = A): χ(15) = C via (16, 11, 15); (20, 15, 20) self-loop → χ(20) ≠ C → χ(20) = B.

  **Shared downstream cascade** (after χ(20) = B):
  - χ(17) = C via (32, 9, 17) + (12, 17, 20) + omega.
  - χ(48) = A via (48, 8, 20) + (48, 5, 17) + omega.
  - χ(21) = C via (4, 20, 21) + (48, 9, 21) + omega.
  - χ(64) = C via (64, 4, 20) + (64, 16, 32) + omega.
  - **TERMINAL (64, 5, 21)**: all C → MONO!

  Major triples verified (and many more):
  - (32, 4, 12): excludes χ(32) = B.
  - (32, 5, 13): excludes χ(32) = C.
  - (64, 4, 20): 64 + 16 = 80 = 4·20 ✓
  - (64, 16, 32): 64 + 64 = 128 = 4·32 ✓
  - (64, 5, 21): 64 + 20 = 84 = 4·21 ✓ (TERMINAL MONO C)
-/

set_option maxHeartbeats 1600000 in
/-- **R307 Case B sub-case (χ4=B, χ8=B) closure**: under h9_eq_16 +
  h4_eq_12 + h8_eq_12, derive False at n ≥ 64. 3-way nested branch
  converging at χ(20) = B, then shared downstream to terminal (64, 5, 21). -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_12_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_eq_12 : χ 4 = χ 12)
    (h8_eq_12 : χ 8 = χ 12) :
    False := by
  -- Setup hχ values.
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  have hχ48 : χ 48 < 3 := hχk 48 (by omega) (by omega)
  have hχ64 : χ 64 < 3 := hχk 64 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  have h4_eq_8 : χ 4 = χ 8 := h4_eq_12.trans h8_eq_12.symm
  ------------------------------------------------------------
  -- UNIVERSAL: χ(5) = C, χ(13) = C, χ(32) = A.
  ------------------------------------------------------------
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
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
  have h13_ne_9 : χ 13 ≠ χ 9 := by
    intro h13_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 9
      rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
    · show χ 9 = χ (9 + 4)
      rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
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
  have h5_eq_13 : χ 5 = χ 13 := by omega
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
  have h32_ne_5 : χ 32 ≠ χ 5 := by
    intro h32_eq_5
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 5
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_5
    · show χ 5 = χ (5 + 8)
      rw [show (5 + 8 : ℕ) = 13 by decide]; exact h5_eq_13
  have h32_eq_9 : χ 32 = χ 9 := by omega
  -- (16, 16, 20) self-loop: χ(20) ≠ A.
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
  have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h20_ne_16 (h.trans h9_eq_16)
  ------------------------------------------------------------
  -- χ(20) = B via 3-way branch (all converge).
  ------------------------------------------------------------
  have h20_ne_5 : χ 20 ≠ χ 5 := by
    by_cases h10_eq_5 : χ 10 = χ 5
    · -- BRANCH I: χ(10) = C.
      intro h20_eq_5
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 5
        rw [show (4 * 5 : ℕ) = 20 by decide]; exact h20_eq_5
      · show χ 5 = χ (5 + 5)
        rw [show (5 + 5 : ℕ) = 10 by decide]; exact h10_eq_5.symm
    · -- BRANCH II: χ(10) ≠ C. Combined with χ(10) ≠ B (self-loop) → χ(10) = A.
      have h10_ne_8 : χ 10 ≠ χ 8 := by
        intro h10_eq_8
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 2) = χ 8
          rw [show (4 * 2 : ℕ) = 8 by decide]
        · show χ 8 = χ (8 + 2)
          rw [show (8 + 2 : ℕ) = 10 by decide]; exact h10_eq_8.symm
      have h10_ne_12 : χ 10 ≠ χ 12 := fun h => h10_ne_8 (h.trans h8_eq_12.symm)
      have h10_eq_9 : χ 10 = χ 9 := by omega
      -- χ(6) = C via (8, 4, 6) + (16, 6, 10).
      have h6_ne_4 : χ 6 ≠ χ 4 := by
        intro h6_eq_4
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 2) (y := 4) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 2) = χ 4
          rw [show (4 * 2 : ℕ) = 8 by decide]; exact h4_eq_8.symm
        · show χ 4 = χ (4 + 2)
          rw [show (4 + 2 : ℕ) = 6 by decide]; exact h6_eq_4.symm
      have h6_ne_12 : χ 6 ≠ χ 12 := fun h => h6_ne_4 (h.trans h4_eq_12.symm)
      have h6_ne_16 : χ 6 ≠ χ 16 := by
        intro h6_eq_16
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 4) = χ 6
          rw [show (4 * 4 : ℕ) = 16 by decide, ← h6_eq_16]
        · show χ 6 = χ (6 + 4)
          rw [show (6 + 4 : ℕ) = 10 by decide, h6_eq_16, ← h9_eq_16, ← h10_eq_9]
      have h6_ne_9 : χ 6 ≠ χ 9 := fun h => h6_ne_16 (h.trans h9_eq_16)
      have h6_eq_5 : χ 6 = χ 5 := by omega
      -- (4, 11, 12): χ(11) ≠ B (universal but used here).
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
      ----------------------------------------------------------
      -- Sub-branch on χ(11).
      ----------------------------------------------------------
      by_cases h11_eq_5 : χ 11 = χ 5
      · -- BRANCH II.B: χ(11) = C.
        intro h20_eq_5
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 5) = χ 6
          rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_5, ← h6_eq_5]
        · show χ 6 = χ (6 + 5)
          rw [show (6 + 5 : ℕ) = 11 by decide, h6_eq_5, ← h11_eq_5]
      · -- BRANCH II.A: χ(11) ≠ C. Combined with χ(11) ≠ B → χ(11) = A.
        have h11_eq_9 : χ 11 = χ 9 := by omega
        -- (16, 11, 15): χ(15) ≠ A.
        have h15_ne_9 : χ 15 ≠ χ 9 := by
          intro h15_eq_9
          have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
            (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
          apply hRado
          refine ⟨?_, ?_⟩
          · show χ (4 * 4) = χ 11
            rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h11_eq_9]
          · show χ 11 = χ (11 + 4)
            rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_9, h15_eq_9]
        -- (12, 12, 15) self-loop: χ(15) ≠ B.
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
        have h15_eq_5 : χ 15 = χ 5 := by omega
        -- (20, 15, 20) self-loop x=z: χ(20) ≠ χ(15) (= C = χ5).
        intro h20_eq_5
        have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
          (d := 5) (y := 15) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (4 * 5) = χ 15
          rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_5, ← h15_eq_5]
        · show χ 15 = χ (15 + 5)
          rw [show (15 + 5 : ℕ) = 20 by decide, h15_eq_5, h20_eq_5]
  ------------------------------------------------------------
  -- After 3-way branch: χ(20) = B (via omega).
  ------------------------------------------------------------
  have h20_eq_12 : χ 20 = χ 12 := by omega
  ------------------------------------------------------------
  -- SHARED DOWNSTREAM CASCADE.
  ------------------------------------------------------------
  -- (32, 9, 17): χ(17) ≠ A.
  have h17_ne_9 : χ 17 ≠ χ 9 := by
    intro h17_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 8) = χ 9
      rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
    · show χ 9 = χ (9 + 8)
      rw [show (9 + 8 : ℕ) = 17 by decide, h17_eq_9]
  -- (12, 17, 20): χ(17) ≠ B.
  have h17_ne_12 : χ 17 ≠ χ 12 := by
    intro h17_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 17) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 3) = χ 17
      rw [show (4 * 3 : ℕ) = 12 by decide, ← h17_eq_12]
    · show χ 17 = χ (17 + 3)
      rw [show (17 + 3 : ℕ) = 20 by decide, h17_eq_12, ← h20_eq_12]
  have h17_eq_5 : χ 17 = χ 5 := by omega
  -- (48, 8, 20): χ(48) ≠ B.
  have h48_ne_12 : χ 48 ≠ χ 12 := by
    intro h48_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 8
      rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_12, ← h8_eq_12]
    · show χ 8 = χ (8 + 12)
      rw [show (8 + 12 : ℕ) = 20 by decide, h8_eq_12, ← h20_eq_12]
  -- (48, 5, 17): χ(48) ≠ C.
  have h48_ne_5 : χ 48 ≠ χ 5 := by
    intro h48_eq_5
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 12) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 12) = χ 5
      rw [show (4 * 12 : ℕ) = 48 by decide]; exact h48_eq_5
    · show χ 5 = χ (5 + 12)
      rw [show (5 + 12 : ℕ) = 17 by decide, ← h17_eq_5]
  have h48_eq_9 : χ 48 = χ 9 := by omega
  -- (4, 20, 21): χ(21) ≠ B.
  have h21_ne_12 : χ 21 ≠ χ 12 := by
    intro h21_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 20
      rw [show (4 * 1 : ℕ) = 4 by decide, h4_eq_12, ← h20_eq_12]
    · show χ 20 = χ (20 + 1)
      rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_12, h21_eq_12]
  -- (48, 9, 21): χ(21) ≠ A.
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
  have h21_eq_5 : χ 21 = χ 5 := by omega
  -- (64, 4, 20): χ(64) ≠ B.
  have h64_ne_12 : χ 64 ≠ χ 12 := by
    intro h64_eq_12
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 4
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_12, ← h4_eq_12]
    · show χ 4 = χ (4 + 16)
      rw [show (4 + 16 : ℕ) = 20 by decide, h4_eq_12, ← h20_eq_12]
  -- (64, 16, 32): χ(64) ≠ A.
  have h64_ne_9 : χ 64 ≠ χ 9 := by
    intro h64_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 16) (y := 16) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 16) = χ 16
      rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h9_eq_16]
    · show χ 16 = χ (16 + 16)
      rw [show (16 + 16 : ℕ) = 32 by decide, ← h9_eq_16, ← h32_eq_9]
  have h64_eq_5 : χ 64 = χ 5 := by omega
  ------------------------------------------------------------
  -- TERMINAL (64, 5, 21): all C.
  ------------------------------------------------------------
  have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 5) (by omega) (by omega) (by omega) (by omega)
  apply hRadoT
  refine ⟨?_, ?_⟩
  · show χ (4 * 16) = χ 5
    rw [show (4 * 16 : ℕ) = 64 by decide]; exact h64_eq_5
  · show χ 5 = χ (5 + 16)
    rw [show (5 + 16 : ℕ) = 21 by decide, ← h21_eq_5]

/-! ### §149. R308 — Case B sub-case (χ4=C, χ8=C) closure — FINAL Case B sub-case.

  **Setup.** Under `h9_eq_16 + h4_ne_9 + h4_ne_12 + h8_ne_9 + h8_ne_12 + h4_eq_8`,
  derive False at n ≥ 64. Last open Case B sub-case.

  Notation: A := χ(9) = χ(16); B := χ(12); C := χ(4) = χ(8).

  **Universal forced**: χ(5) = B.

  **Branch I (χ(10) = B)**: short cascade.
  - χ(13) = C via (12, 10, 13) [≠B] + (16, 9, 13) [≠A].
  - χ(20) = C via (20, 5, 10) [≠B] + (16, 16, 20) [≠A].
  - Terminal **(20, 8, 13)** all C → MONO!

  **Branch II (χ(10) = A)**: 12-step cascade to no-color-left on χ(64).
  - χ(6) = B, χ(28) = C, χ(15) = A, χ(11) = B, χ(20) = C, χ(13) = B,
    χ(24) = C, χ(32) = A, χ(17) = B, χ(48) = A, χ(21) = B.
  - χ(64): (64, 16, 32) ≠ A + (64, 5, 21) ≠ B + (64, 4, 20) ≠ C → **omega False**.

  Major triples (Branch II):
  - (64, 16, 32): 64 + 64 = 128 = 4·32 ✓
  - (64, 5, 21):  64 + 20 = 84 = 4·21 ✓
  - (64, 4, 20):  64 + 16 = 80 = 4·20 ✓ (all three ≠ exclusions converge to χ(64) no-color-left)
-/

set_option maxHeartbeats 3200000 in
/-- **R308 Case B sub-case (χ4=C, χ8=C) closure**: under h9_eq_16 +
  h4_ne_9 + h4_ne_12 + h8_ne_9 + h8_ne_12 + h4_eq_8, derive False at n ≥ 64.
  FINAL Case B sub-case. -/
theorem bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_third_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16)
    (h4_ne_9 : χ 4 ≠ χ 9)
    (h4_ne_12 : χ 4 ≠ χ 12)
    (h8_ne_9 : χ 8 ≠ χ 9)
    (h8_ne_12 : χ 8 ≠ χ 12)
    (h4_eq_8 : χ 4 = χ 8) :
    False := by
  -- Setup hχ values.
  have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
  have hχ5 : χ 5 < 3 := hχk 5 (by omega) (by omega)
  have hχ6 : χ 6 < 3 := hχk 6 (by omega) (by omega)
  have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
  have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
  have hχ10 : χ 10 < 3 := hχk 10 (by omega) (by omega)
  have hχ11 : χ 11 < 3 := hχk 11 (by omega) (by omega)
  have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
  have hχ13 : χ 13 < 3 := hχk 13 (by omega) (by omega)
  have hχ15 : χ 15 < 3 := hχk 15 (by omega) (by omega)
  have hχ16 : χ 16 < 3 := hχk 16 (by omega) (by omega)
  have hχ17 : χ 17 < 3 := hχk 17 (by omega) (by omega)
  have hχ20 : χ 20 < 3 := hχk 20 (by omega) (by omega)
  have hχ21 : χ 21 < 3 := hχk 21 (by omega) (by omega)
  have hχ24 : χ 24 < 3 := hχk 24 (by omega) (by omega)
  have hχ28 : χ 28 < 3 := hχk 28 (by omega) (by omega)
  have hχ32 : χ 32 < 3 := hχk 32 (by omega) (by omega)
  have hχ48 : χ 48 < 3 := hχk 48 (by omega) (by omega)
  have hχ64 : χ 64 < 3 := hχk 64 (by omega) (by omega)
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  ------------------------------------------------------------
  -- UNIVERSAL: χ(5) = B.
  ------------------------------------------------------------
  have h5_ne_9 : χ 5 ≠ χ 9 := by
    intro h5_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 4) (y := 5) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 4) = χ 5
      rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h5_eq_9]
    · show χ 5 = χ (5 + 4)
      rw [show (5 + 4 : ℕ) = 9 by decide]; exact h5_eq_9
  have h5_ne_4 : χ 5 ≠ χ 4 := by
    intro h5_eq_4
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 1) (y := 4) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 1) = χ 4
      rw [show (4 * 1 : ℕ) = 4 by decide]
    · show χ 4 = χ (4 + 1)
      rw [show (4 + 1 : ℕ) = 5 by decide, h5_eq_4]
  have h5_eq_12 : χ 5 = χ 12 := by omega
  ------------------------------------------------------------
  -- BRANCH on χ(10) ∈ {A, B} (χ(10) ≠ C from (8, 8, 10) self-loop).
  ------------------------------------------------------------
  have h10_ne_8 : χ 10 ≠ χ 8 := by
    intro h10_eq_8
    have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 2) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (4 * 2) = χ 8
      rw [show (4 * 2 : ℕ) = 8 by decide]
    · show χ 8 = χ (8 + 2)
      rw [show (8 + 2 : ℕ) = 10 by decide]; exact h10_eq_8.symm
  have h10_ne_4 : χ 10 ≠ χ 4 := fun h => h10_ne_8 (h.trans h4_eq_8)
  by_cases h10_eq_12 : χ 10 = χ 12
  · ----------------------------------------------------------
    -- BRANCH I: χ(10) = B. Short cascade to (20, 8, 13) MONO C.
    ----------------------------------------------------------
    have h13_ne_12 : χ 13 ≠ χ 12 := by
      intro h13_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 3) (y := 10) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 3) = χ 10
        rw [show (4 * 3 : ℕ) = 12 by decide, ← h10_eq_12]
      · show χ 10 = χ (10 + 3)
        rw [show (10 + 3 : ℕ) = 13 by decide, h10_eq_12, h13_eq_12]
    have h13_ne_9 : χ 13 ≠ χ 9 := by
      intro h13_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 9
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
      · show χ 9 = χ (9 + 4)
        rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
    have h13_eq_4 : χ 13 = χ 4 := by omega
    have h20_ne_12 : χ 20 ≠ χ 12 := by
      intro h20_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 5
        rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 5)
        rw [show (5 + 5 : ℕ) = 10 by decide, h5_eq_12, ← h10_eq_12]
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
    have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h20_ne_16 (h.trans h9_eq_16)
    have h20_eq_4 : χ 20 = χ 4 := by omega
    -- TERMINAL (20, 8, 13): all C.
    have hRadoT := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
      (d := 5) (y := 8) (by omega) (by omega) (by omega) (by omega)
    apply hRadoT
    refine ⟨?_, ?_⟩
    · show χ (4 * 5) = χ 8
      rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_4, ← h4_eq_8]
    · show χ 8 = χ (8 + 5)
      rw [show (8 + 5 : ℕ) = 13 by decide, ← h4_eq_8, ← h13_eq_4]
  · ----------------------------------------------------------
    -- BRANCH II: χ(10) ≠ B. Combined with χ(10) ≠ C → χ(10) = A.
    ----------------------------------------------------------
    have h10_eq_9 : χ 10 = χ 9 := by omega
    -- Step: χ(6) = B (= χ12).
    have h6_ne_4 : χ 6 ≠ χ 4 := by
      intro h6_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 2) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 2) = χ 4
        rw [show (4 * 2 : ℕ) = 8 by decide]; exact h4_eq_8.symm
      · show χ 4 = χ (4 + 2)
        rw [show (4 + 2 : ℕ) = 6 by decide]; exact h6_eq_4.symm
    have h6_ne_16 : χ 6 ≠ χ 16 := by
      intro h6_eq_16
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 6) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 6
        rw [show (4 * 4 : ℕ) = 16 by decide, ← h6_eq_16]
      · show χ 6 = χ (6 + 4)
        rw [show (6 + 4 : ℕ) = 10 by decide, h6_eq_16, ← h9_eq_16, ← h10_eq_9]
    have h6_ne_9 : χ 6 ≠ χ 9 := fun h => h6_ne_16 (h.trans h9_eq_16)
    have h6_eq_12 : χ 6 = χ 12 := by omega
    -- Step: χ(28) = C (= χ4).
    have h28_ne_12 : χ 28 ≠ χ 12 := by
      intro h28_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 5
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 7)
        rw [show (5 + 7 : ℕ) = 12 by decide]; exact h5_eq_12
    have h28_ne_9 : χ 28 ≠ χ 9 := by
      intro h28_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 9
        rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_9
      · show χ 9 = χ (9 + 7)
        rw [show (9 + 7 : ℕ) = 16 by decide]; exact h9_eq_16
    have h28_eq_4 : χ 28 = χ 4 := by omega
    -- Step: χ(15) = A (= χ9).
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
    have h15_ne_4 : χ 15 ≠ χ 4 := by
      intro h15_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 8
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_4, ← h4_eq_8]
      · show χ 8 = χ (8 + 7)
        rw [show (8 + 7 : ℕ) = 15 by decide, ← h4_eq_8, ← h15_eq_4]
    have h15_eq_9 : χ 15 = χ 9 := by omega
    -- Step: χ(11) = B (= χ12).
    have h11_ne_4 : χ 11 ≠ χ 4 := by
      intro h11_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 4
        rw [show (4 * 7 : ℕ) = 28 by decide]; exact h28_eq_4
      · show χ 4 = χ (4 + 7)
        rw [show (4 + 7 : ℕ) = 11 by decide]; exact h11_eq_4.symm
    have h11_ne_9 : χ 11 ≠ χ 9 := by
      intro h11_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 11) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 11
        rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16, ← h11_eq_9]
      · show χ 11 = χ (11 + 4)
        rw [show (11 + 4 : ℕ) = 15 by decide, h11_eq_9, ← h15_eq_9]
    have h11_eq_12 : χ 11 = χ 12 := by omega
    -- Step: χ(20) = C (= χ4).
    have h20_ne_12 : χ 20 ≠ χ 12 := by
      intro h20_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 6) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 6
        rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_12, ← h6_eq_12]
      · show χ 6 = χ (6 + 5)
        rw [show (6 + 5 : ℕ) = 11 by decide, h6_eq_12, ← h11_eq_12]
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
    have h20_ne_9 : χ 20 ≠ χ 9 := fun h => h20_ne_16 (h.trans h9_eq_16)
    have h20_eq_4 : χ 20 = χ 4 := by omega
    -- Step: χ(13) = B (= χ12).
    have h13_ne_4 : χ 13 ≠ χ 4 := by
      intro h13_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 5) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 5) = χ 8
        rw [show (4 * 5 : ℕ) = 20 by decide, h20_eq_4, ← h4_eq_8]
      · show χ 8 = χ (8 + 5)
        rw [show (8 + 5 : ℕ) = 13 by decide, ← h4_eq_8, h13_eq_4]
    have h13_ne_9 : χ 13 ≠ χ 9 := by
      intro h13_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 9
        rw [show (4 * 4 : ℕ) = 16 by decide]; exact h9_eq_16.symm
      · show χ 9 = χ (9 + 4)
        rw [show (9 + 4 : ℕ) = 13 by decide, h13_eq_9]
    have h13_eq_12 : χ 13 = χ 12 := by omega
    -- Step: χ(24) = C (= χ4).
    have h24_ne_12 : χ 24 ≠ χ 12 := by
      intro h24_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 6) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 6) = χ 6
        rw [show (4 * 6 : ℕ) = 24 by decide, h24_eq_12, ← h6_eq_12]
      · show χ 6 = χ (6 + 6)
        rw [show (6 + 6 : ℕ) = 12 by decide]; exact h6_eq_12
    have h24_ne_9 : χ 24 ≠ χ 9 := by
      intro h24_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 6) = χ 9
        rw [show (4 * 6 : ℕ) = 24 by decide]; exact h24_eq_9
      · show χ 9 = χ (9 + 6)
        rw [show (9 + 6 : ℕ) = 15 by decide]; exact h15_eq_9.symm
    have h24_eq_4 : χ 24 = χ 4 := by omega
    -- Step: χ(32) = A (= χ9).
    have h32_ne_12 : χ 32 ≠ χ 12 := by
      intro h32_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 5
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 8)
        rw [show (5 + 8 : ℕ) = 13 by decide, h5_eq_12, ← h13_eq_12]
    have h32_ne_4 : χ 32 ≠ χ 4 := by
      intro h32_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 24) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 24
        rw [show (4 * 8 : ℕ) = 32 by decide, h32_eq_4, ← h24_eq_4]
      · show χ 24 = χ (24 + 8)
        rw [show (24 + 8 : ℕ) = 32 by decide, h24_eq_4, ← h32_eq_4]
    have h32_eq_9 : χ 32 = χ 9 := by omega
    -- Step: χ(17) = B (= χ12).
    have h17_ne_9 : χ 17 ≠ χ 9 := by
      intro h17_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 8) = χ 9
        rw [show (4 * 8 : ℕ) = 32 by decide]; exact h32_eq_9
      · show χ 9 = χ (9 + 8)
        rw [show (9 + 8 : ℕ) = 17 by decide, h17_eq_9]
    have h17_ne_4 : χ 17 ≠ χ 4 := by
      intro h17_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 7) (y := 17) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 7) = χ 17
        rw [show (4 * 7 : ℕ) = 28 by decide, h28_eq_4, ← h17_eq_4]
      · show χ 17 = χ (17 + 7)
        rw [show (17 + 7 : ℕ) = 24 by decide, h17_eq_4, ← h24_eq_4]
    have h17_eq_12 : χ 17 = χ 12 := by omega
    -- Step: χ(48) = A (= χ9).
    have h48_ne_4 : χ 48 ≠ χ 4 := by
      intro h48_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 12) (y := 8) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 12) = χ 8
        rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_4, ← h4_eq_8]
      · show χ 8 = χ (8 + 12)
        rw [show (8 + 12 : ℕ) = 20 by decide, ← h4_eq_8, ← h20_eq_4]
    have h48_ne_12 : χ 48 ≠ χ 12 := by
      intro h48_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 12) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 12) = χ 5
        rw [show (4 * 12 : ℕ) = 48 by decide, h48_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 12)
        rw [show (5 + 12 : ℕ) = 17 by decide, h5_eq_12, ← h17_eq_12]
    have h48_eq_9 : χ 48 = χ 9 := by omega
    -- Step: χ(21) = B (= χ12).
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
    have h21_ne_4 : χ 21 ≠ χ 4 := by
      intro h21_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 1) (y := 20) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 1) = χ 20
        rw [show (4 * 1 : ℕ) = 4 by decide, ← h20_eq_4]
      · show χ 20 = χ (20 + 1)
        rw [show (20 + 1 : ℕ) = 21 by decide, h20_eq_4, h21_eq_4]
    have h21_eq_12 : χ 21 = χ 12 := by omega
    ----------------------------------------------------------
    -- TERMINAL: no-color-left on χ(64).
    ----------------------------------------------------------
    have h64_ne_9 : χ 64 ≠ χ 9 := by
      intro h64_eq_9
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 16) (y := 16) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 16) = χ 16
        rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_9, ← h9_eq_16]
      · show χ 16 = χ (16 + 16)
        rw [show (16 + 16 : ℕ) = 32 by decide, ← h9_eq_16, ← h32_eq_9]
    have h64_ne_12 : χ 64 ≠ χ 12 := by
      intro h64_eq_12
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 16) (y := 5) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 16) = χ 5
        rw [show (4 * 16 : ℕ) = 64 by decide, h64_eq_12, ← h5_eq_12]
      · show χ 5 = χ (5 + 16)
        rw [show (5 + 16 : ℕ) = 21 by decide, h5_eq_12, ← h21_eq_12]
    have h64_ne_4 : χ 64 ≠ χ 4 := by
      intro h64_eq_4
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 16) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 16) = χ 4
        rw [show (4 * 16 : ℕ) = 64 by decide]; exact h64_eq_4
      · show χ 4 = χ (4 + 16)
        rw [show (4 + 16 : ℕ) = 20 by decide]; exact h20_eq_4.symm
    -- No-color-left: χ(64) < 3, ≠ χ4, ≠ χ12, ≠ χ9. {A, B, C} = {0, 1, 2}. omega.
    omega

/-! ### §150. R309 — Case B dispatcher.

  **Setup.** Under `h9_eq_16 : χ(9) = χ(16)` + mono-free at n ≥ 64 + 3-coloring,
  derive False by 3×3 case split on (χ(4), χ(8)) ∈ {A, B, C}², dispatching to
  R301-R308 closure theorems.

  Dispatch ledger:
  - (A, A): direct (16, 4, 8) mono A.
  - (A, B): R301.   - (A, C): R303.
  - (B, A): R302.   - (B, B): R307.   - (B, C): R304.
  - (C, A): R306.   - (C, B): R305.   - (C, C): R308.

  Distinctness `χ(9) ≠ χ(12)` derived from `bAdicEquation_4_chi_9_ne_chi_12_in_monoFree`.
  Third-color `h4_eq_8` for (C, C) derived via omega trichotomy.
-/

set_option maxHeartbeats 800000 in
/-- **R309 Case B dispatcher**: under `h9_eq_16` + mono-free at n ≥ 64,
  derive False by 3×3 dispatch on (χ(4), χ(8)). -/
theorem bAdicEquation_4_chi_9_eq_chi_16_forces_False
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ)
    (h9_eq_16 : χ 9 = χ 16) :
    False := by
  -- Auto-distinctness.
  have h9_ne_12 : χ 9 ≠ χ 12 :=
    bAdicEquation_4_chi_9_ne_chi_12_in_monoFree χ (by omega) hNoMono
  -- by_cases on χ4.
  by_cases h4_eq_9 : χ 4 = χ 9
  · -- χ4 = A.
    by_cases h8_eq_9 : χ 8 = χ 9
    · ----------------------------------------------------------
      -- CASE (A, A): direct (16, 4, 8) MONO A.
      ----------------------------------------------------------
      have hRado := bAdicEquation_general_rado_constraint (b := 4) (n := n) (by omega) χ hNoMono
        (d := 4) (y := 4) (by omega) (by omega) (by omega) (by omega)
      apply hRado
      refine ⟨?_, ?_⟩
      · show χ (4 * 4) = χ 4
        rw [show (4 * 4 : ℕ) = 16 by decide, ← h9_eq_16]; exact h4_eq_9.symm
      · show χ 4 = χ (4 + 4)
        rw [show (4 + 4 : ℕ) = 8 by decide, h4_eq_9, ← h8_eq_9]
    · by_cases h8_eq_12 : χ 8 = χ 12
      · ----------------------------------------------------------
        -- CASE (A, B): R301.
        ----------------------------------------------------------
        exact bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_eq_12_forces_False χ h64 hχk hNoMono
          h9_eq_16 h4_eq_9 h8_eq_12
      · ----------------------------------------------------------
        -- CASE (A, C): R303.
        ----------------------------------------------------------
        exact bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_third_forces_False χ h64 hχk hNoMono
          h9_eq_16 h4_eq_9 h8_eq_9 h8_eq_12
  · -- χ4 ≠ A.
    by_cases h4_eq_12 : χ 4 = χ 12
    · -- χ4 = B.
      by_cases h8_eq_9 : χ 8 = χ 9
      · ----------------------------------------------------------
        -- CASE (B, A): R302.
        ----------------------------------------------------------
        exact bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_9_forces_False χ h64 hχk hNoMono
          h9_eq_16 h4_eq_12 h8_eq_9
      · by_cases h8_eq_12 : χ 8 = χ 12
        · ----------------------------------------------------------
          -- CASE (B, B): R307.
          ----------------------------------------------------------
          exact bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_12_forces_False χ h64 hχk hNoMono
            h9_eq_16 h4_eq_12 h8_eq_12
        · ----------------------------------------------------------
          -- CASE (B, C): R304.
          ----------------------------------------------------------
          exact bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_third_forces_False χ h64 hχk hNoMono
            h9_eq_16 h4_eq_12 h8_eq_9 h8_eq_12
    · -- χ4 = C (third).
      by_cases h8_eq_9 : χ 8 = χ 9
      · ----------------------------------------------------------
        -- CASE (C, A): R306.
        ----------------------------------------------------------
        exact bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_9_forces_False χ h64 hχk hNoMono
          h9_eq_16 h4_eq_9 h4_eq_12 h8_eq_9
      · by_cases h8_eq_12 : χ 8 = χ 12
        · ----------------------------------------------------------
          -- CASE (C, B): R305.
          ----------------------------------------------------------
          exact bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_12_forces_False χ h64 hχk hNoMono
            h9_eq_16 h4_eq_9 h4_eq_12 h8_eq_12
        · ----------------------------------------------------------
          -- CASE (C, C): R308. Need h4_eq_8 from omega trichotomy.
          ----------------------------------------------------------
          have hχ4 : χ 4 < 3 := hχk 4 (by omega) (by omega)
          have hχ8 : χ 8 < 3 := hχk 8 (by omega) (by omega)
          have hχ9 : χ 9 < 3 := hχk 9 (by omega) (by omega)
          have hχ12 : χ 12 < 3 := hχk 12 (by omega) (by omega)
          have h4_eq_8 : χ 4 = χ 8 := by omega
          exact bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_third_forces_False χ h64 hχk hNoMono
            h9_eq_16 h4_eq_9 h4_eq_12 h8_eq_9 h8_eq_12 h4_eq_8

/-! ### §151. R310 — FINAL ASSEMBLY: `bAdicEquation_4_no_mono_free_at_64`.

  **The main upper-bound theorem for R₃(4) ≤ 64.**

  Under mono-free 3-coloring at n ≥ 64, derive False by 2-way branch:
  - Case `χ(9) = χ(16)`: apply R309 Case B dispatcher.
  - Case `χ(9) ≠ χ(16)`: apply R300 partial final (routes through R299
    all-distinct dispatcher via auto-derived `χ(9) ≠ χ(12)` and
    `χ(12) ≠ χ(16)`).

  Equivalent to the b=3 analogue `bAdicEquation_3_no_mono_free_at_27`.
  Once proved, R311 produces `IsRadoNumber (bAdicEquation 4) 3 (4^3)`
  via the R254 schema `isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow`.
-/

/-- **R310 FINAL: there is no mono-free 3-coloring of [1, n] (n ≥ 64) for
  bAdicEquation 4**. Equivalent to R₃(4) ≤ 64 directly. Kernel-pure. -/
theorem bAdicEquation_4_no_mono_free_at_64
    {n : ℕ} (χ : ℕ → ℕ) (h64 : 64 ≤ n)
    (hχk : IsKColoring n 3 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 4) n χ) :
    False := by
  by_cases h9_eq_16 : χ 9 = χ 16
  · -- Case B branch.
    exact bAdicEquation_4_chi_9_eq_chi_16_forces_False χ h64 hχk hNoMono h9_eq_16
  · -- All-distinct branch (h9_ne_16).
    exact bAdicEquation_4_no_mono_free_at_64_when_chi9_ne_chi16 χ h64 hχk hNoMono h9_eq_16

/-! ### §152. R311 — MAIN THEOREM: `R₃(4) = 4³` via the schema.

  Applies the general schema `isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow`
  at (b, k) = (4, 3) using R310 `bAdicEquation_4_no_mono_free_at_64` as the
  no-mono-free obligation. Produces `IsRadoNumber (bAdicEquation 4) 3 (4^3)`
  kernel-pure.

  Combined with the lower bound (always available via the valuation argument),
  this gives **R₃(4) = 4³ = 64**.
-/

/-- **R311 MAIN: `IsRadoNumber (bAdicEquation 4) 3 (4^3)` kernel-pure**.
  Mirrors `thm_k3b3_via_general_no_mono_free_schema` for (b, k) = (4, 3).
  Equivalent to R₃(4) = 64. -/
theorem thm_k3b4_via_general_no_mono_free_schema :
    IsRadoNumber (bAdicEquation 4) 3 (4^3) :=
  isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow (b := 4) (k := 3)
    (by omega) (by omega)
    (fun χ hχk hNoMono => by
      have h64 : (4:ℕ)^3 = 64 := by decide
      rw [h64] at hχk hNoMono
      exact bAdicEquation_4_no_mono_free_at_64 χ (le_refl 64) hχk hNoMono)

/-- **R311 PROJECT: `RadoNumbers.IsRadoNumber 4 3 64` kernel-pure**.
  Project-namespace version via `isRadoNumber_bAdicEquation_iff_project`.
  Mirrors `thm_k3b3_project_via_general_no_mono_free_schema`. -/
theorem thm_k3b4_project_via_general_no_mono_free_schema :
    RadoNumbers.IsRadoNumber 4 3 64 := by
  have h := thm_k3b4_via_general_no_mono_free_schema
  have h64 : (4:ℕ)^3 = 64 := by decide
  rw [h64] at h
  exact (isRadoNumber_bAdicEquation_iff_project 4 3 64 (by omega)).mp h

/-! ### §153. R313 — R₄(3) = 81 setup: scale-3 three-color subcoloring bridge.

  **Strategic context**: After R₃(4) = 64 (R311), next instance toward
  Threshold Conjecture is R₄(3) = 3^4 = 81, testing **k-recursion direction**
  at boundary `k = 4 = 2(b-1)` with `b = 3`.

  **Recursive compression pattern** (mirrors R₃(4) = 64):
  1. 4-coloring on [1, 81].
  2. Scale-3 layer `d ↦ χ(3d)` for `d ≤ 27` compressed to 3 colors.
  3. Apply `R₃(3) = 27` (existing kernel-pure `thm_k3b3_via_general_no_mono_free_schema`).
  4. Lift monochromatic solution back to [1, 81] via scale-3.

  This bridge is the b=3, k=4 analog of R254's
  `scale4_two_color_subcoloring_lifts_mono_solution`.

  **Definition of compression**: given three distinct target colors `cA, cB, cC`
  and hypothesis `∀ d ∈ [1, 27], χ(3d) ∈ {cA, cB, cC}`, the layer is effectively
  3-colored. We construct ψ : ℕ → {0, 1, 2} by re-mapping χ(3d) to its bucket
  index, then apply `R₃(3) = 27` to ψ to get a mono ψ-solution, then lift to
  a mono χ-solution at scale 3.
-/

/-- **R313 scale-3 three-color subcoloring bridge**: under mono-free 4-coloring
  `χ` of [1, n] (n ≥ 81), if there exist three distinct colors `cA, cB, cC`
  such that the multiples-of-3 layer `d ↦ χ(3d)` for `d ∈ [1, 27]` lies in
  `{cA, cB, cC}`, then False.

  Kernel-pure. Reusable bridge for any 4-color → 3-color compression at scale 3
  with target threshold n ≥ 81. b=3 analog of R254. -/
theorem scale3_three_color_subcoloring_lifts_mono_solution
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (cA cB cC : ℕ)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    (hLayer : ∀ d, 1 ≤ d → d ≤ 27 → χ (3 * d) = cA ∨ χ (3 * d) = cB ∨ χ (3 * d) = cC) :
    False := by
  -- Define ψ via re-mapping χ(3d) into {0, 1, 2}.
  let ψ : ℕ → ℕ := fun d =>
    if χ (3 * d) = cA then 0
    else if χ (3 * d) = cB then 1
    else 2
  -- ψ is a 3-coloring of [1, 27].
  have hψk : IsKColoring 27 3 ψ := by
    intro d _ _
    show (if χ (3 * d) = cA then 0 else if χ (3 * d) = cB then 1 else 2) < 3
    split_ifs <;> omega
  -- R₃(3) = 27 yields IsKPartitionRegularAt (bAdicEquation 3) 3 27.
  have hThmK3 := thm_k3b3_via_general_no_mono_free_schema
  have h27 : (3 : ℕ) ^ 3 = 27 := by decide
  rw [h27] at hThmK3
  have hPR : IsKPartitionRegularAt (bAdicEquation 3) 3 27 := hThmK3.1
  -- ψ has a mono solution at level 27.
  obtain ⟨f, hbound, hpos, hcolor⟩ := hPR ψ hψk
  -- Lift to χ at scale 3: positions (3·f 0, 3·f 1, 3·f 2) at level 81 ≤ n.
  apply hNoMono
  refine ⟨fun i => 3 * f i, ?_, ?_, ?_⟩
  · -- All positions ≤ n.
    intro i hi
    have hfi : f i ≤ 27 := hbound i hi
    calc 3 * f i ≤ 3 * 27 := Nat.mul_le_mul_left 3 hfi
      _ = 81 := by decide
      _ ≤ n := h81
  · -- Positive solution of bAdicEquation 3.
    exact LinearEquation.isPositiveSolution_const_mul (bAdicEquation 3) (by omega) f hpos
  · -- Mono color: χ(3·f i) = χ(3·f j) via hLayer + ψ-mono.
    intro i j hi hj
    show χ (3 * f i) = χ (3 * f j)
    have hψij : ψ (f i) = ψ (f j) := hcolor i j hi hj
    have hfi_pos : 1 ≤ f i := hpos.1 i hi
    have hfj_pos : 1 ≤ f j := hpos.1 j hj
    have hfi : f i ≤ 27 := hbound i hi
    have hfj : f j ≤ 27 := hbound j hj
    have hL_i := hLayer (f i) hfi_pos hfi
    have hL_j := hLayer (f j) hfj_pos hfj
    -- 3×3 case analysis on (cA, cB, cC) buckets.
    rcases hL_i with hi_A | hi_B | hi_C <;> rcases hL_j with hj_A | hj_B | hj_C
    · -- (A, A): both = cA.
      rw [hi_A, hj_A]
    · -- (A, B): ψ(f i) = 0, ψ(f j) = 1. Contradicts ψij.
      exfalso
      have hψi : ψ (f i) = 0 := if_pos hi_A
      have hj_ne_A : χ (3 * f j) ≠ cA := by rw [hj_B]; exact hAB.symm
      have hψj : ψ (f j) = 1 := by
        show (if χ (3 * f j) = cA then 0 else if χ (3 * f j) = cB then 1 else 2) = 1
        rw [if_neg hj_ne_A, if_pos hj_B]
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (A, C): ψ(f i) = 0, ψ(f j) = 2.
      exfalso
      have hψi : ψ (f i) = 0 := if_pos hi_A
      have hj_ne_A : χ (3 * f j) ≠ cA := by rw [hj_C]; exact hAC.symm
      have hj_ne_B : χ (3 * f j) ≠ cB := by rw [hj_C]; exact hBC.symm
      have hψj : ψ (f j) = 2 := by
        show (if χ (3 * f j) = cA then 0 else if χ (3 * f j) = cB then 1 else 2) = 2
        rw [if_neg hj_ne_A, if_neg hj_ne_B]
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (B, A): ψ(f i) = 1, ψ(f j) = 0.
      exfalso
      have hi_ne_A : χ (3 * f i) ≠ cA := by rw [hi_B]; exact hAB.symm
      have hψi : ψ (f i) = 1 := by
        show (if χ (3 * f i) = cA then 0 else if χ (3 * f i) = cB then 1 else 2) = 1
        rw [if_neg hi_ne_A, if_pos hi_B]
      have hψj : ψ (f j) = 0 := if_pos hj_A
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (B, B): both = cB.
      rw [hi_B, hj_B]
    · -- (B, C): ψ(f i) = 1, ψ(f j) = 2.
      exfalso
      have hi_ne_A : χ (3 * f i) ≠ cA := by rw [hi_B]; exact hAB.symm
      have hψi : ψ (f i) = 1 := by
        show (if χ (3 * f i) = cA then 0 else if χ (3 * f i) = cB then 1 else 2) = 1
        rw [if_neg hi_ne_A, if_pos hi_B]
      have hj_ne_A : χ (3 * f j) ≠ cA := by rw [hj_C]; exact hAC.symm
      have hj_ne_B : χ (3 * f j) ≠ cB := by rw [hj_C]; exact hBC.symm
      have hψj : ψ (f j) = 2 := by
        show (if χ (3 * f j) = cA then 0 else if χ (3 * f j) = cB then 1 else 2) = 2
        rw [if_neg hj_ne_A, if_neg hj_ne_B]
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (C, A): ψ(f i) = 2, ψ(f j) = 0.
      exfalso
      have hi_ne_A : χ (3 * f i) ≠ cA := by rw [hi_C]; exact hAC.symm
      have hi_ne_B : χ (3 * f i) ≠ cB := by rw [hi_C]; exact hBC.symm
      have hψi : ψ (f i) = 2 := by
        show (if χ (3 * f i) = cA then 0 else if χ (3 * f i) = cB then 1 else 2) = 2
        rw [if_neg hi_ne_A, if_neg hi_ne_B]
      have hψj : ψ (f j) = 0 := if_pos hj_A
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (C, B): ψ(f i) = 2, ψ(f j) = 1.
      exfalso
      have hi_ne_A : χ (3 * f i) ≠ cA := by rw [hi_C]; exact hAC.symm
      have hi_ne_B : χ (3 * f i) ≠ cB := by rw [hi_C]; exact hBC.symm
      have hψi : ψ (f i) = 2 := by
        show (if χ (3 * f i) = cA then 0 else if χ (3 * f i) = cB then 1 else 2) = 2
        rw [if_neg hi_ne_A, if_neg hi_ne_B]
      have hj_ne_A : χ (3 * f j) ≠ cA := by rw [hj_B]; exact hAB.symm
      have hψj : ψ (f j) = 1 := by
        show (if χ (3 * f j) = cA then 0 else if χ (3 * f j) = cB then 1 else 2) = 1
        rw [if_neg hj_ne_A, if_pos hj_B]
      rw [hψi, hψj] at hψij; exact absurd hψij (by norm_num)
    · -- (C, C): both = cC.
      rw [hi_C, hj_C]

/-! ### §154. R314 — R₄(3) = 81 power-anchor prefix.

  Basic self-loop inequalities for the b=3 power chain `{3, 9, 27, 81}` and
  immediate neighbors `{2, 4, 6, 12, 18, 36, 54}`. Derived via the generic
  `bAdicEquation_self_loop_chi_diff` (xz family: χ(2m) ≠ χ(3m)) and
  `bAdicEquation_self_loop_xy_chi_diff` (xy family: χ(3m) ≠ χ(4m)).

  These are k-agnostic — they apply to any k-coloring of [1, n] with
  `hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ`.

  Existing reusable lemmas (already in BasicResults):
  - `bAdicEquation_3_chi_6_ne_chi_9` (m=3 xz, n ≥ 9)
  - `bAdicEquation_3_chi_9_ne_chi_12` (m=3 xy, n ≥ 12)
  - `bAdicEquation_3_chi_12_ne_chi_18` (m=6 xz, n ≥ 18)
  - `bAdicEquation_3_chi_12_ne_chi_16` (m=4 xy, n ≥ 16)
  - `bAdicEquation_3_chi_27_ne_chi_18_in_monoFree` (m=9 xz, n ≥ 27)

  New for R₄(3) power chain:
  - `bAdicEquation_3_chi_2_ne_chi_3_in_monoFree` (m=1 xz)
  - `bAdicEquation_3_chi_3_ne_chi_4_in_monoFree` (m=1 xy)
  - `bAdicEquation_3_chi_27_ne_chi_36_in_monoFree` (m=9 xy)
  - `bAdicEquation_3_chi_54_ne_chi_81_in_monoFree` (m=27 xz)
-/

/-- **χ(2) ≠ χ(3)** for mono-free bAdicEquation 3 at n ≥ 3.
  Self-loop xz at m=1: (3, 2, 3) with 3 + 6 = 9 = 3·3. -/
theorem bAdicEquation_3_chi_2_ne_chi_3_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h3 : 3 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 2 ≠ χ 3 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 1) (by omega) (by omega)
  show χ ((3 - 1) * 1) ≠ χ (3 * 1)
  exact h

/-- **χ(3) ≠ χ(4)** for mono-free bAdicEquation 3 at n ≥ 4.
  Self-loop xy at m=1: (3, 3, 4) with 3 + 9 = 12 = 3·4. -/
theorem bAdicEquation_3_chi_3_ne_chi_4_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h4 : 4 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 3 ≠ χ 4 := by
  have h := bAdicEquation_self_loop_xy_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 1) (by omega) (by omega)
  show χ (3 * 1) ≠ χ ((3 + 1) * 1)
  exact h

/-- **χ(27) ≠ χ(36)** for mono-free bAdicEquation 3 at n ≥ 36.
  Self-loop xy at m=9: (27, 27, 36) with 27 + 81 = 108 = 3·36. -/
theorem bAdicEquation_3_chi_27_ne_chi_36_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 27 ≠ χ 36 := by
  have h := bAdicEquation_self_loop_xy_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 9) (by omega) (by omega)
  show χ (3 * 9) ≠ χ ((3 + 1) * 9)
  exact h

/-- **χ(54) ≠ χ(81)** for mono-free bAdicEquation 3 at n ≥ 81.
  Self-loop xz at m=27: (81, 54, 81) with 81 + 162 = 243 = 3·81. -/
theorem bAdicEquation_3_chi_54_ne_chi_81_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 54 ≠ χ 81 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 27) (by omega) (by omega)
  show χ ((3 - 1) * 27) ≠ χ (3 * 27)
  exact h

/-- **χ(18) ≠ χ(27)** for mono-free bAdicEquation 3 at n ≥ 27.
  Self-loop xz at m=9: (27, 18, 27). Symmetric variant of
  `bAdicEquation_3_chi_27_ne_chi_18_in_monoFree` (already in BasicResults). -/
theorem bAdicEquation_3_chi_18_ne_chi_27_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 18 ≠ χ 27 :=
  Ne.symm (bAdicEquation_3_chi_27_ne_chi_18_in_monoFree χ h27 hNoMono)

/-! ### §155. R315 — Begin χ(27) = χ(81) branch for R₄(3) = 81.

  **Setup.** Under `h27_eq_81 : χ(27) = χ(81)` (= A) and mono-free 4-coloring
  at n ≥ 81, force the basic non-A positions in `{18, 36, 54, 72}`.

  Audit showed **no direct single-triple closure** of this branch:
  - (81, 27, 54) would need χ54 = χ27, but self-loop gives χ54 ≠ χ81 = χ27, blocking.
  - The 4-coloring has 3 non-A colors, so {χ18, χ36, χ54, χ72} all ≠ A is consistent.

  **Forced inequalities** (this round):
  - χ(18) ≠ A via (27, 18, 27) self-loop x=z.
  - χ(36) ≠ A via (27, 27, 36) self-loop x=y.
  - χ(54) ≠ A via (81, 54, 81) self-loop x=z + h27_eq_81.
  - χ(72) ≠ A via (27, 72, 81): mono needs χ27 = χ72 AND χ72 = χ81; under h27_eq_81 reduces to χ72 = χ27.

  Universal facts (k-agnostic, not requiring h27_eq_81):
  - χ(36) ≠ χ(54) via (54, 36, 54) self-loop x=z (m=18).
  - χ(54) ≠ χ(72) via (54, 54, 72) self-loop x=y (m=18).
  - χ(48) ≠ χ(72) via (72, 48, 72) self-loop x=z (m=24).

  **Outstanding obstruction**: χ(9) = A is consistent — no direct triple excludes it.
  Full closure requires nested branching on χ(9), χ(3), or layer compression
  via `scale3_three_color_subcoloring_lifts_mono_solution`.
-/

/-- **R315 χ(27) = χ(81) forced prefix**: under h27_eq_81 + mono-free + n ≥ 81,
  force 4 non-A positions: χ(18), χ(36), χ(54), χ(72) ≠ A. -/
theorem bAdicEquation_3_chi_27_eq_chi_81_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81) :
    χ 18 ≠ χ 27 ∧ χ 36 ≠ χ 27 ∧ χ 54 ≠ χ 27 ∧ χ 72 ≠ χ 27 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- χ(18) ≠ χ(27) via (27, 18, 27) self-loop x=z.
    exact bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  · -- χ(36) ≠ χ(27) via (27, 27, 36) self-loop x=y, then Ne.symm.
    exact (bAdicEquation_3_chi_27_ne_chi_36_in_monoFree χ (by omega) hNoMono).symm
  · -- χ(54) ≠ χ(27): from χ(54) ≠ χ(81) (xz self-loop m=27) + h27_eq_81.
    intro h54_eq_27
    exact bAdicEquation_3_chi_54_ne_chi_81_in_monoFree χ h81 hNoMono
      (h54_eq_27.trans h27_eq_81)
  · -- χ(72) ≠ χ(27) via (27, 72, 81): 27 + 3·72 = 243 = 3·81.
    -- Mono needs χ27 = χ72 AND χ72 = χ81 ⟹ both reduce to χ72 = χ27 under h27_eq_81.
    intro h72_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 72) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 9) = χ 72
      rw [show (3 * 9 : ℕ) = 27 by decide]; exact h72_eq_27.symm
    · show χ 72 = χ (72 + 9)
      rw [show (72 + 9 : ℕ) = 81 by decide]
      exact h72_eq_27.trans h27_eq_81

/-! ### §156. R316 — χ(27) = χ(81) branch, sub-case χ(9) = χ(27).

  **Setup.** Three A-anchors `χ(9) = χ(27) = χ(81) = A` (= same color value).
  Under mono-free 4-coloring at n ≥ 81, force more positions to be ≠ A.

  **Forced exclusions** (9 positions ≠ A):
  | Position | Reason |
  |---|---|
  | χ(6) | χ(6) ≠ χ(9) universal + χ9 = A |
  | χ(12) | χ(9) ≠ χ(12) universal + χ9 = A |
  | χ(18) | (27, 18, 27) self-loop (R315) |
  | χ(24) | (9, 24, 27): mono needs χ24 = A; uses h9_eq_27 + h27_eq_81 |
  | χ(30) | (9, 27, 30): mono needs χ30 = A; uses h9_eq_27 |
  | χ(36) | (27, 27, 36) self-loop (R315) |
  | χ(54) | (81, 54, 81) self-loop (R315) |
  | χ(72) | (27, 72, 81) (R315) |
  | χ(78) | (9, 78, 81): mono needs χ78 = A; uses h27_eq_81 (χ9=χ81 via chain) |

  **No direct contradiction found.** χ(3), χ(15), χ(21), χ(33), χ(39), χ(42),
  χ(45), χ(48), χ(51), χ(57), χ(60), χ(63), χ(66), χ(69), χ(75) all unknown
  (could be A or non-A).

  Full closure requires further nested split or layer-compression argument.
  This round delivers Deliverable B (stronger prefix).

  Triples used (b=3):
  - (9, 24, 27):  9 + 72 = 81 = 3·27 ✓ — χ(24) ≠ A.
  - (9, 27, 30):  9 + 81 = 90 = 3·30 ✓ — χ(30) ≠ A.
  - (9, 78, 81):  9 + 234 = 243 = 3·81 ✓ — χ(78) ≠ A.
-/

/-- **R316 χ(27) = χ(81) + χ(9) = χ(27) forced prefix**: under three A-anchors
  `χ(9) = χ(27) = χ(81)`, force 3 additional non-A positions
  beyond R315: χ(24), χ(30), χ(78) ≠ A. -/
theorem bAdicEquation_3_chi_27_eq_chi_81_subcase_chi_9_eq_27_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_eq_27 : χ 9 = χ 27) :
    χ 24 ≠ χ 27 ∧ χ 30 ≠ χ 27 ∧ χ 78 ≠ χ 27 := by
  refine ⟨?_, ?_, ?_⟩
  · -- χ(24) ≠ A via (9, 24, 27): 9 + 72 = 81 = 3·27. Mono needs both conjuncts.
    -- χ(3*3) = χ(9) AND χ(24) = χ(9). Under h9_eq_27, χ9 = χ27, so mono iff χ24 = χ27.
    intro h24_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 24) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 24
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_27]; exact h24_eq_27.symm
    · show χ 24 = χ (24 + 3)
      rw [show (24 + 3 : ℕ) = 27 by decide]; exact h24_eq_27
  · -- χ(30) ≠ A via (9, 27, 30): 9 + 81 = 90 = 3·30. Mono needs χ9 = χ27 AND χ27 = χ30.
    -- Under h9_eq_27 + h30_eq_27, both hold.
    intro h30_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 27) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 27
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h9_eq_27
    · show χ 27 = χ (27 + 3)
      rw [show (27 + 3 : ℕ) = 30 by decide]; exact h30_eq_27.symm
  · -- χ(78) ≠ A via (9, 78, 81): 9 + 234 = 243 = 3·81. Mono needs χ9 = χ78 AND χ78 = χ81.
    -- Under h9_eq_27 + h27_eq_81 + h78_eq_27, all reduce to χ78 = A.
    intro h78_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 78) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 78
      rw [show (3 * 3 : ℕ) = 9 by decide, h9_eq_27]; exact h78_eq_27.symm
    · show χ 78 = χ (78 + 3)
      rw [show (78 + 3 : ℕ) = 81 by decide, h78_eq_27, h27_eq_81]

/-! ### §157. R317 — χ(27) = χ(81) branch, sibling sub-case χ(9) ≠ χ(27).

  **Setup.** Two distinct anchors: A := χ(27) = χ(81), B := χ(9) ≠ A.
  Under mono-free 4-coloring at n ≥ 81, this is the "cleaner" sibling
  of R316's χ(9) = χ(27) sub-case (which has 3 A-anchors).

  **Audit observation**: No direct contradiction via single triple. The
  branch's structure is: 2 anchor colors (A, B) + 2 unknown non-anchor
  colors (C, D). Full closure needs further nested split (recommended
  on χ(18) ∈ {B, C, D}).

  **Strategic significance**: This branch is well-suited for layer
  compression via `scale3_three_color_subcoloring_lifts_mono_solution`
  if a third anchor C can be identified such that the layer
  `{χ(3d) | d ∈ [1, 27]}` ⊆ {A, B, C}. Natural candidates: χ(18) or χ(54).

  **Forced exclusions** (combined R315 + universal):
  | Position | Reason |
  |---|---|
  | χ(18) | ≠ A (R315) |
  | χ(36) | ≠ A (R315) |
  | χ(54) | ≠ A (R315) |
  | χ(72) | ≠ A (R315) |
  | χ(6)  | ≠ B = χ(9) (universal m=3 xz) |
  | χ(12) | ≠ B = χ(9) (universal m=3 xy, Ne.symm) |

  Triples used (all universal or R315-derived):
  - (27, 18, 27), (27, 27, 36), (81, 54, 81), (27, 72, 81): R315.
  - (9, 6, 9): universal m=3 xz.
  - (9, 9, 12): universal m=3 xy.
-/

/-- **R317 χ(27) = χ(81) + χ(9) ≠ χ(27) forced prefix**: under 2 distinct
  anchors A = χ(27) = χ(81), B = χ(9), force 6 positions (R315 + B-exclusions). -/
theorem bAdicEquation_3_chi_27_eq_chi_81_subcase_chi_9_ne_27_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27) :
    χ 18 ≠ χ 27 ∧ χ 36 ≠ χ 27 ∧ χ 54 ≠ χ 27 ∧ χ 72 ≠ χ 27 ∧
    χ 6 ≠ χ 9 ∧ χ 12 ≠ χ 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- χ(18) ≠ A via (27, 18, 27).
    exact bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  · -- χ(36) ≠ A via (27, 27, 36) (Ne.symm).
    exact (bAdicEquation_3_chi_27_ne_chi_36_in_monoFree χ (by omega) hNoMono).symm
  · -- χ(54) ≠ A via (81, 54, 81) + h27_eq_81.
    intro h54_eq_27
    exact bAdicEquation_3_chi_54_ne_chi_81_in_monoFree χ h81 hNoMono
      (h54_eq_27.trans h27_eq_81)
  · -- χ(72) ≠ A via (27, 72, 81).
    intro h72_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 72) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 9) = χ 72
      rw [show (3 * 9 : ℕ) = 27 by decide]; exact h72_eq_27.symm
    · show χ 72 = χ (72 + 9)
      rw [show (72 + 9 : ℕ) = 81 by decide]
      exact h72_eq_27.trans h27_eq_81
  · -- χ(6) ≠ B via (9, 6, 9) self-loop x=z.
    exact bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  · -- χ(12) ≠ B via (9, 9, 12) self-loop x=y, then Ne.symm.
    exact (bAdicEquation_3_chi_9_ne_chi_12 χ (by omega) hNoMono).symm

/-! ### §158. R318 — χ(27) = χ(81) + χ(9) ≠ χ(27), split on χ(18) ∈ {B, ≠B}.

  **Setup.** Two distinct outer anchors: A := χ(27) = χ(81), B := χ(9).
  Split on χ(18) = χ(9) (= B) vs χ(18) ≠ χ(9).

  **Branch I (χ18 = B)** : 2 B-anchors {9, 18}.
  Forced exclusions: χ(6), χ(12), χ(15), χ(21), χ(24) all ≠ B.
  No direct contradiction in one round; B-mono needs 3rd B-anchor.

  **Branch II (χ18 ≠ B)** : 3 distinct anchors {A, B, C := χ18}.
  Bridge-ready for `scale3_three_color_subcoloring_lifts_mono_solution` with
  full layer compression — but layer hLayer still needs cascade.

  Triples used in Branch I:
  - (18, 9, 15): 18 + 27 = 45 = 3·15 ✓ — χ(15) ≠ B (uses h18_eq_9).
  - (9, 18, 21): 9 + 54 = 63 = 3·21 ✓ — χ(21) ≠ B (uses h18_eq_9).
  - (18, 18, 24): 18 + 54 = 72 = 3·24 ✓ — χ(24) ≠ B (self-loop x=y uses h18_eq_9).
-/

/-- **R318 Branch I prefix (χ18 = B)**: under h27_eq_81 + h9_ne_27 + h18_eq_9,
  force χ(6), χ(12), χ(15), χ(21), χ(24) ≠ B plus R315 exclusions. -/
theorem bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_eq9_forces_prefix
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (h18_eq_9 : χ 18 = χ 9) :
    χ 6 ≠ χ 9 ∧ χ 12 ≠ χ 9 ∧ χ 15 ≠ χ 9 ∧ χ 21 ≠ χ 9 ∧ χ 24 ≠ χ 9 ∧
    χ 36 ≠ χ 27 ∧ χ 54 ≠ χ 27 ∧ χ 72 ≠ χ 27 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- χ(6) ≠ B (universal).
    exact bAdicEquation_3_chi_6_ne_chi_9 χ (by omega) hNoMono
  · -- χ(12) ≠ B (universal).
    exact (bAdicEquation_3_chi_9_ne_chi_12 χ (by omega) hNoMono).symm
  · -- χ(15) ≠ B via (18, 9, 15) + h18_eq_9: 18 + 27 = 45 = 3·15.
    -- Mono needs χ18 = χ9 AND χ9 = χ15. χ18 = χ9 by h18_eq_9. So mono iff χ15 = χ9.
    intro h15_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 9) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 9
      rw [show (3 * 6 : ℕ) = 18 by decide]; exact h18_eq_9
    · show χ 9 = χ (9 + 6)
      rw [show (9 + 6 : ℕ) = 15 by decide]; exact h15_eq_9.symm
  · -- χ(21) ≠ B via (9, 18, 21) + h18_eq_9: 9 + 54 = 63 = 3·21.
    intro h21_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 3) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 3) = χ 18
      rw [show (3 * 3 : ℕ) = 9 by decide]; exact h18_eq_9.symm
    · show χ 18 = χ (18 + 3)
      rw [show (18 + 3 : ℕ) = 21 by decide, h18_eq_9, h21_eq_9]
  · -- χ(24) ≠ B via (18, 18, 24) self-loop x=y + h18_eq_9: 18 + 54 = 72 = 3·24.
    intro h24_eq_9
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 6) (y := 18) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 6) = χ 18
      rw [show (3 * 6 : ℕ) = 18 by decide]
    · show χ 18 = χ (18 + 6)
      rw [show (18 + 6 : ℕ) = 24 by decide, h18_eq_9, h24_eq_9]
  · -- χ(36) ≠ A (R315).
    exact (bAdicEquation_3_chi_27_ne_chi_36_in_monoFree χ (by omega) hNoMono).symm
  · -- χ(54) ≠ A (R315).
    intro h54_eq_27
    exact bAdicEquation_3_chi_54_ne_chi_81_in_monoFree χ h81 hNoMono
      (h54_eq_27.trans h27_eq_81)
  · -- χ(72) ≠ A (R315).
    intro h72_eq_27
    have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
      (d := 9) (y := 72) (by omega) (by omega) (by omega) (by omega)
    apply hRado
    refine ⟨?_, ?_⟩
    · show χ (3 * 9) = χ 72
      rw [show (3 * 9 : ℕ) = 27 by decide]; exact h72_eq_27.symm
    · show χ 72 = χ (72 + 9)
      rw [show (72 + 9 : ℕ) = 81 by decide]
      exact h72_eq_27.trans h27_eq_81

/-- **R318 Branch II 3-distinct anchors (χ18 ≠ B)**: under h27_eq_81 + h9_ne_27 +
  h18_ne_9, the three anchors {χ27, χ9, χ18} are pairwise distinct. Sets up
  the bridge `scale3_three_color_subcoloring_lifts_mono_solution` (modulo hLayer). -/
theorem bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_three_anchors
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    χ 27 ≠ χ 9 ∧ χ 27 ≠ χ 18 ∧ χ 9 ≠ χ 18 := by
  refine ⟨h9_ne_27.symm, ?_, h18_ne_9.symm⟩
  -- χ(27) ≠ χ(18) from R314 self-loop xz at m=9.
  exact (bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono).symm

/-! ### §159. R319 — Branch II conditional layer-cascade lemmas.

  Three conditional lemmas as building blocks for classifying χ(36), χ(54), χ(72)
  into the 3-anchor set {A := χ27, B := χ9, C := χ18} from R318 Branch II.

  Each lemma uses a single explicit bAdicEquation 3 triple of the form
  (3·d, y, y+d) and the generic single-coordinate Rado constraint
  `bAdicEquation_general_rado_constraint`.

  - **Lemma 1** (n ≥ 54): triple `(54, 18, 36) = (3·18, 18, 18+18)`.
    Under hNoMono + χ(54) = χ(18), forces χ(36) ≠ χ(18).
  - **Lemma 2** (n ≥ 72): triple `(72, 18, 42) = (3·24, 18, 18+24)`.
    Under hNoMono + χ(72) = χ(18), forces χ(42) ≠ χ(18).
  - **Lemma 3** (n ≥ 72): triple `(72, 9, 33) = (3·24, 9, 9+24)`.
    Under hNoMono + χ(72) = χ(9), forces χ(33) ≠ χ(9).

  These conditional lemmas form the first real layer-cascade infrastructure for
  R₄(3) = 81, propagating high-layer (3·d, d ∈ [10, 27]) anchor equalities
  down to mid-layer (3·d, d ∈ [1, 14]) forced non-equalities.
-/

/-- **R319 Lemma 1**: under `χ(54) = χ(18)` (high-layer anchor C lift to layer 18),
  the triple `(54, 18, 36) = (3·18, 18, 18+18)` forces `χ(36) ≠ χ(18)`. -/
theorem bAdicEquation_3_chi54_eq_chi18_forces_chi36_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18) :
    χ 36 ≠ χ 18 := by
  intro h36_eq_18
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 18
    rw [show (3 * 18 : ℕ) = 54 by decide]; exact h54_eq_18
  · show χ 18 = χ (18 + 18)
    rw [show (18 + 18 : ℕ) = 36 by decide]; exact h36_eq_18.symm

/-- **R319 Lemma 2**: under `χ(72) = χ(18)` (high-layer anchor C lift to layer 18),
  the triple `(72, 18, 42) = (3·24, 18, 18+24)` forces `χ(42) ≠ χ(18)`. -/
theorem bAdicEquation_3_chi72_eq_chi18_forces_chi42_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h72 : 72 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h72_eq_18 : χ 72 = χ 18) :
    χ 42 ≠ χ 18 := by
  intro h42_eq_18
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 24) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 24) = χ 18
    rw [show (3 * 24 : ℕ) = 72 by decide]; exact h72_eq_18
  · show χ 18 = χ (18 + 24)
    rw [show (18 + 24 : ℕ) = 42 by decide]; exact h42_eq_18.symm

/-- **R319 Lemma 3**: under `χ(72) = χ(9)` (high-layer anchor C lift to layer 9),
  the triple `(72, 9, 33) = (3·24, 9, 9+24)` forces `χ(33) ≠ χ(9)`. -/
theorem bAdicEquation_3_chi72_eq_chi9_forces_chi33_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h72 : 72 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h72_eq_9 : χ 72 = χ 9) :
    χ 33 ≠ χ 9 := by
  intro h33_eq_9
  have hRado := bAdicEquation_general_rado_constraint (b := 3) (n := n) (by omega) χ hNoMono
    (d := 24) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 24) = χ 9
    rw [show (3 * 24 : ℕ) = 72 by decide]; exact h72_eq_9
  · show χ 9 = χ (9 + 24)
    rw [show (9 + 24 : ℕ) = 33 by decide]; exact h33_eq_9.symm

/-! ### §160. R320 — Branch II high-layer classifier around χ(54).

  Goal: classify χ(54) in 4-coloring after fixing the 3 anchors {A := χ27, B := χ9,
  C := χ18}. χ(54) has 3 logical options:
  - χ(54) = B (already constrained as χ54 ≠ A via R317 prefix)
  - χ(54) = C
  - χ(54) = D (fourth color)

  Full classification χ(54) ∈ {B, C} is NOT directly provable — the fourth color
  could appear at 54 in principle. Instead R320 delivers:

  1. **Universal self-loop lemma**: χ(36) ≠ χ(54) at n ≥ 54.
     Triple `(54, 36, 54) = (3·18, 2·18, 3·18)`: 54 + 3·36 = 162 = 3·54.
     Instantiation of generic `bAdicEquation_self_loop_chi_diff` at b=3, m=18.

  2. **Fourth-color classifier**: if χ(54) is the fourth color
     (χ54 ≠ B ∧ χ54 ≠ C), then χ(36) ∈ {B, C}.
     Proof uses the pairwise distinctness of {A, B, C, D := χ54} as four colors < 4,
     combined with χ(36) ≠ A (R314) + χ(36) ≠ D (new universal self-loop) +
     χ(36) < 4 (IsKColoring), closed by omega.

  This complements R319 conditional cascade lemmas (χ54 = C and χ72 = C cases)
  and provides the χ54 = D branch handler.
-/

/-- **χ(36) ≠ χ(54)** for mono-free bAdicEquation 3 at n ≥ 54.
  Self-loop xz at m=18: triple `(54, 36, 54)` with 54 + 3·36 = 162 = 3·54.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=18). -/
theorem bAdicEquation_3_chi_36_ne_chi_54_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 36 ≠ χ 54 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 18) (by omega) (by omega)
  show χ ((3 - 1) * 18) ≠ χ (3 * 18)
  exact h

/-- **R320 Branch II fourth-color classifier**: in the Branch II 3-anchor setup
  `{A := χ27 = χ81, B := χ9, C := χ18}` (h27_eq_81 + h9_ne_27 + h18_ne_9),
  if χ(54) is the fourth color (h54_ne_9 + h54_ne_18, with χ54 ≠ A already from
  R315 = `bAdicEquation_3_chi_54_ne_chi_81_in_monoFree` + h27_eq_81), then
  `χ(36) = χ(9) ∨ χ(36) = χ(18)`.

  Mechanism: in a 4-coloring, {A, B, C, D := χ54} pairwise distinct ⟹ {0,1,2,3}.
  χ(36) < 4 and χ(36) ≠ A (R314) and χ(36) ≠ D (R320 universal) ⟹ χ(36) ∈ {B,C}.
  Closed by omega on the 13 collected (in)equality constraints. -/
theorem bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_fourth_forces_chi36_in_9_or_18
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_ne_9 : χ 54 ≠ χ 9)
    (h54_ne_18 : χ 54 ≠ χ 18) :
    χ 36 = χ 9 ∨ χ 36 = χ 18 := by
  -- Anchor pairwise distinctness.
  have hCA : χ 18 ≠ χ 27 :=
    bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  -- D := χ 54 ≠ A := χ 27 via R315 self-loop χ54 ≠ χ81 + h27_eq_81.
  have hD_ne_81 : χ 54 ≠ χ 81 :=
    bAdicEquation_3_chi_54_ne_chi_81_in_monoFree χ h81 hNoMono
  have hDA : χ 54 ≠ χ 27 := fun h => hD_ne_81 (h.trans h27_eq_81)
  -- χ(36) ≠ A := χ 27 via R314 self-loop xy at m=9 (χ27 ≠ χ36).
  have hM_ne_A : χ 36 ≠ χ 27 :=
    (bAdicEquation_3_chi_27_ne_chi_36_in_monoFree χ (by omega) hNoMono).symm
  -- χ(36) ≠ D := χ 54 via R320 universal self-loop xz at m=18.
  have hM_ne_D : χ 36 ≠ χ 54 :=
    bAdicEquation_3_chi_36_ne_chi_54_in_monoFree χ (by omega) hNoMono
  -- All colors < 4 from IsKColoring at positions 9, 18, 27, 36, 54 (all ≤ 81 ≤ n).
  have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
  have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
  have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
  have h36_lt : χ 36 < 4 := hχk 36 (by omega) (by omega)
  have h54_lt : χ 54 < 4 := hχk 54 (by omega) (by omega)
  -- Finite enumeration: {A, B, C, D} = {0,1,2,3} pairwise; χ36 ∈ {A,B,C,D} \ {A,D}.
  omega

/-! ### §161. R321 — Unified Branch II χ(54)/χ(36) dispatcher + χ(48) ≠ χ(72).

  Goal: package R320 four-color classifier as a 3-branch dispatcher: in any
  Branch II (h27_eq_81 + h9_ne_27 + h18_ne_9) coloring of [1, n] with 4 colors,

    (χ54 ∈ {B,C}) ∨ (χ36 ∈ {B,C}),    where B = χ9, C = χ18.

  Proof: by_cases on χ54 = χ9 / χ54 = χ18 (both ℕ-decidable; no Classical needed).
  - If χ54 = B: left ∨ left.
  - If χ54 ≠ B but χ54 = C: left ∨ right.
  - Otherwise χ54 ≠ B ∧ χ54 ≠ C ⟹ R320 fourth-color classifier ⟹ χ36 ∈ {B, C}.

  Second deliverable: universal χ(48) ≠ χ(72) (xz self-loop m=24), companion
  to R320 (A) for the χ(72) high-layer analysis in R322.
-/

/-- **χ(48) ≠ χ(72)** for mono-free bAdicEquation 3 at n ≥ 72.
  Self-loop xz at m=24: triple `(72, 48, 72)` with 72 + 3·48 = 216 = 3·72.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=24).
  Companion to R320 (A) `bAdicEquation_3_chi_36_ne_chi_54_in_monoFree`. -/
theorem bAdicEquation_3_chi_48_ne_chi_72_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h72 : 72 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 48 ≠ χ 72 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 24) (by omega) (by omega)
  show χ ((3 - 1) * 24) ≠ χ (3 * 24)
  exact h

/-- **R321 unified Branch II χ(54)/χ(36) dispatcher**: under R318 Branch II
  3-anchor setup (h27_eq_81 + h9_ne_27 + h18_ne_9) and `IsKColoring n 4 χ`,
  at least one of χ(54), χ(36) already lies in `{B := χ9, C := χ18}`.

  Compression-dispatch invariant: the high-layer pair {54, 36} is partially
  classified into `{B, C}` regardless of which Branch II sub-case holds.

  Proof: 3-way decidable case split on χ(54) vs {χ9, χ18}; the fourth-color
  case delegates to R320 `chi54_fourth_forces_chi36_in_9_or_18`. -/
theorem bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 54 = χ 9 ∨ χ 54 = χ 18) ∨ (χ 36 = χ 9 ∨ χ 36 = χ 18) := by
  by_cases h54_eq_9 : χ 54 = χ 9
  · exact Or.inl (Or.inl h54_eq_9)
  · by_cases h54_eq_18 : χ 54 = χ 18
    · exact Or.inl (Or.inr h54_eq_18)
    · exact Or.inr
        (bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_fourth_forces_chi36_in_9_or_18
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9 h54_eq_18)

/-! ### §162. R322 — Parallel Branch II χ(72)/χ(48) weak dispatcher.

  Goal: mirror R321 dispatch around the {72, 48} high-layer pair.

  **Audit note on χ(48) ≠ χ(27)** (= D ≠ A in the χ72 = D sub-case):
  not directly available from a single bAdicEquation 3 triple. Checked
  candidate triples:
  - xz self-loops `(3d, 2d, 3d)` for b=3: never produce {48, 27} since 3d=48
    ⟹ 2d=32, 3d=27 ⟹ 2d=18.
  - xy self-loops `(3m, 3m, 4m)` for b=3: never produce {48, 27} since 4m=48
    ⟹ 3m=36, 4m=27 not divisible.
  - General rado triples `(b·d, y, y+d)` with two positions in {48, 27}:
    (b·d, y, y+d) = (27, ?, 48), (48, ?, 27), or (?, 27, 48), (?, 48, 27)
    — none give a single-triple forcing of χ48 ≠ χ27 without additional
    color information.

  Consequence: stronger dispatch `χ(48) ∈ {B, C}` in the χ72 = D sub-case
  is NOT provable in this round. Weaker target `χ(48) ∈ {A, B, C}` is
  provable via the 4-color exhaustion argument (χ48 < 4, χ48 ≠ D := χ72).

  Theorem delivers: `(χ72 ∈ {B,C}) ∨ (χ48 ∈ {A,B,C})`.
  Strategically: even the weak form gives a hLayer coverage unit for χ48
  (an extra forced classification when χ72 falls outside {B, C}).
-/

/-- **R322 parallel Branch II χ(72)/χ(48) weak dispatcher**: under R318
  Branch II 3-anchor setup and `IsKColoring n 4 χ`,

    `(χ 72 = χ 9 ∨ χ 72 = χ 18) ∨ (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18)`.

  Mechanism: 3-way decidable by_cases on χ(72) vs {χ9, χ18}. If both fail,
  then χ(72) is the fourth color D since χ(72) ≠ A := χ27 (via triple
  `(27, 72, 81)` and h27_eq_81). Then χ(48) ≠ D via R321 universal
  `bAdicEquation_3_chi_48_ne_chi_72_in_monoFree` + 4-color exhaustion via
  omega ⟹ χ(48) ∈ {A, B, C}.

  Weaker than R321 dispatch (which classifies into {B, C}); the missing
  `χ(48) ≠ A` step is not available from a single triple — see §162 audit. -/
theorem bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 72 = χ 9 ∨ χ 72 = χ 18) ∨ (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) := by
  by_cases h72_eq_9 : χ 72 = χ 9
  · exact Or.inl (Or.inl h72_eq_9)
  · by_cases h72_eq_18 : χ 72 = χ 18
    · exact Or.inl (Or.inr h72_eq_18)
    · right
      -- Anchor pairwise distinctness.
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ(72) ≠ A := χ(27) via triple (27, 72, 81) + h27_eq_81 (R317 prefix step).
      have h72_ne_27 : χ 72 ≠ χ 27 := by
        intro h72_eq_27
        have hRado := bAdicEquation_general_rado_constraint
          (b := 3) (n := n) (by omega) χ hNoMono
          (d := 9) (y := 72) (by omega) (by omega) (by omega) (by omega)
        apply hRado
        refine ⟨?_, ?_⟩
        · show χ (3 * 9) = χ 72
          rw [show (3 * 9 : ℕ) = 27 by decide]; exact h72_eq_27.symm
        · show χ 72 = χ (72 + 9)
          rw [show (72 + 9 : ℕ) = 81 by decide]
          exact h72_eq_27.trans h27_eq_81
      -- χ(48) ≠ χ(72) via R321 universal self-loop (m=24).
      have h48_ne_72 : χ 48 ≠ χ 72 :=
        bAdicEquation_3_chi_48_ne_chi_72_in_monoFree χ (by omega) hNoMono
      -- All colors < 4 from IsKColoring at 9, 18, 27, 48, 72.
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h48_lt : χ 48 < 4 := hχk 48 (by omega) (by omega)
      have h72_lt : χ 72 < 4 := hχk 72 (by omega) (by omega)
      -- {A, B, C, D := χ72} pairwise distinct, all < 4 ⟹ {0,1,2,3}.
      -- χ(48) < 4 ∧ χ(48) ≠ D ⟹ χ(48) ∈ {A, B, C}.
      omega

/-! ### §163. R323 — Two-pair coverage integration + mid-layer χ(24)/χ(30) audit.

  Deliverables:
  - **Combined coverage**: package R321 (χ54/χ36 dispatch) and R322 (χ72/χ48
    dispatch) as a single `And` invariant for hLayer consumers.
  - **Universal mid self-loop χ(20) ≠ χ(30)** via triple (30, 20, 30); xz
    self-loop at b=3, m=10. Counterpart to existing `chi_16_ne_chi_24` (m=8).
  - **Audit: χ(24) ≠ χ(18) is already universal** via `chi_18_ne_chi_24`
    (BasicResults.lean, xy self-loop b=3, m=6, triple (18, 18, 24)). No
    Branch II hypothesis needed — used as `.symm`.
  - **Audit: χ(30) has NO direct single-triple exclusion** against any anchor
    A := χ27, B := χ9, C := χ18 in Branch II. Verified by enumeration:
    * xz self-loops (3d, 2d, 3d) never pair {30, anchor};
    * xy self-loops (3m, 3m, 4m) likewise (4m=30 not integer);
    * general rado triples (b·d, y, y+d) with two coordinates in {30, anchor}
      always need a third unclassified position OR have the conjunction
      `χ(b·d) = χ(y) ∧ χ(y) = χ(y+d)` vacuously satisfied via h9_ne_27 /
      χ18 ≠ χ24 / etc. Concretely:
        (9, 27, 30): conj contains χ9 = χ27, false by h9_ne_27 — vacuous.
        (18, 24, 30): conj contains χ18 = χ24, false universally — vacuous.
        (30, 27, 37), (30, 9, 19), (30, 18, 28): third coord unclassified.
        (63, 9, 30), (36, 18, 30): third coord unclassified.
    χ(30) classification requires future lateral information (e.g., partial
    hLayer fill at χ19/χ28/χ36/χ37/χ63).
-/

/-- **χ(20) ≠ χ(30)** for mono-free bAdicEquation 3 at n ≥ 30.
  Self-loop xz at m=10: triple `(30, 20, 30)` with 30 + 3·20 = 90 = 3·30.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=10).
  Reusable mid-layer self-loop, e.g., for future χ(30) = D fourth-color analysis. -/
theorem bAdicEquation_3_chi_20_ne_chi_30_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h30 : 30 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 20 ≠ χ 30 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 10) (by omega) (by omega)
  show χ ((3 - 1) * 10) ≠ χ (3 * 10)
  exact h

/-- **R323 combined two-pair coverage**: package R321 + R322 dispatchers as a
  single `And` invariant. Under R318 Branch II 3-anchor setup + IsKColoring n 4 χ,

    `(χ54 ∈ {B,C}) ∨ (χ36 ∈ {B,C})`     ∧
    `(χ72 ∈ {B,C}) ∨ (χ48 ∈ {A,B,C})`

  where A := χ27 = χ81, B := χ9, C := χ18. This is the unified entry point
  for future hLayer consumers that need the high-layer coverage facts in
  one place. Proof is `And.intro` of R321 and R322. -/
theorem bAdicEquation_3_branchII_two_pair_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    ((χ 54 = χ 9 ∨ χ 54 = χ 18) ∨ (χ 36 = χ 9 ∨ χ 36 = χ 18)) ∧
    ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
      (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18)) :=
  ⟨bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-! ### §164. R324 — χ(24)/χ(16) mid-layer dispatcher + extended coverage packaging.

  Deliverables:
  - **Main dispatch**: parallel to R322 weak dispatch, mid-layer version
    for {24, 16}. Under Branch II 3-anchor + IsKColoring n 4 χ,
        `(χ24 ∈ {A, B}) ∨ (χ16 ∈ {A, B, C})`.
    Mechanism: by_cases χ24 = A / χ24 = B; otherwise χ24 ≠ A, ≠ B, ≠ C
    (last from universal `chi_18_ne_chi_24`) ⟹ χ24 = D := fourth color.
    Then `χ16 ≠ χ24` (universal `chi_16_ne_chi_24`) + 4-color exhaustion
    via omega ⟹ χ16 ∈ {A, B, C}.
  - **Three coverage units packaging**: And.intro of R323 + R324 main.
  - **Optional self-loops** for χ22 ≠ χ33 (m=11) and χ28 ≠ χ42 (m=14),
    motivated by R319 conditional cascade (χ72 = B → χ33 ≠ B,
    χ72 = C → χ42 ≠ C) — these will support future fourth-color analysis
    around χ33/χ42 in the B/C sub-branches.
  - **Audit χ30**: still no direct A/B/C exclusion after re-check; same
    enumeration as R323 §163. χ30 remains conditional on χ19/χ28/χ37/χ63
    /χ36 partial classification.
-/

/-- **χ(22) ≠ χ(33)** for mono-free bAdicEquation 3 at n ≥ 33.
  Self-loop xz at m=11: triple `(33, 22, 33)` with 33 + 3·22 = 99 = 3·33.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=11).
  Useful for future χ(72) = B sub-branch analysis (R319 lemma gives χ33 ≠ B). -/
theorem bAdicEquation_3_chi_22_ne_chi_33_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h33 : 33 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 22 ≠ χ 33 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 11) (by omega) (by omega)
  show χ ((3 - 1) * 11) ≠ χ (3 * 11)
  exact h

/-- **χ(28) ≠ χ(42)** for mono-free bAdicEquation 3 at n ≥ 42.
  Self-loop xz at m=14: triple `(42, 28, 42)` with 42 + 3·28 = 126 = 3·42.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=14).
  Useful for future χ(72) = C sub-branch analysis (R319 lemma gives χ42 ≠ C). -/
theorem bAdicEquation_3_chi_28_ne_chi_42_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 28 ≠ χ 42 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 14) (by omega) (by omega)
  show χ ((3 - 1) * 14) ≠ χ (3 * 14)
  exact h

/-- **R324 main χ(24)/χ(16) mid-layer dispatcher**: under R318 Branch II
  3-anchor setup + `IsKColoring n 4 χ`,

    `(χ 24 = χ 27 ∨ χ 24 = χ 9) ∨ (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)`.

  Compression-dispatch transfer: if χ(24) is the fourth color D (outside
  {A, B, C}), the risk is pushed to χ(16) which must lie in {A, B, C}.

  Mechanism: 3-way ℕ-decidable by_cases on χ(24) vs {χ27, χ9}. Otherwise
  combine universal `chi_18_ne_chi_24` (giving χ24 ≠ C) with universal
  `chi_16_ne_chi_24` (giving χ16 ≠ D := χ24) and IsKColoring 4 — closed
  by omega via 4-color exhaustion. -/
theorem bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨ (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) := by
  by_cases h24_eq_27 : χ 24 = χ 27
  · exact Or.inl (Or.inl h24_eq_27)
  · by_cases h24_eq_9 : χ 24 = χ 9
    · exact Or.inl (Or.inr h24_eq_9)
    · right
      -- Anchor pairwise (C ≠ A).
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ(24) ≠ C via universal chi_18_ne_chi_24 (R323 audit recall).
      have h24_ne_18 : χ 24 ≠ χ 18 :=
        (bAdicEquation_3_chi_18_ne_chi_24 χ (by omega) hNoMono).symm
      -- χ(16) ≠ χ(24) via universal chi_16_ne_chi_24.
      have h16_ne_24 : χ 16 ≠ χ 24 :=
        bAdicEquation_3_chi_16_ne_chi_24 χ (by omega) hNoMono
      -- IsKColoring 4 at 9, 16, 18, 24, 27 (all ≤ 81 ≤ n).
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h16_lt : χ 16 < 4 := hχk 16 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h24_lt : χ 24 < 4 := hχk 24 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      -- {A, B, C, D := χ24} pairwise distinct, all < 4 ⟹ {0,1,2,3}.
      -- χ(16) < 4 ∧ χ(16) ≠ D ⟹ χ(16) ∈ {A, B, C}.
      omega

/-- **R324 three coverage units packaging**: combine R323 (two-pair coverage)
  with R324 main (χ24/χ16 dispatch) as a triple `And` invariant. Unified
  entry point for future hLayer assemblers needing all 3 coverage facts. -/
theorem bAdicEquation_3_branchII_three_coverage_units
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (((χ 54 = χ 9 ∨ χ 54 = χ 18) ∨ (χ 36 = χ 9 ∨ χ 36 = χ 18)) ∧
     ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
       (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18))) ∧
    ((χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
     (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_two_pair_coverage
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-! ### §165. R325 — Conditional dispatchers for χ(33)/χ(22) and χ(42)/χ(28).

  Deliverables:
  - **Target A** (χ72 = B sub-branch): `(χ33 ∈ {A, C}) ∨ (χ22 ∈ {A, B, C})`.
    Mechanism: R319 lemma `chi72_eq_chi9_forces_chi33_ne_chi9` gives χ33 ≠ B
    immediately; by_cases on χ33 = A / χ33 = C; otherwise χ33 is fourth color
    D, and R324 universal `chi_22_ne_chi_33` + IsKColoring 4 ⟹ χ22 ∈ {A,B,C}.
  - **Target B** (χ72 = C sub-branch): `(χ42 ∈ {A, B}) ∨ (χ28 ∈ {A, B, C})`.
    Parallel mechanism with R319 lemma `chi72_eq_chi18_forces_chi42_ne_chi18`
    + R324 universal `chi_28_ne_chi_42`.
  - **Target C**: packaging as `χ72 = B → ...` ∧ `χ72 = C → ...` for one-shot
    consumption by future χ72 branch dispatcher.

  **Audit χ(33), χ(42) unconditional exclusions**: NEITHER admits a direct
  single-triple exclusion against any anchor A, B, C without conditional
  hypotheses. Enumeration (in §165 docstring):
  - xz/xy self-loops never produce {33, anchor} or {42, anchor} pairs.
  - General rado triples involving {33, anchor} always need an unclassified
    third coordinate (χ20, χ24, χ29, χ38, χ45, χ30) OR have the conjunction
    vacuous via h9_ne_27 / hCA.
  - One conditional path: (72, 9, 33) gives χ33 ≠ χ9 IF h72_eq_9 (this is
    R319 itself). Similarly (72, 18, 42) gives χ42 ≠ χ18 IF h72_eq_18.
  - For χ42 also (?, 9, 42) requires d=33, b·d=99 > n=81: invalid.

  Conclusion: χ33 and χ42 classifications are inherently CONDITIONAL on
  χ72's value; the R325 dispatchers package this dependency structurally.
-/

/-- **R325 Target A — χ(72) = B conditional dispatcher**: under R318 Branch II
  3-anchor + `IsKColoring n 4 χ` + `χ 72 = χ 9`,

    `(χ 33 = χ 27 ∨ χ 33 = χ 18) ∨ (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)`.

  Mechanism: R319 `chi72_eq_chi9_forces_chi33_ne_chi9` gives χ33 ≠ B.
  ℕ-decidable by_cases on χ33 = A / χ33 = C. Otherwise χ33 is fourth color D;
  R324 universal `chi_22_ne_chi_33` + 4-color exhaustion via omega ⟹ χ22 ∈ {A,B,C}. -/
theorem bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_9 : χ 72 = χ 9) :
    (χ 33 = χ 27 ∨ χ 33 = χ 18) ∨ (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) := by
  -- From R319 conditional cascade: χ33 ≠ B = χ9.
  have h33_ne_9 : χ 33 ≠ χ 9 :=
    bAdicEquation_3_chi72_eq_chi9_forces_chi33_ne_chi9 χ (by omega) hNoMono h72_eq_9
  by_cases h33_eq_27 : χ 33 = χ 27
  · exact Or.inl (Or.inl h33_eq_27)
  · by_cases h33_eq_18 : χ 33 = χ 18
    · exact Or.inl (Or.inr h33_eq_18)
    · right
      -- Anchor C ≠ A.
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ22 ≠ χ33 (R324 universal m=11).
      have h22_ne_33 : χ 22 ≠ χ 33 :=
        bAdicEquation_3_chi_22_ne_chi_33_in_monoFree χ (by omega) hNoMono
      -- IsKColoring 4 at 9, 18, 22, 27, 33.
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h22_lt : χ 22 < 4 := hχk 22 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h33_lt : χ 33 < 4 := hχk 33 (by omega) (by omega)
      -- {A, B, C, D := χ33} pairwise < 4 ⟹ {0,1,2,3}; χ22 ≠ D ⟹ χ22 ∈ {A,B,C}.
      omega

/-- **R325 Target B — χ(72) = C conditional dispatcher**: under R318 Branch II
  3-anchor + `IsKColoring n 4 χ` + `χ 72 = χ 18`,

    `(χ 42 = χ 27 ∨ χ 42 = χ 9) ∨ (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)`.

  Mechanism: R319 `chi72_eq_chi18_forces_chi42_ne_chi18` gives χ42 ≠ C.
  ℕ-decidable by_cases on χ42 = A / χ42 = B. Otherwise χ42 is fourth color D;
  R324 universal `chi_28_ne_chi_42` + 4-color exhaustion via omega ⟹ χ28 ∈ {A,B,C}. -/
theorem bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18) :
    (χ 42 = χ 27 ∨ χ 42 = χ 9) ∨ (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) := by
  -- From R319 conditional cascade: χ42 ≠ C = χ18.
  have h42_ne_18 : χ 42 ≠ χ 18 :=
    bAdicEquation_3_chi72_eq_chi18_forces_chi42_ne_chi18 χ (by omega) hNoMono h72_eq_18
  by_cases h42_eq_27 : χ 42 = χ 27
  · exact Or.inl (Or.inl h42_eq_27)
  · by_cases h42_eq_9 : χ 42 = χ 9
    · exact Or.inl (Or.inr h42_eq_9)
    · right
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ28 ≠ χ42 (R324 universal m=14).
      have h28_ne_42 : χ 28 ≠ χ 42 :=
        bAdicEquation_3_chi_28_ne_chi_42_in_monoFree χ (by omega) hNoMono
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h28_lt : χ 28 < 4 := hχk 28 (by omega) (by omega)
      have h42_lt : χ 42 < 4 := hχk 42 (by omega) (by omega)
      -- {A, B, C, D := χ42} pairwise < 4 ⟹ {0,1,2,3}; χ28 ≠ D ⟹ χ28 ∈ {A,B,C}.
      omega

/-- **R325 Target C — χ(72) branch refinement packaging**: package the two
  R325 conditional dispatchers as a single `And` of implications for the
  χ72 = B / χ72 = C sub-branches. Unified consumption by future χ72 branch
  closure (R326+). -/
theorem bAdicEquation_3_branchII_chi72_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 72 = χ 9 →
      ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
       (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18))) ∧
    (χ 72 = χ 18 →
      ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
       (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18))) :=
  ⟨fun h72_eq_9 =>
     bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
       χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9,
   fun h72_eq_18 =>
     bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
       χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18⟩

/-! ### §166. R326 — Conditional dispatchers for χ(54) sub-branches.

  Mirror R325 for the χ(54) ∈ {B, C} sub-branches given by R321's left side.

  Deliverables:
  - **Universal self-loop** χ(24) ≠ χ(36): triple (36, 24, 36), xz self-loop
    at b=3, m=12. Counterpart to R320 (χ36 ≠ χ54) for the χ(36) fourth-color
    risk transfer downward.
  - **Target B** (χ54 = B sub-branch): `(χ36 ∈ {A, C}) ∨ (χ24 ∈ {A, B, C})`.
    Mechanism: R320 universal `chi_36_ne_chi_54` + h54_eq_9 ⟹ χ36 ≠ B.
    by_cases χ36 = A / χ36 = C; otherwise χ36 = D := fourth color, then
    universal `chi_24_ne_chi_36` + 4-color exhaustion via omega ⟹ χ24 ∈ {A,B,C}.
  - **Target C** (χ54 = C sub-branch): `(χ36 ∈ {A, B}) ∨ (χ24 ∈ {A, B, C})`.
    Parallel mechanism with R319 `chi54_eq_chi18_forces_chi36_ne_chi18` +
    R326 new universal `chi_24_ne_chi_36`.
  - **Target D**: packaging as `χ54 = B → ...` ∧ `χ54 = C → ...` for one-shot
    consumption by future χ54 branch closure.
-/

/-- **χ(24) ≠ χ(36)** for mono-free bAdicEquation 3 at n ≥ 36.
  Self-loop xz at m=12: triple `(36, 24, 36)` with 36 + 3·24 = 108 = 3·36.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=12).
  Used in R326 χ(54) sub-branch dispatchers for χ(36) fourth-color
  risk transfer to χ(24). -/
theorem bAdicEquation_3_chi_24_ne_chi_36_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 24 ≠ χ 36 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 12) (by omega) (by omega)
  show χ ((3 - 1) * 12) ≠ χ (3 * 12)
  exact h

/-- **R326 Target B — χ(54) = B conditional dispatcher**: under R318 Branch II
  3-anchor + `IsKColoring n 4 χ` + `χ 54 = χ 9`,

    `(χ 36 = χ 27 ∨ χ 36 = χ 18) ∨ (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)`.

  Mechanism: R320 universal `chi_36_ne_chi_54` + h54_eq_9 ⟹ χ36 ≠ B.
  ℕ-decidable by_cases on χ36 = A / χ36 = C. Otherwise χ36 = D := fourth
  color; R326 new universal `chi_24_ne_chi_36` + IsKColoring 4 + omega
  4-color exhaustion ⟹ χ24 ∈ {A, B, C}. -/
theorem bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_9 : χ 54 = χ 9) :
    (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨ (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18) := by
  -- From R320 universal: χ36 ≠ χ54; with h54_eq_9: χ36 ≠ B.
  have h36_ne_54 : χ 36 ≠ χ 54 :=
    bAdicEquation_3_chi_36_ne_chi_54_in_monoFree χ (by omega) hNoMono
  have h36_ne_9 : χ 36 ≠ χ 9 := h54_eq_9 ▸ h36_ne_54
  by_cases h36_eq_27 : χ 36 = χ 27
  · exact Or.inl (Or.inl h36_eq_27)
  · by_cases h36_eq_18 : χ 36 = χ 18
    · exact Or.inl (Or.inr h36_eq_18)
    · right
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ24 ≠ χ36 (R326 universal m=12).
      have h24_ne_36 : χ 24 ≠ χ 36 :=
        bAdicEquation_3_chi_24_ne_chi_36_in_monoFree χ (by omega) hNoMono
      -- IsKColoring 4 at 9, 18, 24, 27, 36.
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h24_lt : χ 24 < 4 := hχk 24 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h36_lt : χ 36 < 4 := hχk 36 (by omega) (by omega)
      -- {A, B, C, D := χ36} pairwise < 4 ⟹ {0,1,2,3}; χ24 ≠ D ⟹ χ24 ∈ {A,B,C}.
      omega

/-- **R326 Target C — χ(54) = C conditional dispatcher**: under R318 Branch II
  3-anchor + `IsKColoring n 4 χ` + `χ 54 = χ 18`,

    `(χ 36 = χ 27 ∨ χ 36 = χ 9) ∨ (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)`.

  Mechanism: R319 `chi54_eq_chi18_forces_chi36_ne_chi18` ⟹ χ36 ≠ C.
  ℕ-decidable by_cases on χ36 = A / χ36 = B. Otherwise χ36 = D := fourth
  color; R326 universal `chi_24_ne_chi_36` + 4-color exhaustion via omega
  ⟹ χ24 ∈ {A, B, C}. -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18) :
    (χ 36 = χ 27 ∨ χ 36 = χ 9) ∨ (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18) := by
  -- From R319 conditional cascade: χ36 ≠ C = χ18.
  have h36_ne_18 : χ 36 ≠ χ 18 :=
    bAdicEquation_3_chi54_eq_chi18_forces_chi36_ne_chi18 χ (by omega) hNoMono h54_eq_18
  by_cases h36_eq_27 : χ 36 = χ 27
  · exact Or.inl (Or.inl h36_eq_27)
  · by_cases h36_eq_9 : χ 36 = χ 9
    · exact Or.inl (Or.inr h36_eq_9)
    · right
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      have h24_ne_36 : χ 24 ≠ χ 36 :=
        bAdicEquation_3_chi_24_ne_chi_36_in_monoFree χ (by omega) hNoMono
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h24_lt : χ 24 < 4 := hχk 24 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h36_lt : χ 36 < 4 := hχk 36 (by omega) (by omega)
      -- {A, B, C, D := χ36} pairwise < 4 ⟹ {0,1,2,3}; χ24 ≠ D ⟹ χ24 ∈ {A,B,C}.
      omega

/-- **R326 Target D — χ(54) branch refinement packaging**: package the two
  R326 conditional dispatchers as a single `And` of implications for the
  χ54 = B / χ54 = C sub-branches. Parallel to R325 `chi72_branch_refinement`. -/
theorem bAdicEquation_3_branchII_chi54_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 54 = χ 9 →
      ((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
       (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18))) ∧
    (χ 54 = χ 18 →
      ((χ 36 = χ 27 ∨ χ 36 = χ 9) ∨
       (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18))) :=
  ⟨fun h54_eq_9 =>
     bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
       χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9,
   fun h54_eq_18 =>
     bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
       χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18⟩

/-! ### §167. R327 — Chain coverage integration for χ(54) and χ(72) branches.

  Goal: collapse the R321/R322 + R325/R326 dispatch graph into clean
  chain coverage invariants involving only the natural target positions.

  Deliverables:
  - **χ(54)-chain coverage**: combine R321 + R326-B + R326-C into
        `χ36 ∈ {A, B, C}` ∨ `χ24 ∈ {A, B, C}`.
    All R321 sub-cases (χ54 ∈ {B, C} or χ36 ∈ {B, C}) collapse to one of
    two anchor-set memberships in {χ36, χ24}.
  - **χ(72)-chain coverage**: combine R322 + R325-A + R325-B into
        `χ48 ∈ {A, B, C}` ∨ (R325-A conclusion) ∨ (R325-B conclusion).
    All R322 sub-cases (χ72 ∈ {B, C} or χ48 ∈ {A, B, C}) dispatch.
  - **Branch II chain coverage summary**: package chi54-chain + chi72-chain
    + R324 chi24/chi16 dispatch as a triple `And` invariant.

  Strategic value: the R321/R322 dispatch left-branches were previously
  the only un-collapsed obligation in the high-layer attack. R327 consumes
  them through R326/R325 to deliver flat coverage statements.
-/

/-- **R327 χ(54)-chain coverage**: combining R321 (χ54/χ36 dispatch) with
  R326-B (χ54=B sub-branch) and R326-C (χ54=C sub-branch) yields the flat
  invariant

    `(χ 36 ∈ {A, B, C}) ∨ (χ 24 ∈ {A, B, C})`.

  All χ(54) sub-cases are absorbed; only χ(36) and χ(24) appear in the
  conclusion. Proof: rcases on R321, with each branch dispatching through
  R326 or directly handling χ36 ∈ {B, C}. -/
theorem bAdicEquation_3_branchII_chi54_chain_coverage_36_or_24
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 36 = χ 27 ∨ χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
    (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18) := by
  have hR321 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases hR321 with h54BC | h36BC
  · rcases h54BC with h54B | h54C
    · -- χ54 = B: use R326-B dispatcher.
      have h := bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B
      rcases h with h36AC | h24ABC
      · left
        rcases h36AC with h36A | h36C
        · exact Or.inl h36A
        · exact Or.inr (Or.inr h36C)
      · exact Or.inr h24ABC
    · -- χ54 = C: use R326-C dispatcher.
      have h := bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C
      rcases h with h36AB | h24ABC
      · left
        rcases h36AB with h36A | h36B
        · exact Or.inl h36A
        · exact Or.inr (Or.inl h36B)
      · exact Or.inr h24ABC
  · -- χ36 ∈ {B, C} directly.
    left
    rcases h36BC with h36B | h36C
    · exact Or.inr (Or.inl h36B)
    · exact Or.inr (Or.inr h36C)

/-- **R327 χ(72)-chain coverage**: combining R322 (χ72/χ48 weak dispatch)
  with R325-A (χ72=B sub-branch) and R325-B (χ72=C sub-branch) yields the
  3-way invariant

    `(χ 48 ∈ {A, B, C}) ∨ (R325-A conclusion) ∨ (R325-B conclusion)`,

  where R325-A = `(χ 33 ∈ {A, C}) ∨ (χ 22 ∈ {A, B, C})` and R325-B =
  `(χ 42 ∈ {A, B}) ∨ (χ 28 ∈ {A, B, C})`. All χ(72) sub-cases dispatch. -/
theorem bAdicEquation_3_branchII_chi72_chain_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) ∨
    ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
      (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∨
    ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
      (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)) := by
  have hR322 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases hR322 with h72BC | h48ABC
  · rcases h72BC with h72B | h72C
    · -- χ72 = B: use R325-A.
      have h := bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72B
      exact Or.inr (Or.inl h)
    · -- χ72 = C: use R325-B.
      have h := bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72C
      exact Or.inr (Or.inr h)
  · -- χ48 ∈ {A, B, C} directly.
    exact Or.inl h48ABC

/-- **R327 Branch II chain coverage summary**: package the χ54-chain + χ72-chain
  + R324 χ24/χ16 dispatchers into a triple `And` invariant. Unified entry
  point for downstream consumers after R325/R326 sub-branch collapses. -/
theorem bAdicEquation_3_branchII_chain_coverage_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
     (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
    ((χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) ∨
     ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
       (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∨
     ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
       (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18))) ∧
    ((χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
     (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi54_chain_coverage_36_or_24
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_branchII_chi72_chain_coverage
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-! ### §168. R328 — Refined χ(54)-chain via R324 χ(24)/χ(16) dispatcher.

  Goal: sharpen R327 `chi54_chain_coverage_36_or_24` by replacing the
  `χ24 ∈ {A, B, C}` disjunct with the strictly tighter R324 split
  `χ24 ∈ {A, B} ∨ χ16 ∈ ABC`. Net result:

      `χ36 ∈ {A, B, C}` ∨ `χ24 ∈ {A, B}` ∨ `χ16 ∈ {A, B, C}`.

  R324 is unconditional under Branch II, so once the R327 chain falls to
  the χ24 side, R324 immediately refines. The χ36 side is propagated
  unchanged.

  **Next refinement target audit** (for R329+):
  - χ(48) (R322/R327 right-side): IS a layer position (3·16). Best next
    target. R322 weak split into {A, B, C}; can attempt a χ48 sub-branch
    dispatcher analogous to R325/R326 around χ48 ∈ {A, B, C}.
  - χ(22) (R325-A right-side): NOT a layer position (22 ≠ 3·d). Lower
    transfer point; refinement gives less direct hLayer progress.
  - χ(28) (R325-B right-side): NOT a layer position (28 ≠ 3·d).
    Same caveat as χ22.
  Conclusion: χ48 is the highest-value next refinement target.
-/

/-- **R328 refined χ(54)-chain coverage**: tighten R327
  `chi54_chain_coverage_36_or_24` using the unconditional R324 χ24/χ16
  dispatcher. Under R318 Branch II 3-anchor + IsKColoring n 4 χ,

    `(χ 36 ∈ {A, B, C}) ∨ (χ 24 ∈ {A, B}) ∨ (χ 16 ∈ {A, B, C})`.

  Strictly stronger than R327 chi54-chain: the χ24 disjunct shrinks from
  {A, B, C} to {A, B}, and the residual is absorbed into χ16 ∈ {A, B, C}. -/
theorem bAdicEquation_3_branchII_chi54_chain_coverage_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 36 = χ 27 ∨ χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) := by
  have hChain :=
    bAdicEquation_3_branchII_chi54_chain_coverage_36_or_24
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases hChain with h36ABC | _h24ABC
  · exact Or.inl h36ABC
  · -- Drop the R327 χ24 ∈ ABC info; use the stricter unconditional R324.
    have h24_or_h16 :=
      bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
    rcases h24_or_h16 with h24AB | h16ABC
    · exact Or.inr (Or.inl h24AB)
    · exact Or.inr (Or.inr h16ABC)

/-- **R328 refined Branch II chain coverage summary**: package the
  R328 refined χ54-chain + R327 χ72-chain into a unified `And` invariant.
  Replaces R327 `chain_coverage_summary` with strict refinement on the
  χ54 side. -/
theorem bAdicEquation_3_branchII_chain_coverage_summary_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
     (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
     (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) ∧
    ((χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) ∨
     ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
       (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∨
     ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
       (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18))) :=
  ⟨bAdicEquation_3_branchII_chi54_chain_coverage_refined
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_branchII_chi72_chain_coverage
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-! ### §169. R329 — χ(48) branch refinement infrastructure.

  Deliverables:
  - **Universal self-loop** `χ(32) ≠ χ(48)`: xz self-loop at b=3, m=16,
    triple (48, 32, 48). Reusable infrastructure for future χ48 dispatchers.
  - **Three conditional exclusion lemmas** for χ(48) sub-branches:
    * `χ48 = A → χ75 ≠ A` via triple (81, 48, 75) + h27_eq_81;
    * `χ48 = B → χ51 ≠ B` via triple (9, 48, 51);
    * `χ48 = C → χ54 ≠ C` via triple (18, 48, 54).
  - **χ48 branch refinement package**: And of the three conditional implications.

  These do NOT form a full χ48 dispatcher (which would require a transfer
  point like χ32 ∈ {A, B, C}). They establish that each χ48 sub-branch
  forces a specific neighboring layer-position exclusion.

  **Strategic value of `χ48 = C → χ54 ≠ C`**: this interacts strongly with
  R321's left branch `χ54 ∈ {B, C}`. If χ48 = C, then χ54 ∈ {B, C} narrows
  to χ54 = B (since χ54 ≠ C). That collapses one sub-branch in R326.

  **Audit: χ32 dispatcher viability** (Target D):
  χ32 is NOT a layer position (32 ≠ 3·d) and 32 is not divisible by 3,
  so it has no x = z = 32 self-loop. However:
  - xy self-loop at b=3, m=8: triple (24, 24, 32) gives `χ24 ≠ χ32`.
    This connects χ32 UPWARD to χ24 (already covered by R324), not downward.
  - Under χ48 = anchor, R329 universal gives `χ32 ≠ that anchor`. Combined
    with χ32 < 4 + 4-color exhaustion, χ32 ∈ {other anchors, D}. Pushing
    χ32 = D case via xy self-loop `χ24 ≠ χ32 = D` yields `χ24 ≠ D`, which
    R324 already provides (with even stronger χ24 ∈ {A, B}).
  Conclusion: a dedicated χ32 dispatcher would not yield new hLayer
  information beyond what R324 already gives. R329 therefore stops at
  conditional exclusion lemmas rather than building a χ32 dispatcher.
-/

/-- **χ(32) ≠ χ(48)** for mono-free bAdicEquation 3 at n ≥ 48.
  Self-loop xz at m=16: triple `(48, 32, 48)` with 48 + 3·32 = 144 = 3·48.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=16).
  Companion to R320/R321 (m=18, 24) and R326 (m=12) high/mid self-loops. -/
theorem bAdicEquation_3_chi_32_ne_chi_48_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 32 ≠ χ 48 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 16) (by omega) (by omega)
  show χ ((3 - 1) * 16) ≠ χ (3 * 16)
  exact h

/-- **R329 χ(48) = A conditional exclusion**: under Branch II
  (h27_eq_81 implies χ81 = A) and `χ 48 = χ 27`, the triple `(81, 48, 75)`
  forces `χ 75 ≠ χ 27`.
  Triple: 81 + 3·48 = 225 = 3·75. -/
theorem bAdicEquation_3_chi48_eq_chi27_forces_chi75_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h48_eq_27 : χ 48 = χ 27) :
    χ 75 ≠ χ 27 := by
  intro h75_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 27) (y := 48) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 27) = χ 48
    rw [show (3 * 27 : ℕ) = 81 by decide]
    exact h27_eq_81.symm.trans h48_eq_27.symm
  · show χ 48 = χ (48 + 27)
    rw [show (48 + 27 : ℕ) = 75 by decide]
    exact h48_eq_27.trans h75_eq_27.symm

/-- **R329 χ(48) = B conditional exclusion**: under `χ 48 = χ 9`, the
  triple `(9, 48, 51)` forces `χ 51 ≠ χ 9`.
  Triple: 9 + 3·48 = 153 = 3·51. n ≥ 81 sufficient for n ≥ 51. -/
theorem bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9) :
    χ 51 ≠ χ 9 := by
  intro h51_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 48) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 48
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h48_eq_9.symm
  · show χ 48 = χ (48 + 3)
    rw [show (48 + 3 : ℕ) = 51 by decide]
    exact h48_eq_9.trans h51_eq_9.symm

/-- **R329 χ(48) = C conditional exclusion**: under `χ 48 = χ 18`, the
  triple `(18, 48, 54)` forces `χ 54 ≠ χ 18`.
  Triple: 18 + 3·48 = 162 = 3·54.

  **Strategic value**: with R321 `χ54 ∈ {B, C}`, this collapses χ54 = C
  to χ54 = B, removing one sub-branch in R326. -/
theorem bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18) :
    χ 54 ≠ χ 18 := by
  intro h54_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 48) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 48
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h48_eq_18.symm
  · show χ 48 = χ (48 + 6)
    rw [show (48 + 6 : ℕ) = 54 by decide]
    exact h48_eq_18.trans h54_eq_18.symm

/-- **R329 χ(48) branch refinement package**: three conditional exclusion
  implications for χ48 = A / B / C sub-branches. Not a full dispatcher
  (no transfer to a single fully-classified position); rather, each
  sub-branch forces a specific layer-position exclusion that downstream
  rounds can chain into the broader hLayer attack. -/
theorem bAdicEquation_3_branchII_chi48_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 48 = χ 27 → χ 75 ≠ χ 27) ∧
    (χ 48 = χ 9  → χ 51 ≠ χ 9) ∧
    (χ 48 = χ 18 → χ 54 ≠ χ 18) :=
  ⟨fun h48_eq_27 =>
     bAdicEquation_3_chi48_eq_chi27_forces_chi75_ne_chi27
       χ h81 hNoMono h27_eq_81 h48_eq_27,
   fun h48_eq_9 =>
     bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
       χ h81 hNoMono h48_eq_9,
   fun h48_eq_18 =>
     bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
       χ (by omega) hNoMono h48_eq_18⟩

/-! ### §170. R330 — Exploit χ(48) = C strategic cascade.

  R329 established `χ 48 = χ 18 → χ 54 ≠ χ 18` (triple (18, 48, 54)).
  Combined with R321 dispatch `χ54 ∈ {B, C} ∨ χ36 ∈ {B, C}`, the
  χ54 = C sub-branch is eliminated under χ48 = C, collapsing R321's
  left side to χ54 = B which R326-B handles.

  Deliverables:
  - **Target B** (`chi48_eq18_forces_chi36_or_chi24_refined`): under
    χ48 = C, output is `χ36 ∈ {B, C}` ∨ (R326-B conclusion).
  - **Target C** (`chi48_eq18_forces_refined_chain`): further refine
    via R324 dispatcher, output is 4-disjunct:
      `χ36 ∈ {B, C}` ∨ `χ36 ∈ {A, C}` ∨ `χ24 ∈ {A, B}` ∨ `χ16 ∈ {A, B, C}`.

  **Audit χ48 = A / B future branches** (for R331+):
  - **χ48 = A → χ75 ≠ A** (R329). χ75 is a layer position (75 = 3·25).
    Next step: universal self-loop `χ50 ≠ χ75` (xz at m=25, triple
    (75, 50, 75): 75 + 3·50 = 225 = 3·75). Under χ48 = A, χ75 ∈ {B, C, D}.
    If χ75 = D fourth color, χ50 ≠ D + 4-color exhaustion ⟹ χ50 ∈ {A, B, C}.
    Need additional anchor exclusion (χ75 ≠ B/C?) to make this a dispatcher.
  - **χ48 = B → χ51 ≠ B** (R329). χ51 is a layer position (51 = 3·17).
    Next step: universal self-loop `χ34 ≠ χ51` (xz at m=17, triple
    (51, 34, 51): 51 + 3·34 = 153 = 3·51).
  Both candidate dispatchers exist but require additional anchor
  exclusions (analogous to R326's `χ54 ≠ A`). Not pursued in R330.
-/

/-- **R330 Target B — χ(48) = C forces χ(36) or χ(24) refined coverage**:
  combines R321 dispatcher with R329 `chi48_eq_chi18_forces_chi54_ne_chi18`
  to eliminate R321's χ54 = C sub-branch.

  Result: under R318 Branch II 3-anchor + `IsKColoring n 4 χ` + `χ 48 = χ 18`,

    `(χ 36 = χ 9 ∨ χ 36 = χ 18) ∨ R326-B conclusion`.

  This is strictly stronger than R327 chi54-chain in the χ48 = C scenario:
  the χ54 = C sub-branch is closed by contradiction with `χ 54 ≠ χ 18`. -/
theorem bAdicEquation_3_branchII_chi48_eq18_forces_chi36_or_chi24_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_18 : χ 48 = χ 18) :
    (χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
    ((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) := by
  have hR321 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  -- R329 strategic lemma: χ48 = C ⟹ χ54 ≠ C.
  have h54_ne_18 :=
    bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
      χ (by omega) hNoMono h48_eq_18
  rcases hR321 with h54BC | h36BC
  · rcases h54BC with h54B | h54C
    · -- χ54 = B: use R326-B dispatcher.
      have h := bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B
      exact Or.inr h
    · -- χ54 = C: contradiction with R329 χ54 ≠ C under χ48 = C.
      exact absurd h54C h54_ne_18
  · -- χ36 ∈ {B, C} directly.
    exact Or.inl h36BC

/-- **R330 Target C — χ(48) = C forces refined chain coverage**: further
  refine R330 Target B by dispatching the χ24 ∈ {A, B, C} disjunct (from
  R326-B fallback) through R324 chi24/chi16 dispatcher.

  Result: under R318 Branch II 3-anchor + `IsKColoring n 4 χ` + `χ 48 = χ 18`,

    `(χ 36 ∈ {B, C}) ∨ (χ 36 ∈ {A, C}) ∨ (χ 24 ∈ {A, B}) ∨ (χ 16 ∈ {A, B, C})`.

  4-disjunct invariant; strictly stronger than Target B in the χ54 = B
  sub-branch (χ24 disjunct narrows from {A, B, C} to {A, B} via R324). -/
theorem bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_18 : χ 48 = χ 18) :
    (χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
    (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) := by
  have hR321 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  have h54_ne_18 :=
    bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
      χ (by omega) hNoMono h48_eq_18
  rcases hR321 with h54BC | h36BC
  · rcases h54BC with h54B | h54C
    · -- χ54 = B: use R326-B + R324 chain.
      have h := bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B
      rcases h with h36AC | _h24ABC
      · -- χ36 ∈ {A, C}: 2nd disjunct.
        exact Or.inr (Or.inl h36AC)
      · -- Drop R326's χ24 ∈ ABC; use stricter R324.
        have h24_or_h16 := bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
        rcases h24_or_h16 with h24AB | h16ABC
        · -- χ24 ∈ {A, B}: 3rd disjunct.
          exact Or.inr (Or.inr (Or.inl h24AB))
        · -- χ16 ∈ {A, B, C}: 4th disjunct.
          exact Or.inr (Or.inr (Or.inr h16ABC))
    · exact absurd h54C h54_ne_18
  · -- χ36 ∈ {B, C}: 1st disjunct.
    exact Or.inl h36BC

/-! ### §171. R331 — χ(48) = A and χ(48) = B weak dispatchers.

  Deliverables:
  - **Universal self-loops**:
    * `χ50 ≠ χ75` (xz at m=25, triple (75, 50, 75): 75 + 3·50 = 225 = 3·75).
    * `χ34 ≠ χ51` (xz at m=17, triple (51, 34, 51): 51 + 3·34 = 153 = 3·51).
  - **χ48 = A weak dispatcher** `(χ75 ∈ {B, C}) ∨ (χ50 ∈ {A, B, C})`.
    Mechanism: R329 gives χ75 ≠ A. by_cases χ75 = B / χ75 = C; otherwise
    χ75 = D := fourth color, R331 universal `chi_50_ne_chi_75` +
    4-color exhaustion via omega ⟹ χ50 ∈ {A, B, C}.
  - **χ48 = B weak dispatcher** `(χ51 ∈ {A, C}) ∨ (χ34 ∈ {A, B, C})`.
    Parallel mechanism with R329 χ48=B → χ51 ≠ B + R331 chi_34_ne_chi_51.

  **Audit χ(75) direct B/C exclusion** (Target C): NO unconditional
  single-triple route. Enumeration:
  - xz/xy self-loops never pair {75, B} or {75, C} (3d=75 ⟹ 2d=50;
    4m=75 not divisible; 3m=75 ⟹ 4m=100 > n=81).
  - General rado triples with two coords in {75, B}: (75, 9, 34),
    (9, 75, 78), (9, 72, 75) all need a third unclassified position
    (χ34, χ78) or conditional on χ72 = B.
  - General rado with {75, C}: (75, 18, 43), (18, 75, 81), (18, 69, 75)
    all need third unclassified position or are vacuous via hCA.

  Conclusion: χ75 = D fourth-color analysis (the R331 dispatcher mechanism)
  is the only available path. χ50 absorbs the fourth-color risk.
-/

/-- **χ(50) ≠ χ(75)** for mono-free bAdicEquation 3 at n ≥ 75.
  Self-loop xz at m=25: triple `(75, 50, 75)` with 75 + 3·50 = 225 = 3·75.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=25). -/
theorem bAdicEquation_3_chi_50_ne_chi_75_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h75 : 75 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 50 ≠ χ 75 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 25) (by omega) (by omega)
  show χ ((3 - 1) * 25) ≠ χ (3 * 25)
  exact h

/-- **χ(34) ≠ χ(51)** for mono-free bAdicEquation 3 at n ≥ 51.
  Self-loop xz at m=17: triple `(51, 34, 51)` with 51 + 3·34 = 153 = 3·51.
  Instantiation of `bAdicEquation_self_loop_chi_diff` (b=3, m=17). -/
theorem bAdicEquation_3_chi_34_ne_chi_51_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h51 : 51 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 34 ≠ χ 51 := by
  have h := bAdicEquation_self_loop_chi_diff (b := 3) (n := n) (by omega) χ hNoMono
    (m := 17) (by omega) (by omega)
  show χ ((3 - 1) * 17) ≠ χ (3 * 17)
  exact h

/-- **R331 χ(48) = A weak dispatcher**: under R318 Branch II 3-anchor +
  `IsKColoring n 4 χ` + `χ 48 = χ 27`,

    `(χ 75 = χ 9 ∨ χ 75 = χ 18) ∨ (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)`.

  Mechanism: R329 χ48=A → χ75 ≠ A. ℕ-decidable by_cases on χ75 = B / C.
  Otherwise χ75 = D fourth color; R331 universal chi_50_ne_chi_75 +
  4-color exhaustion via omega ⟹ χ50 ∈ {A, B, C}. -/
theorem bAdicEquation_3_branchII_chi48_eq27_chi75_or_chi50_in_BC_or_ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_27 : χ 48 = χ 27) :
    (χ 75 = χ 9 ∨ χ 75 = χ 18) ∨
    (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) := by
  -- From R329: χ75 ≠ A = χ27.
  have h75_ne_27 :=
    bAdicEquation_3_chi48_eq_chi27_forces_chi75_ne_chi27
      χ h81 hNoMono h27_eq_81 h48_eq_27
  by_cases h75_eq_9 : χ 75 = χ 9
  · exact Or.inl (Or.inl h75_eq_9)
  · by_cases h75_eq_18 : χ 75 = χ 18
    · exact Or.inl (Or.inr h75_eq_18)
    · right
      -- Anchor pairwise distinctness (C ≠ A).
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ50 ≠ χ75 (R331 universal m=25).
      have h50_ne_75 : χ 50 ≠ χ 75 :=
        bAdicEquation_3_chi_50_ne_chi_75_in_monoFree χ (by omega) hNoMono
      -- IsKColoring 4 at 9, 18, 27, 50, 75.
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h50_lt : χ 50 < 4 := hχk 50 (by omega) (by omega)
      have h75_lt : χ 75 < 4 := hχk 75 (by omega) (by omega)
      -- {A, B, C, D := χ75} pairwise < 4 ⟹ {0,1,2,3}; χ50 ≠ D ⟹ χ50 ∈ {A,B,C}.
      omega

/-- **R331 χ(48) = B weak dispatcher**: under R318 Branch II 3-anchor +
  `IsKColoring n 4 χ` + `χ 48 = χ 9`,

    `(χ 51 = χ 27 ∨ χ 51 = χ 18) ∨ (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)`.

  Parallel to R331 χ48=A dispatcher. Mechanism: R329 χ48=B → χ51 ≠ B.
  ℕ-decidable by_cases on χ51 = A / C. Otherwise χ51 = D fourth color;
  R331 universal chi_34_ne_chi_51 + 4-color exhaustion via omega ⟹
  χ34 ∈ {A, B, C}. -/
theorem bAdicEquation_3_branchII_chi48_eq9_chi51_or_chi34_in_AC_or_ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 51 = χ 27 ∨ χ 51 = χ 18) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) := by
  -- From R329: χ51 ≠ B = χ9.
  have h51_ne_9 :=
    bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
      χ h81 hNoMono h48_eq_9
  by_cases h51_eq_27 : χ 51 = χ 27
  · exact Or.inl (Or.inl h51_eq_27)
  · by_cases h51_eq_18 : χ 51 = χ 18
    · exact Or.inl (Or.inr h51_eq_18)
    · right
      have hCA : χ 18 ≠ χ 27 :=
        bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
      -- χ34 ≠ χ51 (R331 universal m=17).
      have h34_ne_51 : χ 34 ≠ χ 51 :=
        bAdicEquation_3_chi_34_ne_chi_51_in_monoFree χ (by omega) hNoMono
      have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
      have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
      have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
      have h34_lt : χ 34 < 4 := hχk 34 (by omega) (by omega)
      have h51_lt : χ 51 < 4 := hχk 51 (by omega) (by omega)
      omega

/-! ### §172. R332 — Full χ(48) branch integration into χ(72)-chain.

  Deliverables:
  - **Target A** `chi48_in_ABC_full_coverage`: consumes `χ48 ∈ {A, B, C}`
    and returns the 3-way expansion using R330 (χ48=C) + R331-A (χ48=A)
    + R331-B (χ48=B) dispatchers.
  - **Target B** `chi72_chain_coverage_expanded_chi48`: replaces R327's
    `χ48 ∈ ABC` terminal disjunct with Target A expansion. The χ72-chain
    no longer has any terminal χ48 atom — every leaf is now a layer or
    transfer position.
  - **Target C** `chain_coverage_summary_chi48_expanded`: updated global
    Branch II summary using refined χ54-chain + expanded χ72-chain.

  **Best next refinement target audit** (for R333+):
  - **χ75 ∈ {B, C}** (from χ48=A): χ75 is a layer position (3·25). Has
    universal self-loop χ50 ≠ χ75 (R331). Future dispatcher: sub-branches
    χ75 = B and χ75 = C, each requiring new conditional exclusion lemmas
    (analogous to R329's pattern).
  - **χ51 ∈ {A, C}** (from χ48=B): χ51 is a layer position (3·17). Has
    universal self-loop χ34 ≠ χ51 (R331). Parallel future dispatcher.
  - **χ33 ∈ {A, C}** (from χ72=B, R325-A): layer position (3·11). Has
    universal self-loop χ22 ≠ χ33 (R324).
  - **χ42 ∈ {A, B}** (from χ72=C, R325-B): layer position (3·14). Has
    universal self-loop χ28 ≠ χ42 (R324).

  All four are layer positions ready for sub-branch refinement. R333+
  should target χ75 (highest layer index, completes χ48=A path) or
  χ33 (smaller layer, faster verification).
-/

/-- **R332 Target A — χ(48) ∈ ABC full coverage**: consumes the χ48 ∈ ABC
  disjunct and expands it into a 3-way coverage statement using R330
  (χ48=C refined chain), R331-A (χ48=A weak dispatcher), and R331-B
  (χ48=B weak dispatcher). -/
theorem bAdicEquation_3_branchII_chi48_in_ABC_full_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((χ 75 = χ 9 ∨ χ 75 = χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    ((χ 51 = χ 27 ∨ χ 51 = χ 18) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) := by
  rcases h48ABC with h48A | h48B_or_C
  · -- χ48 = A: use R331-A.
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_chi75_or_chi50_in_BC_or_ABC
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A)
  · rcases h48B_or_C with h48B | h48C
    · -- χ48 = B: use R331-B.
      exact Or.inr (Or.inl
        (bAdicEquation_3_branchII_chi48_eq9_chi51_or_chi34_in_AC_or_ABC
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B))
    · -- χ48 = C: use R330 refined chain.
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48C))

/-- **R332 Target B — Expanded χ(72)-chain with χ(48) fully integrated**:
  combines R327 χ72-chain with R332 Target A to replace the `χ48 ∈ ABC`
  terminal disjunct with the 3-way expansion. The χ72-chain no longer
  has any terminal χ48 atom — every leaf is a layer or transfer position. -/
theorem bAdicEquation_3_branchII_chi72_chain_coverage_expanded_chi48
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    (((χ 75 = χ 9 ∨ χ 75 = χ 18) ∨
        (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
      ((χ 51 = χ 27 ∨ χ 51 = χ 18) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
      ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
        (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
        (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∨
    ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
      (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∨
    ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
      (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)) := by
  have h72 :=
    bAdicEquation_3_branchII_chi72_chain_coverage
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases h72 with h48ABC | hRest
  · -- χ48 ∈ ABC: expand via Target A.
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_in_ABC_full_coverage
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48ABC)
  · -- χ33/χ22 or χ42/χ28 branches: pass through.
    exact Or.inr hRest

/-- **R332 Target C — Updated Branch II chain coverage summary**: replaces
  R328 summary's χ72-chain side with the χ48-expanded version. Refined
  χ54-chain remains unchanged. Both sides now expose all leaf positions
  as layer or transfer points; no terminal anchor-set membership atoms
  remain at the top level. -/
theorem bAdicEquation_3_branchII_chain_coverage_summary_chi48_expanded
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
     (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
     (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) ∧
    ((((χ 75 = χ 9 ∨ χ 75 = χ 18) ∨
         (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
       ((χ 51 = χ 27 ∨ χ 51 = χ 18) ∨
         (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
       ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
         (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
         (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
         (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∨
      ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
        (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∨
      ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
        (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18))) :=
  ⟨bAdicEquation_3_branchII_chi54_chain_coverage_refined
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9,
   bAdicEquation_3_branchII_chi72_chain_coverage_expanded_chi48
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-! ### §173. R333 — χ(75) terminal branch refinement (under χ48 = A path).

  R332 Target A exposed `(χ75 ∈ {B, C}) ∨ (χ50 ∈ {A, B, C})` as the
  χ48 = A coverage. The χ75 disjunct is a terminal anchor-membership
  atom. R333 refines it by adding conditional exclusions for each
  χ75 sub-branch.

  Deliverables:
  - **Target A** `χ75 = B → χ72 ≠ B` via triple (9, 72, 75).
    Strategic value: directly prunes R322's χ72 = B branch under χ75 = B.
  - **Target B** `χ75 = C → χ43 ≠ C` via triple (75, 18, 43).
    Note: χ43 is NOT a layer position; this is a transfer exclusion.
  - **Target C** `chi75_branch_refinement` packaging.
  - **Target E** `chi48_eq27_branch_expanded`: combine R331-A dispatcher
    with R333 sub-branch exclusions for a richer χ48 = A coverage.

  **Audit χ75 refinement value** (Target F):
  - χ75 = B → χ72 ≠ B: strong (interacts with R322/R325-A).
  - χ75 = C → χ43 ≠ C: weak (χ43 non-layer, no immediate hLayer impact).
  - Overall χ75 refinement is asymmetric — strong on the B side, weak
    on the C side. Future rounds (R334+) should consider χ51 (similar
    asymmetry with χ44/χ35), χ33 (R325-A entry), or χ42 (R325-B entry)
    as alternative refinement targets.
-/

/-- **R333 Target A — χ(75) = B forces χ(72) ≠ B**: under `χ 75 = χ 9`,
  the triple `(9, 72, 75)` with b=3, d=3, y=72 (9 + 3·72 = 225 = 3·75)
  forces `χ 72 ≠ χ 9`.

  Strategic: directly prunes the R322 χ72 = B left branch when χ75 = B. -/
theorem bAdicEquation_3_chi75_eq_chi9_forces_chi72_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h75 : 75 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h75_eq_9 : χ 75 = χ 9) :
    χ 72 ≠ χ 9 := by
  intro h72_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 72) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 72
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h72_eq_9.symm
  · show χ 72 = χ (72 + 3)
    rw [show (72 + 3 : ℕ) = 75 by decide]
    exact h72_eq_9.trans h75_eq_9.symm

/-- **R333 Target B — χ(75) = C forces χ(43) ≠ C**: under `χ 75 = χ 18`,
  the triple `(75, 18, 43)` with b=3, d=25, y=18 (75 + 3·18 = 129 = 3·43)
  forces `χ 43 ≠ χ 18`.

  Note: χ43 is NOT a layer position (43 ≠ 3·d); this is a transfer
  exclusion with weaker direct hLayer value than Target A. -/
theorem bAdicEquation_3_chi75_eq_chi18_forces_chi43_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h75 : 75 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h75_eq_18 : χ 75 = χ 18) :
    χ 43 ≠ χ 18 := by
  intro h43_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 25) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 25) = χ 18
    rw [show (3 * 25 : ℕ) = 75 by decide]
    exact h75_eq_18
  · show χ 18 = χ (18 + 25)
    rw [show (18 + 25 : ℕ) = 43 by decide]
    exact h43_eq_18.symm

/-- **R333 Target C — χ(75) branch refinement packaging**: package the two
  R333 conditional exclusions as an `And` of implications for χ75 = B / C.
  Parallel to R329 `chi48_branch_refinement`. -/
theorem bAdicEquation_3_branchII_chi75_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 75 = χ 9 → χ 72 ≠ χ 9) ∧
    (χ 75 = χ 18 → χ 43 ≠ χ 18) :=
  ⟨fun h75_eq_9 =>
     bAdicEquation_3_chi75_eq_chi9_forces_chi72_ne_chi9
       χ (by omega) hNoMono h75_eq_9,
   fun h75_eq_18 =>
     bAdicEquation_3_chi75_eq_chi18_forces_chi43_ne_chi18
       χ (by omega) hNoMono h75_eq_18⟩

/-- **R333 Target E — χ(48) = A expanded branch**: combines R331-A
  dispatcher with R333 sub-branch exclusions to enrich the χ48 = A
  coverage with additional forced inequalities.

  Result: under `χ 48 = χ 27`,

    `((χ75 = B ∧ χ72 ≠ B) ∨ (χ75 = C ∧ χ43 ≠ C)) ∨ (χ50 ∈ {A, B, C})`.

  Strictly stronger than R331-A: each χ75 = B/C sub-branch now carries
  an additional forced exclusion. -/
theorem bAdicEquation_3_branchII_chi48_eq27_branch_expanded
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_27 : χ 48 = χ 27) :
    ((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
     (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
    (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) := by
  have hR331A :=
    bAdicEquation_3_branchII_chi48_eq27_chi75_or_chi50_in_BC_or_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_27
  rcases hR331A with h75BC | h50ABC
  · rcases h75BC with h75B | h75C
    · -- χ75 = B: add forced χ72 ≠ B via R333 Target A.
      have h72_ne_9 :=
        bAdicEquation_3_chi75_eq_chi9_forces_chi72_ne_chi9
          χ (by omega) hNoMono h75B
      exact Or.inl (Or.inl ⟨h75B, h72_ne_9⟩)
    · -- χ75 = C: add forced χ43 ≠ C via R333 Target B.
      have h43_ne_18 :=
        bAdicEquation_3_chi75_eq_chi18_forces_chi43_ne_chi18
          χ (by omega) hNoMono h75C
      exact Or.inl (Or.inr ⟨h75C, h43_ne_18⟩)
  · -- χ50 ∈ ABC: pass through.
    exact Or.inr h50ABC

/-! ### §174. R334 — Crossed χ(48) = A / χ(72) = B coverage.

  Strategic insight: R333-A says `χ75 = B → χ72 ≠ B`. Contrapositive:
  under `χ72 = B`, the `χ75 = B` sub-branch of R331-A is impossible.
  This collapses R331-A's χ75 ∈ {B, C} disjunct to just `χ75 = C` in
  the joint context χ48 = A ∧ χ72 = B.

  Deliverables:
  - **Target A** `chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC`: the
    crossed theorem `χ48 = A ∧ χ72 = B → (χ75 = C ∧ χ43 ≠ C) ∨ χ50 ∈ ABC`.
    Strictly stronger than R331-A in this joint context: the χ75 = B
    sub-branch is eliminated via R333-A.
  - **Target C** `chi48_eq27_chi72_eq9_combined_coverage`: combine Target A
    with R325-A dispatcher (which fires on h72_eq_9) for a 2-And cross-chain
    coverage.

  **Audit χ50 / χ43 further refinement** (Target D):
  - χ50 (non-layer, R331-A fallback): always present as 4-color exhaustion
    fallback when χ75 = D (fourth color). R331-A is a *weak* dispatcher;
    elimination of χ50 disjunct would require showing χ75 cannot be D
    under χ48 = A. No direct triple gives this.
  - χ43 (non-layer, R333-B output): future triples (43, y, z) involve
    further unclassified positions. Direct refinement is low-value.
  Both fallback paths are structural and cannot be eliminated by single-
  triple analysis.
-/

/-- **R334 Target A — Crossed χ(48) = A ∧ χ(72) = B coverage**: under
  R318 Branch II 3-anchor + `IsKColoring n 4 χ` + `χ 48 = χ 27` +
  `χ 72 = χ 9`,

    `(χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨ (χ 50 ∈ {A, B, C})`.

  Mechanism: R331-A dispatcher gives `(χ75 ∈ {B, C}) ∨ (χ50 ∈ ABC)`.
  Under χ72 = B, the χ75 = B sub-branch contradicts R333-A
  (`χ75 = B → χ72 ≠ B`); R333-B handles the χ75 = C sub-branch with
  χ43 ≠ C. Strictly stronger than R333 `chi48_eq27_branch_expanded`
  in the joint context. -/
theorem bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_27 : χ 48 = χ 27)
    (h72_eq_9 : χ 72 = χ 9) :
    (χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
    (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) := by
  have hR331A :=
    bAdicEquation_3_branchII_chi48_eq27_chi75_or_chi50_in_BC_or_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_27
  rcases hR331A with h75BC | h50ABC
  · rcases h75BC with h75B | h75C
    · -- χ75 = B: R333-A forces χ72 ≠ B, contradiction with h72_eq_9.
      have h72_ne_9 :=
        bAdicEquation_3_chi75_eq_chi9_forces_chi72_ne_chi9
          χ (by omega) hNoMono h75B
      exact absurd h72_eq_9 h72_ne_9
    · -- χ75 = C: R333-B gives χ43 ≠ C.
      have h43_ne_18 :=
        bAdicEquation_3_chi75_eq_chi18_forces_chi43_ne_chi18
          χ (by omega) hNoMono h75C
      exact Or.inl ⟨h75C, h43_ne_18⟩
  · -- χ50 ∈ ABC: pass through.
    exact Or.inr h50ABC

/-- **R334 Target C — χ(48) = A ∧ χ(72) = B combined coverage**: under
  the joint hypotheses, both R334 Target A (χ75/χ50 refinement) and
  R325-A dispatcher (χ33/χ22 coverage, fires on h72_eq_9) hold
  simultaneously.

  Result: 2-And combined cross-chain coverage:
    Left side: `(χ75 = C ∧ χ43 ≠ C) ∨ χ50 ∈ ABC`.
    Right side: `(χ33 ∈ {A, C}) ∨ (χ22 ∈ ABC)`.

  This is the first cross-chain combined coverage theorem unifying the
  χ48 branch and the χ72 branch under joint hypotheses. -/
theorem bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_27 : χ 48 = χ 27)
    (h72_eq_9 : χ 72 = χ 9) :
    ((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∧
    ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
      (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_27 h72_eq_9,
   bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9⟩

/-! ### §175. R335 — χ(51) terminal branch refinement + χ48=B crossed coverage.

  Mirror R333/R334 for the χ48 = B path. R331-B gives
  `(χ51 ∈ {A, C}) ∨ (χ34 ∈ ABC)`; R335 refines the χ51 terminal atom.

  Deliverables:
  - **Target A** `χ51 = A → χ44 ≠ A` via triple (51, 27, 44).
  - **Target B** `χ51 = C → χ35 ≠ C` via triple (51, 18, 35).
  - **Target C** chi51 branch refinement packaging.
  - **Target D** chi48_eq9_branch_expanded.
  - **Target E** crossed `χ51 = C ∧ χ72 = C → χ75 ≠ C` via triple
    (72, 51, 75). Strategic value: interacts with R333 χ75=C branch.
  - **Target F** combined χ48=B ∧ χ72=C coverage using Target E.

  Notes:
  - χ44, χ35 are non-layer (44 ≠ 3·d, 35 ≠ 3·d); transfer exclusions only.
  - Target E provides the first χ48=B path crossed hook with χ72 branch.
-/

/-- **R335 Target A — χ(51) = A forces χ(44) ≠ A**: under `χ 51 = χ 27`,
  triple (51, 27, 44) with b=3, d=17, y=27 (51 + 3·27 = 132 = 3·44)
  forces `χ 44 ≠ χ 27`.

  Note: χ44 is NOT a layer position; transfer exclusion. -/
theorem bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h51 : 51 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_27 : χ 51 = χ 27) :
    χ 44 ≠ χ 27 := by
  intro h44_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 17) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 17) = χ 27
    rw [show (3 * 17 : ℕ) = 51 by decide]
    exact h51_eq_27
  · show χ 27 = χ (27 + 17)
    rw [show (27 + 17 : ℕ) = 44 by decide]
    exact h44_eq_27.symm

/-- **R335 Target B — χ(51) = C forces χ(35) ≠ C**: under `χ 51 = χ 18`,
  triple (51, 18, 35) with b=3, d=17, y=18 (51 + 3·18 = 105 = 3·35)
  forces `χ 35 ≠ χ 18`.

  Note: χ35 is NOT a layer position; transfer exclusion. -/
theorem bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h51 : 51 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18) :
    χ 35 ≠ χ 18 := by
  intro h35_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 17) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 17) = χ 18
    rw [show (3 * 17 : ℕ) = 51 by decide]
    exact h51_eq_18
  · show χ 18 = χ (18 + 17)
    rw [show (18 + 17 : ℕ) = 35 by decide]
    exact h35_eq_18.symm

/-- **R335 Target C — χ(51) branch refinement packaging**: And of the two
  R335 conditional exclusions for χ51 = A / C. Parallel to R333
  chi75_branch_refinement. -/
theorem bAdicEquation_3_branchII_chi51_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 51 = χ 27 → χ 44 ≠ χ 27) ∧
    (χ 51 = χ 18 → χ 35 ≠ χ 18) :=
  ⟨fun h51_eq_27 =>
     bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
       χ (by omega) hNoMono h51_eq_27,
   fun h51_eq_18 =>
     bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
       χ (by omega) hNoMono h51_eq_18⟩

/-- **R335 Target D — χ(48) = B expanded branch**: combines R331-B
  dispatcher with R335 sub-branch exclusions to enrich the χ48 = B
  coverage. Parallel to R333 chi48_eq27_branch_expanded.

  Result: under `χ 48 = χ 9`,

    `((χ51 = A ∧ χ44 ≠ A) ∨ (χ51 = C ∧ χ35 ≠ C)) ∨ (χ34 ∈ {A, B, C})`. -/
theorem bAdicEquation_3_branchII_chi48_eq9_branch_expanded
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) := by
  have hR331B :=
    bAdicEquation_3_branchII_chi48_eq9_chi51_or_chi34_in_AC_or_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  rcases hR331B with h51AC | h34ABC
  · rcases h51AC with h51A | h51C
    · -- χ51 = A: add forced χ44 ≠ A via Target A.
      have h44_ne_27 :=
        bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
          χ (by omega) hNoMono h51A
      exact Or.inl (Or.inl ⟨h51A, h44_ne_27⟩)
    · -- χ51 = C: add forced χ35 ≠ C via Target B.
      have h35_ne_18 :=
        bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
          χ (by omega) hNoMono h51C
      exact Or.inl (Or.inr ⟨h51C, h35_ne_18⟩)
  · -- χ34 ∈ ABC: pass through.
    exact Or.inr h34ABC

/-- **R335 Target E — Crossed χ(51) = C ∧ χ(72) = C forces χ(75) ≠ C**:
  via triple (72, 51, 75) with b=3, d=24, y=51 (72 + 3·51 = 225 = 3·75).
  Under `χ 51 = χ 18 ∧ χ 72 = χ 18`, both first conjuncts of the rado
  constraint hold; assuming `χ 75 = χ 18` triggers monochromatic solution.

  Strategic value: provides a cross-chain hook for χ48 = B path that
  interacts with R333 χ75 = C branch. -/
theorem bAdicEquation_3_chi51_eq_chi18_chi72_eq_chi18_forces_chi75_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h75 : 75 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18)
    (h72_eq_18 : χ 72 = χ 18) :
    χ 75 ≠ χ 18 := by
  intro h75_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 24) (y := 51) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 24) = χ 51
    rw [show (3 * 24 : ℕ) = 72 by decide]
    exact h72_eq_18.trans h51_eq_18.symm
  · show χ 51 = χ (51 + 24)
    rw [show (51 + 24 : ℕ) = 75 by decide]
    exact h51_eq_18.trans h75_eq_18.symm

/-- **R335 Target F — Combined χ(48) = B ∧ χ(72) = C coverage**:
  enriches R335 Target D in the joint context `χ48 = B ∧ χ72 = C`
  by adding `χ 75 ≠ χ 18` to the χ51 = C sub-branch via Target E.

  Result: under joint hypotheses,
    `((χ51 = A ∧ χ44 ≠ A) ∨ (χ51 = C ∧ χ35 ≠ C ∧ χ75 ≠ C)) ∨ χ34 ∈ ABC`.

  Parallel to R334 crossed coverage on the χ48 = B side. -/
theorem bAdicEquation_3_branchII_chi48_eq9_chi72_eq18_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h72_eq_18 : χ 72 = χ 18) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) := by
  have hR331B :=
    bAdicEquation_3_branchII_chi48_eq9_chi51_or_chi34_in_AC_or_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  rcases hR331B with h51AC | h34ABC
  · rcases h51AC with h51A | h51C
    · -- χ51 = A: same as Target D.
      have h44_ne_27 :=
        bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
          χ (by omega) hNoMono h51A
      exact Or.inl (Or.inl ⟨h51A, h44_ne_27⟩)
    · -- χ51 = C: now also add χ75 ≠ C via Target E (uses h72_eq_18).
      have h35_ne_18 :=
        bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
          χ (by omega) hNoMono h51C
      have h75_ne_18 :=
        bAdicEquation_3_chi51_eq_chi18_chi72_eq_chi18_forces_chi75_ne_chi18
          χ (by omega) hNoMono h51C h72_eq_18
      exact Or.inl (Or.inr ⟨h51C, h35_ne_18, h75_ne_18⟩)
  · -- χ34 ∈ ABC: pass through.
    exact Or.inr h34ABC

/-! ### §176. R336 — Crossed χ(72) sub-branch / χ(48) ∈ ABC expansions.

  Integrate the cross-chain theorems from R334/R335 (and the independent
  expansions from R333/R335) into branch-specific summary theorems under
  joint χ72 ∈ {B, C} sub-branches.

  Deliverables:
  - **Target A** `chi72_eq9_chi48ABC_crossed_expansion`: under χ72 = B
    and χ48 ∈ ABC, dispatch through 3 χ48 sub-cases:
    * χ48 = A: R334 crossed (χ75 = B sub-branch eliminated);
    * χ48 = B: R335-D expanded (no extra χ72=B hook);
    * χ48 = C: R330 refined chain.
  - **Target B** `chi72_eq18_chi48ABC_crossed_expansion`: under χ72 = C
    and χ48 ∈ ABC:
    * χ48 = A: R333-E expanded (χ72 = C makes χ72 ≠ B trivial);
    * χ48 = B: R335-F combined (χ51 = C adds χ75 ≠ C hook);
    * χ48 = C: R330 refined chain.
  - **Target C** `chi72_eq9_chi48ABC_crossed_with_chi33_coverage`:
    Target A ∧ R325-A χ33/χ22 dispatcher.
  - **Target D** `chi72_eq18_chi48ABC_crossed_with_chi42_coverage`:
    Target B ∧ R325-B χ42/χ28 dispatcher.

  These reusable theorems form the cross-chain coverage layer that
  consumes R325 (χ72 sub-branch) + R331/R333/R335 (χ48 sub-branch
  refinements) in one shot.

  **Next refinement target audit** (for R337+): χ33 ∈ {A, C} and
  χ42 ∈ {A, B} are layer positions arising from R325-A/B; both have
  universal self-loops (χ22 ≠ χ33 from R324, χ28 ≠ χ42 from R324).
  Either is a viable next refinement target with the R333/R335 pattern.
-/

/-- **R336 Target A — χ(72) = B crossed expansion over χ(48) ∈ ABC**:
  combines R334 crossed (χ48=A) + R335-D expanded (χ48=B) + R330 refined
  chain (χ48=C) for the χ72 = B context. -/
theorem bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) := by
  rcases h48ABC with h48A | h48BC
  · -- χ48 = A: use R334 crossed (χ75=B sub-branch eliminated under χ72=B).
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A h72_eq_9)
  · rcases h48BC with h48B | h48C
    · -- χ48 = B: use R335-D expanded (no extra χ72=B hook).
      exact Or.inr (Or.inl
        (bAdicEquation_3_branchII_chi48_eq9_branch_expanded
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B))
    · -- χ48 = C: use R330 refined chain.
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48C))

/-- **R336 Target B — χ(72) = C crossed expansion over χ(48) ∈ ABC**:
  combines R333-E expanded (χ48=A) + R335-F combined (χ48=B, adds χ75≠C
  hook in χ51=C sub-branch) + R330 refined chain (χ48=C) under χ72 = C. -/
theorem bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
       (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) := by
  rcases h48ABC with h48A | h48BC
  · -- χ48 = A: use R333-E expanded (no extra χ72=C hook beyond independence).
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_branch_expanded
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A)
  · rcases h48BC with h48B | h48C
    · -- χ48 = B: use R335-F combined (adds χ75 ≠ C hook in χ51 = C).
      exact Or.inr (Or.inl
        (bAdicEquation_3_branchII_chi48_eq9_chi72_eq18_combined_coverage
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B h72_eq_18))
    · -- χ48 = C: use R330 refined chain.
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48C))

/-- **R336 Target C — χ(72) = B crossed expansion combined with χ33/χ22 coverage**:
  pair Target A with R325-A dispatcher. The χ72 = B sub-branch fires both
  the χ48 ABC expansion and the χ33 ∈ {A,C} ∨ χ22 ∈ ABC dispatcher. -/
theorem bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_with_chi33_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
        (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
      ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
        (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
        (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∧
    ((χ 33 = χ 27 ∨ χ 33 = χ 18) ∨
      (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_expansion
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9 h48ABC,
   bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9⟩

/-- **R336 Target D — χ(72) = C crossed expansion combined with χ42/χ28 coverage**:
  pair Target B with R325-B dispatcher. -/
theorem bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_with_chi42_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
        (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
       (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
      ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
        (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
        (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∧
    ((χ 42 = χ 27 ∨ χ 42 = χ 9) ∨
      (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_expansion
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18 h48ABC,
   bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18⟩

/-! ### §177. R337 — χ(33) and χ(42) terminal branch refinements.

  Refine the two layer-position terminal atoms from R325 dispatchers:
  - χ33 ∈ {A, C} (from R325-A, χ72 = B branch);
  - χ42 ∈ {A, B} (from R325-B, χ72 = C branch).

  Deliverables:
  - **Target A** `χ33 = A → χ38 ≠ A` via triple (33, 27, 38).
  - **Target B** `χ33 = C → χ29 ≠ C` via triple (33, 18, 29).
  - **Target C** `chi33_branch_refinement` packaging.
  - **Target D** `chi72_eq9_branch_expanded_chi33`: enrich R325-A with χ33
    sub-branch exclusions.
  - **Target F-1** `χ42 = A → χ41 ≠ A` via triple (42, 27, 41).
  - **Target F-2** `χ42 = B → χ23 ≠ B` via triple (42, 9, 23).
  - **Target F-3** `chi42_branch_refinement` packaging.
  - **Target F-4** `chi72_eq18_branch_expanded_chi42`: enrich R325-B with χ42
    sub-branch exclusions.

  Notes: χ38, χ29, χ41, χ23 are all NON-layer positions; transfer exclusions only.

  **Audit cross-chain hooks for χ33** (Target E):
  - **(51, 33, 50)**: 51 + 3·33 = 150 = 3·50. Under χ51 = X ∧ χ33 = X
    forces χ50 ≠ X. Potential cross-chain hook with R331-B / R335
    (χ51 ∈ {A, C}) and R325-A (χ33 ∈ {A, C}): if both terminals fire same
    color (A or C), χ50 is forced. χ50 is the R331-A fallback (transfer);
    moderate value.
  - **(75, 33, 58)**: 75 + 3·33 = 174 = 3·58. Under χ75 = X ∧ χ33 = X
    forces χ58 ≠ X. χ58 non-layer; low value.
  - **(33, 42, 53)**: 33 + 3·42 = 159 = 3·53. Under χ33 = X ∧ χ42 = X
    forces χ53 ≠ X. χ53 non-layer; low value.

  R338+ may pursue (51, 33, 50) cross-chain integration if useful.
-/

/-- **R337 Target A — χ(33) = A forces χ(38) ≠ A**: under `χ 33 = χ 27`,
  triple (33, 27, 38) with b=3, d=11, y=27 (33 + 3·27 = 114 = 3·38)
  forces `χ 38 ≠ χ 27`. -/
theorem bAdicEquation_3_chi33_eq_chi27_forces_chi38_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h38 : 38 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h33_eq_27 : χ 33 = χ 27) :
    χ 38 ≠ χ 27 := by
  intro h38_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 11) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 11) = χ 27
    rw [show (3 * 11 : ℕ) = 33 by decide]
    exact h33_eq_27
  · show χ 27 = χ (27 + 11)
    rw [show (27 + 11 : ℕ) = 38 by decide]
    exact h38_eq_27.symm

/-- **R337 Target B — χ(33) = C forces χ(29) ≠ C**: under `χ 33 = χ 18`,
  triple (33, 18, 29) with b=3, d=11, y=18 (33 + 3·18 = 87 = 3·29)
  forces `χ 29 ≠ χ 18`. -/
theorem bAdicEquation_3_chi33_eq_chi18_forces_chi29_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h33 : 33 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h33_eq_18 : χ 33 = χ 18) :
    χ 29 ≠ χ 18 := by
  intro h29_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 11) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 11) = χ 18
    rw [show (3 * 11 : ℕ) = 33 by decide]
    exact h33_eq_18
  · show χ 18 = χ (18 + 11)
    rw [show (18 + 11 : ℕ) = 29 by decide]
    exact h29_eq_18.symm

/-- **R337 Target C — χ(33) branch refinement packaging**: And of R337 Target A/B
  conditional exclusions. Parallel to R333 chi75_branch_refinement / R335 chi51. -/
theorem bAdicEquation_3_branchII_chi33_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 33 = χ 27 → χ 38 ≠ χ 27) ∧
    (χ 33 = χ 18 → χ 29 ≠ χ 18) :=
  ⟨fun h33_eq_27 =>
     bAdicEquation_3_chi33_eq_chi27_forces_chi38_ne_chi27
       χ (by omega) hNoMono h33_eq_27,
   fun h33_eq_18 =>
     bAdicEquation_3_chi33_eq_chi18_forces_chi29_ne_chi18
       χ (by omega) hNoMono h33_eq_18⟩

/-- **R337 Target D — χ(72) = B branch expanded via χ(33)**: combines R325-A
  dispatcher with R337 Target A/B exclusions. Under `χ 72 = χ 9`,

    `((χ33 = A ∧ χ38 ≠ A) ∨ (χ33 = C ∧ χ29 ≠ C)) ∨ χ22 ∈ ABC`.

  Parallel to R333 chi48_eq27_branch_expanded / R335-D. -/
theorem bAdicEquation_3_branchII_chi72_eq9_branch_expanded_chi33
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_9 : χ 72 = χ 9) :
    ((χ 33 = χ 27 ∧ χ 38 ≠ χ 27) ∨
     (χ 33 = χ 18 ∧ χ 29 ≠ χ 18)) ∨
    (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) := by
  have hR325A :=
    bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9
  rcases hR325A with h33AC | h22ABC
  · rcases h33AC with h33A | h33C
    · -- χ33 = A: add forced χ38 ≠ A via Target A.
      have h38_ne_27 :=
        bAdicEquation_3_chi33_eq_chi27_forces_chi38_ne_chi27
          χ (by omega) hNoMono h33A
      exact Or.inl (Or.inl ⟨h33A, h38_ne_27⟩)
    · -- χ33 = C: add forced χ29 ≠ C via Target B.
      have h29_ne_18 :=
        bAdicEquation_3_chi33_eq_chi18_forces_chi29_ne_chi18
          χ (by omega) hNoMono h33C
      exact Or.inl (Or.inr ⟨h33C, h29_ne_18⟩)
  · -- χ22 ∈ ABC: pass through.
    exact Or.inr h22ABC

/-- **R337 Target F-1 — χ(42) = A forces χ(41) ≠ A**: under `χ 42 = χ 27`,
  triple (42, 27, 41) with b=3, d=14, y=27 (42 + 3·27 = 123 = 3·41)
  forces `χ 41 ≠ χ 27`. -/
theorem bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_27 : χ 42 = χ 27) :
    χ 41 ≠ χ 27 := by
  intro h41_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 27
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_27
  · show χ 27 = χ (27 + 14)
    rw [show (27 + 14 : ℕ) = 41 by decide]
    exact h41_eq_27.symm

/-- **R337 Target F-2 — χ(42) = B forces χ(23) ≠ B**: under `χ 42 = χ 9`,
  triple (42, 9, 23) with b=3, d=14, y=9 (42 + 3·9 = 69 = 3·23)
  forces `χ 23 ≠ χ 9`. -/
theorem bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_9 : χ 42 = χ 9) :
    χ 23 ≠ χ 9 := by
  intro h23_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 9
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_9
  · show χ 9 = χ (9 + 14)
    rw [show (9 + 14 : ℕ) = 23 by decide]
    exact h23_eq_9.symm

/-- **R337 Target F-3 — χ(42) branch refinement packaging**: And of F-1/F-2. -/
theorem bAdicEquation_3_branchII_chi42_branch_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 42 = χ 27 → χ 41 ≠ χ 27) ∧
    (χ 42 = χ 9  → χ 23 ≠ χ 9) :=
  ⟨fun h42_eq_27 =>
     bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
       χ (by omega) hNoMono h42_eq_27,
   fun h42_eq_9 =>
     bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
       χ (by omega) hNoMono h42_eq_9⟩

/-- **R337 Target F-4 — χ(72) = C branch expanded via χ(42)**: combines R325-B
  dispatcher with R337 F-1/F-2 exclusions. Under `χ 72 = χ 18`,

    `((χ42 = A ∧ χ41 ≠ A) ∨ (χ42 = B ∧ χ23 ≠ B)) ∨ χ28 ∈ ABC`. -/
theorem bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18) :
    ((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
     (χ 42 = χ 9 ∧ χ 23 ≠ χ 9)) ∨
    (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) := by
  have hR325B :=
    bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18
  rcases hR325B with h42AB | h28ABC
  · rcases h42AB with h42A | h42B
    · -- χ42 = A: add forced χ41 ≠ A via F-1.
      have h41_ne_27 :=
        bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
          χ (by omega) hNoMono h42A
      exact Or.inl (Or.inl ⟨h42A, h41_ne_27⟩)
    · -- χ42 = B: add forced χ23 ≠ B via F-2.
      have h23_ne_9 :=
        bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
          χ (by omega) hNoMono h42B
      exact Or.inl (Or.inr ⟨h42B, h23_ne_9⟩)
  · -- χ28 ∈ ABC: pass through.
    exact Or.inr h28ABC

/-! ### §178. R338 — R337 χ(33)/χ(42) expansions integrated into R336 summaries.

  R336 Target C / D paired R336 crossed χ48 expansion with R325-A / R325-B
  dispatchers (giving raw χ33/χ22 / χ42/χ28 coverage). R338 replaces the
  R325 side with R337 expansions (which add forced exclusions to the χ33/χ42
  sub-branches).

  Deliverables:
  - **Target A** `chi72_eq9_chi48ABC_crossed_with_chi33_expanded`: upgrade of
    R336 Target C. R325-A side replaced with R337 chi33-expanded.
  - **Target B** `chi72_eq18_chi48ABC_crossed_with_chi42_expanded`: upgrade of
    R336 Target D. R325-B side replaced with R337 chi42-expanded.

  **Audit remaining terminal types** (Target D, for R339+):
  After R338, the R336 summaries contain the following terminal atoms:
  - χ75 sub-branches (B/C with conditional exclusions) — R333 refined
  - χ50 ∈ ABC — R331-A transfer fallback, no further single-triple refinement
  - χ51 sub-branches (A/C with conditional exclusions) — R335 refined
  - χ34 ∈ ABC — R331-B transfer fallback, no further refinement
  - χ36/χ24/χ16 refined chain — R330 (already strongest)
  - χ33 sub-branches (A/C with conditional exclusions) — R337 refined
  - χ22 ∈ ABC — R325-A transfer fallback
  - χ42 sub-branches (A/B with conditional exclusions) — R337 refined
  - χ28 ∈ ABC — R325-B transfer fallback

  Most "transfer ∈ ABC" terminals (χ50, χ34, χ22, χ28) are structural
  4-color fallbacks, not direct hLayer atoms. The (51, 33, 50) cross-chain
  hook (noted in R337 audit) is the most promising next step.
-/

/-- **R338 Target A — χ(72) = B summary upgraded with χ(33) expansion**:
  pair R336 chi48 crossed expansion with R337 chi33 expanded.

  Result: under joint χ72 = B ∧ χ48 ∈ ABC, the crossed χ48 expansion AND
  the (R337-strengthened) χ33 expansion both hold. -/
theorem bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_with_chi33_expanded
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
        (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
      ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
        (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
        (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∧
    (((χ 33 = χ 27 ∧ χ 38 ≠ χ 27) ∨
       (χ 33 = χ 18 ∧ χ 29 ≠ χ 18)) ∨
      (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_expansion
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9 h48ABC,
   bAdicEquation_3_branchII_chi72_eq9_branch_expanded_chi33
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9⟩

/-- **R338 Target B — χ(72) = C summary upgraded with χ(42) expansion**:
  pair R336 chi48 crossed expansion with R337 chi42 expanded.

  Result: under joint χ72 = C ∧ χ48 ∈ ABC, the crossed χ48 expansion AND
  the (R337-strengthened) χ42 expansion both hold. -/
theorem bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_with_chi42_expanded
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
        (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
       (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
      ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
        (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
        (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18))) ∧
    (((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
       (χ 42 = χ 9 ∧ χ 23 ≠ χ 9)) ∨
      (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_expansion
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18 h48ABC,
   bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18⟩

/-! ### §179. R339 — First double-terminal cross-chain lemma (χ51 / χ33 / χ50).

  R337 audit identified triple (51, 33, 50) as the highest-value cross-chain
  candidate. It links:
  - χ51 (R331-B / R335 terminal of χ48 = B path),
  - χ33 (R325-A / R337 terminal of χ72 = B path),
  - χ50 (R331-A transfer fallback of χ48 = A path).

  Arithmetic: 51 + 3·33 = 51 + 99 = 150 = 3·50.
  Rado constraint: ¬(χ51 = χ33 ∧ χ33 = χ50). When χ51 and χ33 share a color X,
  any χ50 = X creates a monochromatic solution.

  Deliverables:
  - **Target A** `χ51 = A ∧ χ33 = A → χ50 ≠ A`.
  - **Target B** `χ51 = C ∧ χ33 = C → χ50 ≠ C`.
  - **Target C** `chi51_chi33_cross_refinement` packaging.
  - **Target D** specialized to χ48 = B ∧ χ72 = B context (semantic alias).
  - **Optional E** χ50 ∈ ABC refinements under same-color χ51/χ33.

  **Audit next cross-chain candidates** (Target F, for R340+):
  - **(54, 33, 51)**: 54 + 3·33 = 153 = 3·51. Three-chain bridge linking
    χ54 (R321/R326), χ33 (R325-A/R337), χ51 (R331-B/R335). Highest priority.
  - **(75, 33, 58)**: 75 + 3·33 = 174 = 3·58. χ58 non-layer; lower value.
  - **(51, 42, 59)**: 51 + 3·42 = 177 = 3·59. χ59 non-layer; lower value.
  - **(75, 42, 67)**: 75 + 3·42 = 201 = 3·67. χ67 non-layer; lower value.
-/

/-- **R339 Target A — Cross-chain `χ51 = A ∧ χ33 = A → χ50 ≠ A`**:
  via triple (51, 33, 50) with b=3, d=17, y=33 (51 + 3·33 = 150 = 3·50).
  Under χ51 = χ27 = χ33, the first conjunct of the rado constraint holds;
  assuming χ50 = χ27 triggers the second conjunct and forces a mono solution. -/
theorem bAdicEquation_3_chi51_eq_chi27_chi33_eq_chi27_forces_chi50_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h51 : 51 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_27 : χ 51 = χ 27)
    (h33_eq_27 : χ 33 = χ 27) :
    χ 50 ≠ χ 27 := by
  intro h50_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 17) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 17) = χ 33
    rw [show (3 * 17 : ℕ) = 51 by decide]
    exact h51_eq_27.trans h33_eq_27.symm
  · show χ 33 = χ (33 + 17)
    rw [show (33 + 17 : ℕ) = 50 by decide]
    exact h33_eq_27.trans h50_eq_27.symm

/-- **R339 Target B — Cross-chain `χ51 = C ∧ χ33 = C → χ50 ≠ C`**:
  via same triple (51, 33, 50). Parallel to Target A with anchor C. -/
theorem bAdicEquation_3_chi51_eq_chi18_chi33_eq_chi18_forces_chi50_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h51 : 51 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18)
    (h33_eq_18 : χ 33 = χ 18) :
    χ 50 ≠ χ 18 := by
  intro h50_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 17) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 17) = χ 33
    rw [show (3 * 17 : ℕ) = 51 by decide]
    exact h51_eq_18.trans h33_eq_18.symm
  · show χ 33 = χ (33 + 17)
    rw [show (33 + 17 : ℕ) = 50 by decide]
    exact h33_eq_18.trans h50_eq_18.symm

/-- **R339 Target C — χ51/χ33/χ50 cross refinement packaging**: And of
  Target A and Target B as implications. Reusable bridge between χ48 = B
  and χ72 = B chains. -/
theorem bAdicEquation_3_branchII_chi51_chi33_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 51 = χ 27 → χ 33 = χ 27 → χ 50 ≠ χ 27) ∧
    (χ 51 = χ 18 → χ 33 = χ 18 → χ 50 ≠ χ 18) :=
  ⟨fun h51_eq_27 h33_eq_27 =>
     bAdicEquation_3_chi51_eq_chi27_chi33_eq_chi27_forces_chi50_ne_chi27
       χ (by omega) hNoMono h51_eq_27 h33_eq_27,
   fun h51_eq_18 h33_eq_18 =>
     bAdicEquation_3_chi51_eq_chi18_chi33_eq_chi18_forces_chi50_ne_chi18
       χ (by omega) hNoMono h51_eq_18 h33_eq_18⟩

/-- **R339 Target D — Specialized χ51/χ33 cross under χ48 = B ∧ χ72 = B**:
  semantic alias of Target C tied to the joint context. Future consumers
  in the χ48 = B ∧ χ72 = B path can call this directly. -/
theorem bAdicEquation_3_branchII_chi48_eq9_chi72_eq9_same_terminal_cross
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h48_eq_9 : χ 48 = χ 9)
    (_h72_eq_9 : χ 72 = χ 9) :
    (χ 51 = χ 27 → χ 33 = χ 27 → χ 50 ≠ χ 27) ∧
    (χ 51 = χ 18 → χ 33 = χ 18 → χ 50 ≠ χ 18) :=
  bAdicEquation_3_branchII_chi51_chi33_cross_refinement
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9

/-- **R339 Target E-1 — χ50 ∈ ABC refinement under χ51 = A ∧ χ33 = A**:
  combine R339 Target A with χ50 ∈ ABC to narrow to χ50 ∈ {B, C}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi51A_chi33A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_27 : χ 51 = χ 27)
    (h33_eq_27 : χ 33 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 ∨ χ 50 = χ 18 := by
  have h50_ne_27 :=
    bAdicEquation_3_chi51_eq_chi27_chi33_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h51_eq_27 h33_eq_27
  rcases h50ABC with h50A | h50B_or_C
  · exact absurd h50A h50_ne_27
  · exact h50B_or_C

/-- **R339 Target E-2 — χ50 ∈ ABC refinement under χ51 = C ∧ χ33 = C**:
  combine R339 Target B with χ50 ∈ ABC to narrow to χ50 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi51C_chi33C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18)
    (h33_eq_18 : χ 33 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 9 := by
  have h50_ne_18 :=
    bAdicEquation_3_chi51_eq_chi18_chi33_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h51_eq_18 h33_eq_18
  rcases h50ABC with h50A | h50B_or_C
  · exact Or.inl h50A
  · rcases h50B_or_C with h50B | h50C
    · exact Or.inr h50B
    · exact absurd h50C h50_ne_18

/-! ### §180. R340 — Three-chain cross lemma (χ54, χ33, χ51).

  Triple (54, 33, 51): 54 + 3·33 = 153 = 3·51. Bridges three main chains:
  - χ54 from χ54-chain (R321, R326);
  - χ33 from χ72-chain (R325-A, R337);
  - χ51 from χ48 = B branch (R331-B, R335).

  Rado constraint ¬(χ54 = χ33 ∧ χ33 = χ51): when χ54 and χ33 share color X,
  χ51 = X triggers monochromatic solution.

  Deliverables:
  - **Target A** `χ54 = C ∧ χ33 = C → χ51 ≠ C` — primary value.
  - **Target B** `χ54 = A ∧ χ33 = A → χ51 ≠ A` — Branch II has χ54 ≠ A,
    so generic but lower utility.
  - **Target C** `χ54 = B ∧ χ33 = B → χ51 ≠ B` — generic.
  - **Target D** `chi54_chi33_chi51_cross_refinement` packaging A/B/C.
  - **Target E** `chi51AC_refine_of_chi54C_chi33C`: refine χ51 ∈ {A, C} to
    χ51 = A using Target A.
  - **Target G** `chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch`:
    practical branch pruning under χ48 = B ∧ χ54 = C ∧ χ33 = C — eliminates
    the χ51 = C sub-branch of R335-D, yielding tighter coverage.

  This is the first three-chain bridge linking χ54-chain, χ72-chain, and
  χ48 = B branch via a single triple.
-/

/-- **R340 Target A — `χ54 = C ∧ χ33 = C → χ51 ≠ C`**: via triple (54, 33, 51)
  with b=3, d=18, y=33 (54 + 3·33 = 153 = 3·51). Under χ54 = χ18 = χ33,
  rado constraint's first conjunct holds; assuming χ51 = χ18 triggers
  mono solution. -/
theorem bAdicEquation_3_chi54_eq_chi18_chi33_eq_chi18_forces_chi51_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18)
    (h33_eq_18 : χ 33 = χ 18) :
    χ 51 ≠ χ 18 := by
  intro h51_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 33
    rw [show (3 * 18 : ℕ) = 54 by decide]
    exact h54_eq_18.trans h33_eq_18.symm
  · show χ 33 = χ (33 + 18)
    rw [show (33 + 18 : ℕ) = 51 by decide]
    exact h33_eq_18.trans h51_eq_18.symm

/-- **R340 Target B — `χ54 = A ∧ χ33 = A → χ51 ≠ A`**: parallel to Target A
  for anchor A. Branch II has χ54 ≠ A globally, so this is a generic
  cross lemma for completeness. -/
theorem bAdicEquation_3_chi54_eq_chi27_chi33_eq_chi27_forces_chi51_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_27 : χ 54 = χ 27)
    (h33_eq_27 : χ 33 = χ 27) :
    χ 51 ≠ χ 27 := by
  intro h51_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 33
    rw [show (3 * 18 : ℕ) = 54 by decide]
    exact h54_eq_27.trans h33_eq_27.symm
  · show χ 33 = χ (33 + 18)
    rw [show (33 + 18 : ℕ) = 51 by decide]
    exact h33_eq_27.trans h51_eq_27.symm

/-- **R340 Target C — `χ54 = B ∧ χ33 = B → χ51 ≠ B`**: parallel for anchor B. -/
theorem bAdicEquation_3_chi54_eq_chi9_chi33_eq_chi9_forces_chi51_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_9 : χ 54 = χ 9)
    (h33_eq_9 : χ 33 = χ 9) :
    χ 51 ≠ χ 9 := by
  intro h51_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 33) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 33
    rw [show (3 * 18 : ℕ) = 54 by decide]
    exact h54_eq_9.trans h33_eq_9.symm
  · show χ 33 = χ (33 + 18)
    rw [show (33 + 18 : ℕ) = 51 by decide]
    exact h33_eq_9.trans h51_eq_9.symm

/-- **R340 Target D — Three-chain cross refinement packaging**: And of A/B/C
  color same-color exclusions for χ54/χ33/χ51 cross-chain triple. -/
theorem bAdicEquation_3_branchII_chi54_chi33_chi51_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 54 = χ 27 → χ 33 = χ 27 → χ 51 ≠ χ 27) ∧
    (χ 54 = χ 9  → χ 33 = χ 9  → χ 51 ≠ χ 9) ∧
    (χ 54 = χ 18 → χ 33 = χ 18 → χ 51 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h54_eq_27 h33_eq_27
    exact bAdicEquation_3_chi54_eq_chi27_chi33_eq_chi27_forces_chi51_ne_chi27
      χ (by omega) hNoMono h54_eq_27 h33_eq_27
  · intro h54_eq_9 h33_eq_9
    exact bAdicEquation_3_chi54_eq_chi9_chi33_eq_chi9_forces_chi51_ne_chi9
      χ (by omega) hNoMono h54_eq_9 h33_eq_9
  · intro h54_eq_18 h33_eq_18
    exact bAdicEquation_3_chi54_eq_chi18_chi33_eq_chi18_forces_chi51_ne_chi18
      χ (by omega) hNoMono h54_eq_18 h33_eq_18

/-- **R340 Target E — χ51 ∈ {A, C} refinement under χ54 = C ∧ χ33 = C**:
  under same-color (C) at χ54 and χ33, the χ51 = C sub-branch from R331-B
  is eliminated, forcing χ51 = A. -/
theorem bAdicEquation_3_branchII_chi51AC_refine_of_chi54C_chi33C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18)
    (h33_eq_18 : χ 33 = χ 18)
    (h51AC : χ 51 = χ 27 ∨ χ 51 = χ 18) :
    χ 51 = χ 27 := by
  have h51_ne_18 :=
    bAdicEquation_3_chi54_eq_chi18_chi33_eq_chi18_forces_chi51_ne_chi18
      χ (by omega) hNoMono h54_eq_18 h33_eq_18
  rcases h51AC with h51A | h51C
  · exact h51A
  · exact absurd h51C h51_ne_18

/-- **R340 Target G — Practical branch pruning under χ48 = B ∧ χ54 = C ∧ χ33 = C**:
  combines R335-D `chi48_eq9_branch_expanded` with R340 Target A.
  The χ51 = C sub-branch of R335-D is eliminated since R340-A forces χ51 ≠ C.

  Result: only `χ51 = A ∧ χ44 ≠ A` survives (with χ34 ∈ ABC fallback). -/
theorem bAdicEquation_3_branchII_chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h33_eq_18 : χ 33 = χ 18) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) := by
  have hR335D :=
    bAdicEquation_3_branchII_chi48_eq9_branch_expanded
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  have h51_ne_18 :=
    bAdicEquation_3_chi54_eq_chi18_chi33_eq_chi18_forces_chi51_ne_chi18
      χ (by omega) hNoMono h54_eq_18 h33_eq_18
  rcases hR335D with h51AC | h34ABC
  · rcases h51AC with h51A | h51C
    · -- χ51 = A ∧ χ44 ≠ A: preserved.
      exact Or.inl h51A
    · -- χ51 = C ∧ χ35 ≠ C: contradicts R340-A which gives χ51 ≠ C.
      exact absurd h51C.1 h51_ne_18
  · -- χ34 ∈ ABC: pass through.
    exact Or.inr h34ABC

/-! ### §181. R341 — Triple-context Branch II combined coverage (χ54=C ∧ χ72=B ∧ χ48=B).

  R340 Target G `chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch` shows
  that under χ48=B ∧ χ54=C ∧ χ33=C, the χ51=C sub-branch of R335-D is
  eliminated. R341 integrates this into the broader triple-context
  (χ54=C ∧ χ72=B ∧ χ48=B), exploiting R337-D dispatcher on χ33.

  Deliverables:
  - **Target A** `chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage`: full
    3-way combined theorem with χ33 cases (A / C / χ22∈ABC) cross-applied
    to χ51 coverage (R335-D full or R340-G pruned in χ33=C case).

  **Audit χ54=B value** (Target D-equivalent):
  R326-B handles χ54=B with χ36/χ24 dispatch, not χ33. R340's B-color
  variant `χ54=B ∧ χ33=B → χ51≠B` requires χ33=B, but under χ72=B
  (R325-A) χ33 terminal is {A, C}, never B. So χ54=B does not benefit
  from R340 in the natural χ72=B context. Low priority.

  **Audit R338 summary integration**:
  R340 applies only inside the joint χ54=C ∧ χ72=B ∧ χ48=B ∧ χ33=C
  context. R338 summary's χ48 dispatch is parameterized only by χ48
  membership, not χ54. Inserting R340 into R338 requires a χ54=C-aware
  parameter; that creates a parallel χ54-parameterized summary, not an
  upgrade to R338 itself. Best handled as a separate R341+ theorem.
-/

/-- **R341 Target A — Triple-context combined coverage**: under R318 Branch II
  3-anchor + IsKColoring n 4 χ + `χ54 = C ∧ χ72 = B ∧ χ48 = B`, the χ33
  dispatch from R337-D is integrated with χ51 coverage from R335-D. In the
  χ33=C sub-case, R340-G prunes the χ51=C sub-branch.

  Result: 3-disjunct (over χ33 cases), each carrying the appropriate χ51
  coverage. -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 33 = χ 27 ∧ χ 38 ≠ χ 27 ∧
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
    (χ 33 = χ 18 ∧ χ 29 ≠ χ 18 ∧
      ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
    ((χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) ∧
      (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
         (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
        (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) := by
  have h33_exp :=
    bAdicEquation_3_branchII_chi72_eq9_branch_expanded_chi33
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9
  have h51_exp :=
    bAdicEquation_3_branchII_chi48_eq9_branch_expanded
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  rcases h33_exp with h33AC | h22ABC
  · rcases h33AC with h33A | h33C
    · -- χ33 = A: preserve full R335-D for χ51.
      exact Or.inl ⟨h33A.1, h33A.2, h51_exp⟩
    · -- χ33 = C: use R340-G to prune χ51=C sub-branch from R335-D.
      have hPruned :=
        bAdicEquation_3_branchII_chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9 h54_eq_18 h33C.1
      exact Or.inr (Or.inl ⟨h33C.1, h33C.2, hPruned⟩)
  · -- χ22 ∈ ABC: preserve full R335-D for χ51.
    exact Or.inr (Or.inr ⟨h22ABC, h51_exp⟩)

/-! ### §182. R342 — Exploit χ(48)=C / χ(54)=C incompatibility.

  R329 already established `χ48 = C → χ54 ≠ C` (triple (18, 48, 54)). R342
  exploits this via direct contradiction theorems and uses it to prune the
  χ48=C case from coverages under χ54=C.

  Deliverables:
  - **Target A** `chi48_eq18_and_chi54_eq18_false`: direct contradiction
    from R329.
  - **Target B** `chi54_eq18_chi48ABC_refined_no_chi48C`: under χ54=C
    and χ48 ∈ ABC, χ48=C eliminated; only R333-E (χ48=A) and R335-D
    (χ48=B) branches remain.
  - **Target C** `chi54_eq18_chi72_eq9_chi48ABC_combined_coverage`: under
    χ54=C ∧ χ72=B ∧ χ48 ∈ ABC, use R334 crossed (χ48=A) + R341 (χ48=B);
    χ48=C contradicts.
  - **Target D** `chi54_eq18_chi72_eq18_chi48ABC_combined_coverage`: under
    χ54=C ∧ χ72=C ∧ χ48 ∈ ABC, use R333-E (χ48=A) + R335-F (χ48=B);
    χ48=C contradicts.

  **Audit R338 integration** (Target E): χ54=C-parameterized strengthened
  summaries (Targets C/D) are the correct integration pattern, not
  modifying R338 in place. R338's existing χ48 dispatch covers all χ48 ∈
  ABC under arbitrary χ54; the χ54=C-parameterized version is a strict
  enhancement that lives alongside R338.
-/

/-- **R342 Target A — Direct contradiction `χ48 = C ∧ χ54 = C → False`**:
  immediate from R329 (`χ48 = C → χ54 ≠ C`). This is the foundational
  incompatibility theorem used by R342 Targets B/C/D to eliminate
  χ48=C under χ54=C contexts. -/
theorem bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h54_eq_18 : χ 54 = χ 18) :
    False := by
  have h54_ne_18 :=
    bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
      χ (by omega) hNoMono h48_eq_18
  exact h54_ne_18 h54_eq_18

/-- **R342 Target B — χ(54)=C + χ(48) ∈ ABC excludes χ(48)=C**: under
  R318 Branch II 3-anchor + IsKColoring n 4 χ + `χ54 = C` + `χ48 ∈ ABC`,
  χ48 ≠ C; dispatch χ48 to R333-E expansion (χ48=A) or R335-D expansion
  (χ48=B). -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi48ABC_refined_no_chi48C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
       (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) := by
  rcases h48ABC with h48A | h48BC
  · -- χ48 = A: R333-E expanded.
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_branch_expanded
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A)
  · rcases h48BC with h48B | h48C
    · -- χ48 = B: R335-D expanded.
      exact Or.inr
        (bAdicEquation_3_branchII_chi48_eq9_branch_expanded
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B)
    · -- χ48 = C: contradicts χ54 = C via R342 Target A.
      exact absurd (bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
        χ h81 hNoMono h48C h54_eq_18) (by simp)

/-- **R342 Target C — χ(54)=C ∧ χ(72)=B ∧ χ(48) ∈ ABC combined coverage**:
  under joint hypotheses, χ48=C is impossible (Target A); χ48=A uses R334
  crossed (χ72=B eliminates χ75=B); χ48=B uses R341 (full triple-context
  R340-G prune of χ51=C). -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48ABC_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    ((χ 33 = χ 27 ∧ χ 38 ≠ χ 27 ∧
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
      (χ 33 = χ 18 ∧ χ 29 ≠ χ 18 ∧
        ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
      ((χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) ∧
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)))) := by
  rcases h48ABC with h48A | h48BC
  · -- χ48 = A: R334 crossed.
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A h72_eq_9)
  · rcases h48BC with h48B | h48C
    · -- χ48 = B: R341 triple-context combined coverage.
      exact Or.inr
        (bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h72_eq_9 h48B)
    · -- χ48 = C: contradicts χ54 = C via R342 Target A.
      exact absurd (bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
        χ h81 hNoMono h48C h54_eq_18) (by simp)

/-- **R342 Target D — χ(54)=C ∧ χ(72)=C ∧ χ(48) ∈ ABC combined coverage**:
  under joint hypotheses, χ48=C is impossible (Target A); χ48=A uses
  R333-E expanded; χ48=B uses R335-F combined (χ72=C adds χ75 ≠ C hook). -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi72_eq18_chi48ABC_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
       (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) := by
  rcases h48ABC with h48A | h48BC
  · -- χ48 = A: R333-E expanded (no extra χ72=C hook).
    exact Or.inl
      (bAdicEquation_3_branchII_chi48_eq27_branch_expanded
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A)
  · rcases h48BC with h48B | h48C
    · -- χ48 = B + χ72 = C: R335-F combined.
      exact Or.inr
        (bAdicEquation_3_branchII_chi48_eq9_chi72_eq18_combined_coverage
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B h72_eq_18)
    · -- χ48 = C: contradicts χ54 = C via R342 Target A.
      exact absurd (bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
        χ h81 hNoMono h48C h54_eq_18) (by simp)

/-! ### §183. R343 — Compact χ(54)=C-parametrized Branch II summary.

  Goal: assemble a clean, reusable χ(54)=C summary by combining R322
  weak dispatcher with R342 Target A's incompatibility.

  Deliverables:
  - **Target D** `chi54_eq18_chi72BC_or_chi48AB`: under χ54=C, R322's
    χ48 ∈ ABC fallback collapses to χ48 ∈ {A, B}.
  - **Target H** `chi54_eq18_core_summary`: pair Target D with R326-C
    (`chi54_eq18_chi36_or_chi24_dispatch`) to yield the χ54=C core
    macro-case summary.

  **Audit Pitfall (Target G)**: an "obvious" χ54=C mega-summary
  combining χ72 ∈ {B, C} ∧ χ48 ∈ ABC is INVALID from R322 alone. R322
  provides a DISJUNCTION `χ72 ∈ {B,C} ∨ χ48 ∈ ABC`, not a conjunction.
  The χ54=C summary must respect this — Target D's output is the
  correct structural macro-case split:
       `(χ72 ∈ {B,C}) ∨ (χ48 ∈ {A,B})`,
  not `(χ72 ∈ {B,C}) ∧ (χ48 ∈ {A,B})`.

  Future macro-case work (R344+) should branch on one side or the
  other, applying R342 Target C/D when χ72 ∈ {B,C} fires, or
  R342 Target B / R333-E / R335-D when χ48 ∈ {A,B} fires.
-/

/-- **R343 Target D — Under χ(54)=C, R322 collapses χ(48) ABC to χ(48) AB**:
  combines R322 weak dispatcher with R342 Target A's incompatibility
  `χ48=C ∧ χ54=C → False` to remove χ48=C from R322's fallback. -/
theorem bAdicEquation_3_branchII_chi54_eq18_chi72BC_or_chi48AB
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18) :
    (χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
    (χ 48 = χ 27 ∨ χ 48 = χ 9) := by
  have hR322 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases hR322 with h72BC | h48ABC
  · exact Or.inl h72BC
  · rcases h48ABC with h48A | h48B_or_C
    · exact Or.inr (Or.inl h48A)
    · rcases h48B_or_C with h48B | h48C
      · exact Or.inr (Or.inr h48B)
      · -- χ48 = C: contradicts χ54 = C via R342 Target A.
        exact absurd
          (bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
            χ h81 hNoMono h48C h54_eq_18) (by simp)

/-- **R343 Target H — χ(54)=C core summary**: package R326-C dispatcher
  with R343 Target D into a 2-And macro-case summary.

  Under χ54 = C:
  - Left side: `χ36 ∈ {A, B} ∨ χ24 ∈ ABC` (R326-C dispatcher).
  - Right side: `χ72 ∈ {B, C} ∨ χ48 ∈ {A, B}` (R343 Target D).

  Future macro-case branching on either side yields R344+ leaf cases. -/
theorem bAdicEquation_3_branchII_chi54_eq18_core_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 9) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
    ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
      (χ 48 = χ 27 ∨ χ 48 = χ 9)) :=
  ⟨bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18,
   bAdicEquation_3_branchII_chi54_eq18_chi72BC_or_chi48AB
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18⟩

/-! ### §184. R344 — Compact χ(54)=B core summary and unified χ(54)∈{B,C} summary.

  R343 covered the χ54=C case. R344 builds the parallel χ54=B summary
  and unifies them via R321 left branch (χ54 ∈ {B, C}).

  Deliverables:
  - **Target A** `chi54_eq9_core_summary`: 2-And summary under χ54=B,
    using R326-B + R322 weak dispatcher.
  - **Target B** `chi54_BC_core_summary`: 2-disjunction over χ54 ∈ {B, C}
    with each case carrying the corresponding core summary.
  - **Target C** `chi54_or_chi36_core_split`: R321-rooted theorem
    incorporating Target B for the χ54 ∈ {B, C} side.
  - **Optional Target E-1** `chi54_eq9_chi48_eq9_forces_chi66_ne_chi9`
    via triple (54, 48, 66).
  - **Optional Target E-2** `chi72_eq9_chi54_eq9_forces_chi78_ne_chi9`
    via triple (72, 54, 78).

  **Audit χ54=B χ48-color elimination** (Target D):
  - χ48=A and χ54=B differ; no same-color triple eliminates this combo.
  - χ48=C and χ54=B differ; ditto.
  - χ48=B and χ54=B share color B but the relevant triple (54, 48, 66)
    forces χ66 ≠ B (a future layer point), NOT a direct contradiction.
  Conclusion: χ54=B does NOT eliminate any χ48 anchor-set membership,
  so the R344 χ54=B core summary keeps the full R322 χ48 ∈ ABC fallback
  (in contrast to R343's χ54=C summary which collapsed to χ48 ∈ {A,B}).
-/

/-- **R344 Target A — χ(54)=B core summary**: package R326-B dispatcher
  with R322 weak dispatcher. Under χ54=B:
  - Left side: `χ36 ∈ {A, C} ∨ χ24 ∈ ABC` (R326-B).
  - Right side: `χ72 ∈ {B, C} ∨ χ48 ∈ ABC` (R322, no pruning since χ54=B
    doesn't eliminate any χ48 anchor-set membership). -/
theorem bAdicEquation_3_branchII_chi54_eq9_core_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_9 : χ 54 = χ 9) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
    ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
      (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18)) :=
  ⟨bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9,
   bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC
     χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9⟩

/-- **R344 Target B — Unified χ(54) ∈ {B, C} core summary**: dispatches
  on χ54 to R344-A (χ54=B) or R343 (χ54=C) core summary. Preserves
  h54-equality in each disjunct. -/
theorem bAdicEquation_3_branchII_chi54_BC_core_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54BC : χ 54 = χ 9 ∨ χ 54 = χ 18) :
    (χ 54 = χ 9 ∧
      (((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
       ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
        (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18)))) ∨
    (χ 54 = χ 18 ∧
      (((χ 36 = χ 27 ∨ χ 36 = χ 9) ∨
        (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
       ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
        (χ 48 = χ 27 ∨ χ 48 = χ 9)))) := by
  rcases h54BC with h54B | h54C
  · exact Or.inl ⟨h54B,
      bAdicEquation_3_branchII_chi54_eq9_core_summary
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B⟩
  · exact Or.inr ⟨h54C,
      bAdicEquation_3_branchII_chi54_eq18_core_summary
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C⟩

/-- **R344 Target C — R321-connected χ(54)-or-χ(36) core split**:
  combines R321 with R344 Target B for the χ54 ∈ {B, C} side.

  Under R318 Branch II 3-anchor + IsKColoring n 4 χ, output is:
  - Left: χ54 ∈ {B, C} case carries R344-B unified summary;
  - Right: χ36 ∈ {B, C} directly (R321 right side, no further structure
    added here). -/
theorem bAdicEquation_3_branchII_chi54_or_chi36_core_split
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9) :
    ((χ 54 = χ 9 ∧
        (((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
          (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
         ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
          (χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18)))) ∨
      (χ 54 = χ 18 ∧
        (((χ 36 = χ 27 ∨ χ 36 = χ 9) ∨
          (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
         ((χ 72 = χ 9 ∨ χ 72 = χ 18) ∨
          (χ 48 = χ 27 ∨ χ 48 = χ 9))))) ∨
    (χ 36 = χ 9 ∨ χ 36 = χ 18) := by
  have hR321 :=
    bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  rcases hR321 with h54BC | h36BC
  · exact Or.inl
      (bAdicEquation_3_branchII_chi54_BC_core_summary
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54BC)
  · exact Or.inr h36BC

/-- **R344 Target E-1 — `χ(54)=B ∧ χ(48)=B → χ(66) ≠ B`** via triple (54, 48, 66):
  54 + 3·48 = 198 = 3·66. b=3, d=18, y=48. Under χ54=B ∧ χ48=B, first conjunct
  holds; χ66=B triggers mono. χ66 is layer (3·22) but currently not a terminal. -/
theorem bAdicEquation_3_chi54_eq_chi9_chi48_eq_chi9_forces_chi66_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h66 : 66 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_9 : χ 54 = χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    χ 66 ≠ χ 9 := by
  intro h66_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 48) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 48
    rw [show (3 * 18 : ℕ) = 54 by decide]
    exact h54_eq_9.trans h48_eq_9.symm
  · show χ 48 = χ (48 + 18)
    rw [show (48 + 18 : ℕ) = 66 by decide]
    exact h48_eq_9.trans h66_eq_9.symm

/-- **R344 Target E-2 — `χ(72)=B ∧ χ(54)=B → χ(78) ≠ B`** via triple (72, 54, 78):
  72 + 3·54 = 234 = 3·78. b=3, d=24, y=54. Under χ72=B ∧ χ54=B, first conjunct
  holds; χ78=B triggers mono. χ78 is layer (3·26). -/
theorem bAdicEquation_3_chi72_eq_chi9_chi54_eq_chi9_forces_chi78_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h78 : 78 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h72_eq_9 : χ 72 = χ 9)
    (h54_eq_9 : χ 54 = χ 9) :
    χ 78 ≠ χ 9 := by
  intro h78_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 24) (y := 54) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 24) = χ 54
    rw [show (3 * 24 : ℕ) = 72 by decide]
    exact h72_eq_9.trans h54_eq_9.symm
  · show χ 54 = χ (54 + 24)
    rw [show (54 + 24 : ℕ) = 78 by decide]
    exact h54_eq_9.trans h78_eq_9.symm

/-! ### §185. R345 — χ(54)=B parameterized crossed summaries.

  Parallel to R342's χ54=C summaries, but χ54=B does NOT eliminate any
  χ48 anchor membership (audit). So the χ54=B parameterized versions are
  semantic aliases of existing R336/R332 expansions with an added
  `_h54_eq_9` hypothesis for naming consistency.

  Deliverables:
  - **Target A** `chi54_eq9_chi72_eq9_chi48ABC_combined_coverage`: under
    χ54=B ∧ χ72=B ∧ χ48 ∈ ABC. Delegates to R336 Target A
    (chi72_eq9_chi48ABC_crossed_expansion).
  - **Target B** `chi54_eq9_chi72_eq18_chi48ABC_combined_coverage`: under
    χ54=B ∧ χ72=C ∧ χ48 ∈ ABC. Delegates to R336 Target B.
  - **Target C** `chi54_eq9_chi48ABC_full_expansion`: under χ54=B ∧ χ48 ∈ ABC.
    Delegates to R332 Target A (chi48_in_ABC_full_coverage).

  **Audit Target D — χ54=B vs χ54=C pruning strength**:
  - R342 (χ54=C): eliminates χ48=C via incompatibility with R329.
  - R345 (χ54=B): NO direct χ48 elimination; only same-color pairs
    (χ54=B ∧ χ48=B) yield future-layer exclusions (χ66 ≠ B from R344 E-1,
    or χ78 ≠ B from R344 E-2 via χ72).
  Conclusion: χ54=B is structurally weaker than χ54=C. R345 summaries
  preserve all three χ48 sub-cases (A/B/C) unchanged.

  **Optional χ66/χ78 annotation policy**: not integrated. Adding
  `χ66 ≠ B` to χ48=B branches or `χ78 ≠ B` to χ72=B branches would
  require conjunction restructuring and increase syntactic clutter
  without strengthening dispatcher outputs. Left for future rounds
  if χ66/χ78 become explicit terminal targets.
-/

/-- **R345 Target A — χ(54)=B ∧ χ(72)=B ∧ χ(48) ∈ ABC combined coverage**:
  semantic alias of R336 `chi72_eq9_chi48ABC_crossed_expansion` with
  χ54=B context tag. The h54_eq_9 hypothesis is structural only (no
  pruning since χ54=B doesn't conflict with any χ48 anchor). -/
theorem bAdicEquation_3_branchII_chi54_eq9_chi72_eq9_chi48ABC_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_9 : χ 54 = χ 9)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :=
  bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_expansion
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9 h48ABC

/-- **R345 Target B — χ(54)=B ∧ χ(72)=C ∧ χ(48) ∈ ABC combined coverage**:
  semantic alias of R336 `chi72_eq18_chi48ABC_crossed_expansion` with
  χ54=B context tag. -/
theorem bAdicEquation_3_branchII_chi54_eq9_chi72_eq18_chi48ABC_combined_coverage
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_9 : χ 54 = χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
       (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
       (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :=
  bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_expansion
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18 h48ABC

/-- **R345 Target C — χ(54)=B ∧ χ(48) ∈ ABC standalone full expansion**:
  semantic alias of R332 Target A `chi48_in_ABC_full_coverage` with
  χ54=B context tag. No χ48 elimination; all three sub-cases (A/B/C)
  retained. -/
theorem bAdicEquation_3_branchII_chi54_eq9_chi48ABC_full_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_9 : χ 54 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    ((χ 75 = χ 9 ∨ χ 75 = χ 18) ∨
      (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
    ((χ 51 = χ 27 ∨ χ 51 = χ 18) ∨
      (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
    ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
      (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
      (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
      (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :=
  bAdicEquation_3_branchII_chi48_in_ABC_full_coverage
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48ABC

/-! ### §186. R346 — Unified χ(54)∈{B,C} parameterized summaries.

  Build unified summaries dispatching on χ54 ∈ {B, C}, combining:
  - χ54=B side: R345 expansions (no χ48 elimination), or inline R333-E /
    R335-D / R330 dispatch for the χ48ABC-only variant (needed to expose
    ≠ annotations not present in R345-C's R332-A delegation).
  - χ54=C side: R342 expansions (with χ48=C eliminated).

  Deliverables:
  - **Target A** `chi54BC_chi48ABC_parameterized_expansion`: unified χ54 ∈ {B, C}
    ∧ χ48 ∈ ABC. χ54=B side inlines R333-E + R335-D + R330; χ54=C side
    delegates to R342-B.
  - **Target B** `chi54BC_chi72_eq9_chi48ABC_parameterized_expansion`:
    unified under χ72=B. Delegates to R345-A / R342-C.
  - **Target C** `chi54BC_chi72_eq18_chi48ABC_parameterized_expansion`:
    unified under χ72=C. Delegates to R345-B / R342-D.

  **Audit Target E — Usefulness**: these unified summaries are
  high-resolution dispatch entry points for downstream consumers needing
  a single h54BC hypothesis. They do NOT replace R344 core split
  (`chi54_or_chi36_core_split`), which remains the most compact view of
  the χ54-side macro-case structure. R346 summaries are richer expansions
  for cases needing concrete leaf-level conclusions.
-/

/-- **R346 Target A — Unified χ(54) ∈ {B, C} ∧ χ(48) ∈ ABC expansion**:
  χ54=B side uses R333-E + R335-D + R330 dispatch (with ≠ annotations);
  χ54=C side uses R342-B (χ48=C eliminated). -/
theorem bAdicEquation_3_branchII_chi54BC_chi48ABC_parameterized_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54BC : χ 54 = χ 9 ∨ χ 54 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (χ 54 = χ 9 ∧
      ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
          (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
         (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
        ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
          (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
          (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
          (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)))) ∨
    (χ 54 = χ 18 ∧
      ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
          (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
         (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)))) := by
  rcases h54BC with h54B | h54C
  · -- χ54=B: inline R333-E (χ48=A) + R335-D (χ48=B) + R330 (χ48=C).
    refine Or.inl ⟨h54B, ?_⟩
    rcases h48ABC with h48A | h48BC'
    · exact Or.inl
        (bAdicEquation_3_branchII_chi48_eq27_branch_expanded
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48A)
    · rcases h48BC' with h48B | h48C
      · exact Or.inr (Or.inl
          (bAdicEquation_3_branchII_chi48_eq9_branch_expanded
            χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48B))
      · exact Or.inr (Or.inr
          (bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain
            χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48C))
  · -- χ54=C: delegate to R342-B (χ48=C eliminated).
    exact Or.inr ⟨h54C,
      bAdicEquation_3_branchII_chi54_eq18_chi48ABC_refined_no_chi48C
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C h48ABC⟩

/-- **R346 Target B — Unified χ(54) ∈ {B, C} ∧ χ(72)=B ∧ χ(48) ∈ ABC expansion**:
  χ54=B side delegates to R345-A; χ54=C side delegates to R342-C. -/
theorem bAdicEquation_3_branchII_chi54BC_chi72_eq9_chi48ABC_parameterized_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54BC : χ 54 = χ 9 ∨ χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (χ 54 = χ 9 ∧
      (((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
          (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
        ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
          (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
          (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
          (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)))) ∨
    (χ 54 = χ 18 ∧
      (((χ 75 = χ 18 ∧ χ 43 ≠ χ 18) ∨
          (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        ((χ 33 = χ 27 ∧ χ 38 ≠ χ 27 ∧
            (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
               (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
              (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
          (χ 33 = χ 18 ∧ χ 29 ≠ χ 18 ∧
            ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
              (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18))) ∨
          ((χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) ∧
            (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
               (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
              (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)))))) := by
  rcases h54BC with h54B | h54C
  · exact Or.inl ⟨h54B,
      bAdicEquation_3_branchII_chi54_eq9_chi72_eq9_chi48ABC_combined_coverage
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B h72_eq_9 h48ABC⟩
  · exact Or.inr ⟨h54C,
      bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48ABC_combined_coverage
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C h72_eq_9 h48ABC⟩

/-- **R346 Target C — Unified χ(54) ∈ {B, C} ∧ χ(72)=C ∧ χ(48) ∈ ABC expansion**:
  χ54=B side delegates to R345-B; χ54=C side delegates to R342-D. -/
theorem bAdicEquation_3_branchII_chi54BC_chi72_eq18_chi48ABC_parameterized_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54BC : χ 54 = χ 9 ∨ χ 54 = χ 18)
    (h72_eq_18 : χ 72 = χ 18)
    (h48ABC : χ 48 = χ 27 ∨ χ 48 = χ 9 ∨ χ 48 = χ 18) :
    (χ 54 = χ 9 ∧
      ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
          (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
         (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)) ∨
        ((χ 36 = χ 9 ∨ χ 36 = χ 18) ∨
          (χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
          (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
          (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)))) ∨
    (χ 54 = χ 18 ∧
      ((((χ 75 = χ 9 ∧ χ 72 ≠ χ 9) ∨
          (χ 75 = χ 18 ∧ χ 43 ≠ χ 18)) ∨
         (χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18)) ∨
        (((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
           (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 75 ≠ χ 18)) ∨
          (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18)))) := by
  rcases h54BC with h54B | h54C
  · exact Or.inl ⟨h54B,
      bAdicEquation_3_branchII_chi54_eq9_chi72_eq18_chi48ABC_combined_coverage
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B h72_eq_18 h48ABC⟩
  · exact Or.inr ⟨h54C,
      bAdicEquation_3_branchII_chi54_eq18_chi72_eq18_chi48ABC_combined_coverage
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C h72_eq_18 h48ABC⟩

/-! ### §187. R347 — Transfer-terminal cross-chain (48, 34, 50).

  Audit identified (48, 34, 50): 48 + 3·34 = 150 = 3·50 as the highest-value
  triple linking transfer-point terminals across branches:
  - χ48 = R331-B branch anchor (also R333-E/R335-D/R330 dispatch);
  - χ34 = R331-B / R335-D transfer terminal (χ48=B path);
  - χ50 = R331-A transfer fallback (χ48=A path).

  Rado constraint ¬(χ48 = χ34 ∧ χ34 = χ50): when χ48 and χ34 share color X,
  χ50 = X triggers monochromatic solution. This is a cross-branch
  constraint between χ48=A and χ48=B paths via the χ34 terminal.

  Deliverables:
  - **Target B-A** `χ48=A ∧ χ34=A → χ50≠A`.
  - **Target B-B** `χ48=B ∧ χ34=B → χ50≠B`.
  - **Target B-C** `χ48=C ∧ χ34=C → χ50≠C`.
  - **Target B-Pkg** `chi48_chi34_chi50_cross_refinement`: And of A/B/C.
  - **Target C/D** χ50 ∈ ABC refinements under same-color χ48/χ34
    (A → {B,C}; B → {A,C}; C → {A,B}).

  **Audit Target E — connection to current branches**:
  - R335-D χ48=B fallback supplies χ34 ∈ ABC; R334 / R342-C χ48=A fallback
    supplies χ50 ∈ ABC. If a downstream consumer has BOTH χ48=A and χ34=A
    available (unusual but possible in nested contexts), R347-A refines χ50.
  - Standalone usage: external context supplying matching χ48/χ34 values.

  **Audit Target F — next candidate (42, 36, 50)**:
  42 + 3·36 = 150 = 3·50. Links χ42 (R325-B / R337-F terminal of χ72=C
  branch) + χ36 (R326-C / R321 terminal of χ54-chain) + χ50 (R331-A
  fallback). Both χ42 and χ36 are layer positions on active chains —
  highest-priority R348 target.
-/

/-- **R347 Target B-A — `χ(48)=A ∧ χ(34)=A → χ(50) ≠ A`** via triple (48, 34, 50)
  with b=3, d=16, y=34 (48 + 3·34 = 150 = 3·50). -/
theorem bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h34_eq_27 : χ 34 = χ 27) :
    χ 50 ≠ χ 27 := by
  intro h50_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 34
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_27.trans h34_eq_27.symm
  · show χ 34 = χ (34 + 16)
    rw [show (34 + 16 : ℕ) = 50 by decide]
    exact h34_eq_27.trans h50_eq_27.symm

/-- **R347 Target B-B — `χ(48)=B ∧ χ(34)=B → χ(50) ≠ B`** via triple (48, 34, 50). -/
theorem bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9) :
    χ 50 ≠ χ 9 := by
  intro h50_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 34
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_9.trans h34_eq_9.symm
  · show χ 34 = χ (34 + 16)
    rw [show (34 + 16 : ℕ) = 50 by decide]
    exact h34_eq_9.trans h50_eq_9.symm

/-- **R347 Target B-C — `χ(48)=C ∧ χ(34)=C → χ(50) ≠ C`** via triple (48, 34, 50). -/
theorem bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h34_eq_18 : χ 34 = χ 18) :
    χ 50 ≠ χ 18 := by
  intro h50_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 34
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_18.trans h34_eq_18.symm
  · show χ 34 = χ (34 + 16)
    rw [show (34 + 16 : ℕ) = 50 by decide]
    exact h34_eq_18.trans h50_eq_18.symm

/-- **R347 Target B-Pkg — χ(48)/χ(34)/χ(50) cross refinement packaging**:
  And of three same-color implications A/B/C. -/
theorem bAdicEquation_3_branchII_chi48_chi34_chi50_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 48 = χ 27 → χ 34 = χ 27 → χ 50 ≠ χ 27) ∧
    (χ 48 = χ 9  → χ 34 = χ 9  → χ 50 ≠ χ 9) ∧
    (χ 48 = χ 18 → χ 34 = χ 18 → χ 50 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_27 h34_eq_27
    exact bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h48_eq_27 h34_eq_27
  · intro h48_eq_9 h34_eq_9
    exact bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h48_eq_9 h34_eq_9
  · intro h48_eq_18 h34_eq_18
    exact bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h48_eq_18 h34_eq_18

/-- **R347 Target C — χ(50) ∈ ABC refinement under χ(48)=A ∧ χ(34)=A**:
  χ50 ∈ {B, C} (χ50 = A eliminated by Target B-A). -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi48A_chi34A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h34_eq_27 : χ 34 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 ∨ χ 50 = χ 18 := by
  have h50_ne_27 :=
    bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h48_eq_27 h34_eq_27
  rcases h50ABC with h50A | h50B_or_C
  · exact absurd h50A h50_ne_27
  · exact h50B_or_C

/-- **R347 Target D-B — χ(50) ∈ ABC refinement under χ(48)=B ∧ χ(34)=B**:
  χ50 ∈ {A, C} (χ50 = B eliminated by Target B-B). -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi48B_chi34B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 18 := by
  have h50_ne_9 :=
    bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h48_eq_9 h34_eq_9
  rcases h50ABC with h50A | h50B_or_C
  · exact Or.inl h50A
  · rcases h50B_or_C with h50B | h50C
    · exact absurd h50B h50_ne_9
    · exact Or.inr h50C

/-- **R347 Target D-C — χ(50) ∈ ABC refinement under χ(48)=C ∧ χ(34)=C**:
  χ50 ∈ {A, B} (χ50 = C eliminated by Target B-C). -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi48C_chi34C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h34_eq_18 : χ 34 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 9 := by
  have h50_ne_18 :=
    bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h48_eq_18 h34_eq_18
  rcases h50ABC with h50A | h50B_or_C
  · exact Or.inl h50A
  · rcases h50B_or_C with h50B | h50C
    · exact Or.inr h50B
    · exact absurd h50C h50_ne_18

/-! ### §188. R348 — Layer/transfer cross-chain (42, 36, 50).

  Triple (42, 36, 50): 42 + 3·36 = 150 = 3·50. Higher-value than R347
  because TWO layer terminals (χ42 and χ36) cross with the χ50 transfer:
  - χ42 = R325-B / R337-F terminal of χ72=C branch (layer 3·14);
  - χ36 = R326-C / R321 terminal of χ54-chain (layer 3·12);
  - χ50 = R331-A transfer fallback of χ48=A path.

  Rado constraint ¬(χ42 = χ36 ∧ χ36 = χ50): same-color χ42/χ36 forces
  χ50 to differ.

  Deliverables:
  - **Target A** `χ42=A ∧ χ36=A → χ50≠A`.
  - **Target B** `χ42=B ∧ χ36=B → χ50≠B`.
  - **Target C** `χ42=C ∧ χ36=C → χ50≠C`.
  - **Target D** `chi42_chi36_chi50_cross_refinement`: And of A/B/C.
  - **Target E** χ50 ∈ ABC refinements (A/B/C variants).

  **Audit Target F — current branch hook under χ54=C ∧ χ72=C**:
  - R337-F χ42 expanded (under χ72=C): `χ42 ∈ {A, B}` (no C, since R325-B
    χ72=C terminal pins χ42 to {A,B}).
  - R326-C / R343 χ36 dispatcher (under χ54=C): `χ36 ∈ {A, B}` (no C).
  - When χ42=A ∧ χ36=A: R348-A forces χ50 ≠ A.
  - When χ42=B ∧ χ36=B: R348-B forces χ50 ≠ B.
  - Combined with R342-D χ50 ∈ ABC fallback under χ54=C ∧ χ72=C ∧ χ48=A,
    these become **active refinements** in the joint context.

  **Audit Target H — R347 + R348 jointly force χ50**:
  - R347-A: χ48=A ∧ χ34=A → χ50≠A
  - R348-A: χ42=A ∧ χ36=A → χ50≠A (same conclusion, different trigger)
  - In contexts where two independent exclusions fire (e.g. χ50≠A AND
    χ50≠B), combined with χ50 ∈ ABC, χ50 is pinned to one color.
  - Future generic helper "colorABC + 2 exclusions → 1 color" could
    be added if pattern repeats enough.
-/

/-- **R348 Target A — `χ(42)=A ∧ χ(36)=A → χ(50) ≠ A`** via triple (42, 36, 50)
  with b=3, d=14, y=36 (42 + 3·36 = 150 = 3·50). -/
theorem bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_27 : χ 42 = χ 27)
    (h36_eq_27 : χ 36 = χ 27) :
    χ 50 ≠ χ 27 := by
  intro h50_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 36
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_27.trans h36_eq_27.symm
  · show χ 36 = χ (36 + 14)
    rw [show (36 + 14 : ℕ) = 50 by decide]
    exact h36_eq_27.trans h50_eq_27.symm

/-- **R348 Target B — `χ(42)=B ∧ χ(36)=B → χ(50) ≠ B`** via triple (42, 36, 50). -/
theorem bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_9 : χ 42 = χ 9)
    (h36_eq_9 : χ 36 = χ 9) :
    χ 50 ≠ χ 9 := by
  intro h50_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 36
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_9.trans h36_eq_9.symm
  · show χ 36 = χ (36 + 14)
    rw [show (36 + 14 : ℕ) = 50 by decide]
    exact h36_eq_9.trans h50_eq_9.symm

/-- **R348 Target C — `χ(42)=C ∧ χ(36)=C → χ(50) ≠ C`** via triple (42, 36, 50). -/
theorem bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_18 : χ 42 = χ 18)
    (h36_eq_18 : χ 36 = χ 18) :
    χ 50 ≠ χ 18 := by
  intro h50_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 36
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_18.trans h36_eq_18.symm
  · show χ 36 = χ (36 + 14)
    rw [show (36 + 14 : ℕ) = 50 by decide]
    exact h36_eq_18.trans h50_eq_18.symm

/-- **R348 Target D — χ(42)/χ(36)/χ(50) cross refinement packaging**:
  And of three same-color implications A/B/C. -/
theorem bAdicEquation_3_branchII_chi42_chi36_chi50_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 42 = χ 27 → χ 36 = χ 27 → χ 50 ≠ χ 27) ∧
    (χ 42 = χ 9  → χ 36 = χ 9  → χ 50 ≠ χ 9) ∧
    (χ 42 = χ 18 → χ 36 = χ 18 → χ 50 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h42_eq_27 h36_eq_27
    exact bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h42_eq_27 h36_eq_27
  · intro h42_eq_9 h36_eq_9
    exact bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h42_eq_9 h36_eq_9
  · intro h42_eq_18 h36_eq_18
    exact bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h42_eq_18 h36_eq_18

/-- **R348 Target E-A — χ(50) ∈ ABC refinement under χ(42)=A ∧ χ(36)=A**:
  χ50 ∈ {B, C} (χ50 = A eliminated by Target A). -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi42A_chi36A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_27 : χ 42 = χ 27)
    (h36_eq_27 : χ 36 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 ∨ χ 50 = χ 18 := by
  have h50_ne_27 :=
    bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h42_eq_27 h36_eq_27
  rcases h50ABC with h50A | h50B_or_C
  · exact absurd h50A h50_ne_27
  · exact h50B_or_C

/-- **R348 Target E-B — χ(50) ∈ ABC refinement under χ(42)=B ∧ χ(36)=B**:
  χ50 ∈ {A, C}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi42B_chi36B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_9 : χ 42 = χ 9)
    (h36_eq_9 : χ 36 = χ 9)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 18 := by
  have h50_ne_9 :=
    bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h42_eq_9 h36_eq_9
  rcases h50ABC with h50A | h50B_or_C
  · exact Or.inl h50A
  · rcases h50B_or_C with h50B | h50C
    · exact absurd h50B h50_ne_9
    · exact Or.inr h50C

/-- **R348 Target E-C — χ(50) ∈ ABC refinement under χ(42)=C ∧ χ(36)=C**:
  χ50 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi42C_chi36C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_18 : χ 42 = χ 18)
    (h36_eq_18 : χ 36 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 9 := by
  have h50_ne_18 :=
    bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h42_eq_18 h36_eq_18
  rcases h50ABC with h50A | h50B_or_C
  · exact Or.inl h50A
  · rcases h50B_or_C with h50B | h50C
    · exact Or.inr h50B
    · exact absurd h50C h50_ne_18

/-! ### §189. R349 — ABC color-refinement helpers + R347+R348 χ(50) closures.

  Build small reusable helpers for "ABC + exclusion(s) → narrowed color set"
  pattern. Then apply them to χ(50) combining R347 (48/34/50 cross-chain)
  with R348 (42/36/50 cross-chain), forcing χ50 to a single color under
  appropriate 2-exclusion contexts.

  Deliverables:
  - **Helpers A1-A3** (ABC + 2 exclusions → 1 color):
    * `branchII_ABC_refine_neA_neB_to_C`: ABC ∧ ¬A ∧ ¬B → χ = C
    * `branchII_ABC_refine_neA_neC_to_B`: ABC ∧ ¬A ∧ ¬C → χ = B
    * `branchII_ABC_refine_neB_neC_to_A`: ABC ∧ ¬B ∧ ¬C → χ = A
  - **Helpers B1-B3** (ABC + 1 exclusion → 2-color disjunction):
    * `branchII_ABC_refine_neA_to_BC`
    * `branchII_ABC_refine_neB_to_AC`
    * `branchII_ABC_refine_neC_to_AB`
  - **6 χ(50) single-color forcing theorems** combining R347 + R348 with
    different exclusion colors.

  **Audit E — current branch relevance**: under χ54=C ∧ χ72=C, both
  χ42 ∈ {A, B} and χ36 ∈ {A, B} (R337-F / R343). So R348 only fires
  A-A or B-B same-color in this active context. R347 has no such restriction
  (operates on χ34/χ48). The 6 combinators are mostly future-leverage for
  nested contexts where both same-color conditions appear independently.

  **Audit F — next candidate (R350)**: triple (36, 38, 50). χ38 emerges
  as R337-D χ33=A sub-branch terminal exclusion. χ36 is active in
  χ54-chain. Cross-chain with χ50 transfer fallback worth investigating.
-/

/-- **R349 Helper A1 — ABC ∧ ¬A ∧ ¬B → C**: under `χ x ∈ {A, B, C}`,
  exclusions of A and B narrow to C. -/
theorem branchII_ABC_refine_neA_neB_to_C
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneA : χ x ≠ χ 27)
    (hneB : χ x ≠ χ 9) :
    χ x = χ 18 := by
  rcases hABC with hA | hB_or_C
  · exact absurd hA hneA
  · rcases hB_or_C with hB | hC
    · exact absurd hB hneB
    · exact hC

/-- **R349 Helper A2 — ABC ∧ ¬A ∧ ¬C → B**. -/
theorem branchII_ABC_refine_neA_neC_to_B
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneA : χ x ≠ χ 27)
    (hneC : χ x ≠ χ 18) :
    χ x = χ 9 := by
  rcases hABC with hA | hB_or_C
  · exact absurd hA hneA
  · rcases hB_or_C with hB | hC
    · exact hB
    · exact absurd hC hneC

/-- **R349 Helper A3 — ABC ∧ ¬B ∧ ¬C → A**. -/
theorem branchII_ABC_refine_neB_neC_to_A
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneB : χ x ≠ χ 9)
    (hneC : χ x ≠ χ 18) :
    χ x = χ 27 := by
  rcases hABC with hA | hB_or_C
  · exact hA
  · rcases hB_or_C with hB | hC
    · exact absurd hB hneB
    · exact absurd hC hneC

/-- **R349 Helper B1 — ABC ∧ ¬A → B ∨ C**. -/
theorem branchII_ABC_refine_neA_to_BC
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneA : χ x ≠ χ 27) :
    χ x = χ 9 ∨ χ x = χ 18 := by
  rcases hABC with hA | hB_or_C
  · exact absurd hA hneA
  · exact hB_or_C

/-- **R349 Helper B2 — ABC ∧ ¬B → A ∨ C**. -/
theorem branchII_ABC_refine_neB_to_AC
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneB : χ x ≠ χ 9) :
    χ x = χ 27 ∨ χ x = χ 18 := by
  rcases hABC with hA | hB_or_C
  · exact Or.inl hA
  · rcases hB_or_C with hB | hC
    · exact absurd hB hneB
    · exact Or.inr hC

/-- **R349 Helper B3 — ABC ∧ ¬C → A ∨ B**. -/
theorem branchII_ABC_refine_neC_to_AB
    {χ : ℕ → ℕ} {x : ℕ}
    (hABC : χ x = χ 27 ∨ χ x = χ 9 ∨ χ x = χ 18)
    (hneC : χ x ≠ χ 18) :
    χ x = χ 27 ∨ χ x = χ 9 := by
  rcases hABC with hA | hB_or_C
  · exact Or.inl hA
  · rcases hB_or_C with hB | hC
    · exact Or.inr hB
    · exact absurd hC hneC

/-- **R349 Combinator 1 — R347-A + R348-B force χ(50) = C**: under joint
  context χ48=A ∧ χ34=A (R347-A excludes χ50=A) and χ42=B ∧ χ36=B
  (R348-B excludes χ50=B), if χ50 ∈ ABC, then χ50 = C. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_C_of_chi48A_chi34A_and_chi42B_chi36B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h34_eq_27 : χ 34 = χ 27)
    (h42_eq_9 : χ 42 = χ 9)
    (h36_eq_9 : χ 36 = χ 9)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 18 := by
  have h50_ne_27 := bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
    χ (by omega) hNoMono h48_eq_27 h34_eq_27
  have h50_ne_9 := bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
    χ (by omega) hNoMono h42_eq_9 h36_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h50ABC h50_ne_27 h50_ne_9

/-- **R349 Combinator 2 — R347-A + R348-C force χ(50) = B**. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_B_of_chi48A_chi34A_and_chi42C_chi36C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h34_eq_27 : χ 34 = χ 27)
    (h42_eq_18 : χ 42 = χ 18)
    (h36_eq_18 : χ 36 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 := by
  have h50_ne_27 := bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
    χ (by omega) hNoMono h48_eq_27 h34_eq_27
  have h50_ne_18 := bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
    χ (by omega) hNoMono h42_eq_18 h36_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h50ABC h50_ne_27 h50_ne_18

/-- **R349 Combinator 3 — R347-B + R348-A force χ(50) = C**. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_C_of_chi48B_chi34B_and_chi42A_chi36A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9)
    (h42_eq_27 : χ 42 = χ 27)
    (h36_eq_27 : χ 36 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 18 := by
  have h50_ne_27 := bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
    χ (by omega) hNoMono h42_eq_27 h36_eq_27
  have h50_ne_9 := bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
    χ (by omega) hNoMono h48_eq_9 h34_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h50ABC h50_ne_27 h50_ne_9

/-- **R349 Combinator 4 — R347-B + R348-C force χ(50) = A**. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_A_of_chi48B_chi34B_and_chi42C_chi36C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9)
    (h42_eq_18 : χ 42 = χ 18)
    (h36_eq_18 : χ 36 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 := by
  have h50_ne_9 := bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
    χ (by omega) hNoMono h48_eq_9 h34_eq_9
  have h50_ne_18 := bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
    χ (by omega) hNoMono h42_eq_18 h36_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h50ABC h50_ne_9 h50_ne_18

/-- **R349 Combinator 5 — R347-C + R348-A force χ(50) = B**. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_B_of_chi48C_chi34C_and_chi42A_chi36A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h34_eq_18 : χ 34 = χ 18)
    (h42_eq_27 : χ 42 = χ 27)
    (h36_eq_27 : χ 36 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 := by
  have h50_ne_27 := bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
    χ (by omega) hNoMono h42_eq_27 h36_eq_27
  have h50_ne_18 := bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
    χ (by omega) hNoMono h48_eq_18 h34_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h50ABC h50_ne_27 h50_ne_18

/-- **R349 Combinator 6 — R347-C + R348-B force χ(50) = A**. -/
theorem bAdicEquation_3_branchII_chi50ABC_forces_A_of_chi48C_chi34C_and_chi42B_chi36B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h34_eq_18 : χ 34 = χ 18)
    (h42_eq_9 : χ 42 = χ 9)
    (h36_eq_9 : χ 36 = χ 9)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 := by
  have h50_ne_9 := bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
    χ (by omega) hNoMono h42_eq_9 h36_eq_9
  have h50_ne_18 := bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
    χ (by omega) hNoMono h48_eq_18 h34_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h50ABC h50_ne_9 h50_ne_18

/-! ### §190. R350 — Third χ(50) cross-chain (36, 38, 50).

  Triple (36, 38, 50): 36 + 3·38 = 150 = 3·50. Bridges:
  - χ36 = R326-C / R321 terminal of χ54-chain (layer 3·12, active);
  - χ38 = R337-D χ33=A sub-branch forced-exclusion target (`χ33=A → χ38≠A`);
  - χ50 = R331-A transfer fallback of χ48=A path.

  Rado constraint ¬(χ36 = χ38 ∧ χ38 = χ50): same-color χ36/χ38 forces χ50
  to differ.

  Deliverables:
  - **Target A** `χ36=A ∧ χ38=A → χ50≠A`.
  - **Target B** `χ36=B ∧ χ38=B → χ50≠B`.
  - **Target C** `χ36=C ∧ χ38=C → χ50≠C`.
  - **Target D** `chi36_chi38_chi50_cross_refinement`: And of A/B/C.
  - **Target E** χ50 ∈ ABC refinements (A/B/C variants).

  **Audit F — current branch relevance**:
  - χ38 currently appears in R337-D as `χ33=A → χ38≠A` (forced exclusion).
    χ38 is NOT yet classified into any anchor (no positive equality).
  - R350 cross lemmas activate only when context positively classifies
    χ38 (B or C, since A is excluded under χ33=A; or all three if χ33 ≠ A).
  - **Future-leverage**: this is the third independent χ50 exclusion
    source (after R347 and R348), available for R351+ contexts that
    classify χ38.

  **Audit G — next route to classify χ38**:
  - χ38 not in current dispatcher chain. Need new triple connecting χ38
    to ABC anchor:
    * (b·d, y, y+d) with y or y+d = 38 and another coord in {A, B, C}.
    * (b·d=9, y=29, y+d=32): no.
    * (38, y, ?): b·d = 38 not divisible by 3, invalid.
    * (y+d=38): d = 38 - y. For y=9, d=29; y=18, d=20; y=27, d=11.
      (33, 9, 38): 33 + 27 = 60 ≠ 3·38=114. No.
      (33, 18, 38): 33+54=87 ≠ 114. No.
      (b·d=33, y=27, y+d=38) → d=11, y=27, y+d=38: 33+81=114=3·38 ✓.
        Triple (33, 27, 38). χ33 + A → χ38 condition. R337-D already!
  Conclusion: χ38 ≠ A is the only existing condition. To get χ38 = B or C,
  need a triple `(?, ?, 38)` with two classified positions. Future work.
-/

/-- **R350 Target A — `χ(36)=A ∧ χ(38)=A → χ(50) ≠ A`** via triple (36, 38, 50)
  with b=3, d=12, y=38 (36 + 3·38 = 150 = 3·50). -/
theorem bAdicEquation_3_chi36_eq_chi27_chi38_eq_chi27_forces_chi50_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27)
    (h38_eq_27 : χ 38 = χ 27) :
    χ 50 ≠ χ 27 := by
  intro h50_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 38) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 38
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_27.trans h38_eq_27.symm
  · show χ 38 = χ (38 + 12)
    rw [show (38 + 12 : ℕ) = 50 by decide]
    exact h38_eq_27.trans h50_eq_27.symm

/-- **R350 Target B — `χ(36)=B ∧ χ(38)=B → χ(50) ≠ B`** via triple (36, 38, 50). -/
theorem bAdicEquation_3_chi36_eq_chi9_chi38_eq_chi9_forces_chi50_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h38_eq_9 : χ 38 = χ 9) :
    χ 50 ≠ χ 9 := by
  intro h50_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 38) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 38
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_9.trans h38_eq_9.symm
  · show χ 38 = χ (38 + 12)
    rw [show (38 + 12 : ℕ) = 50 by decide]
    exact h38_eq_9.trans h50_eq_9.symm

/-- **R350 Target C — `χ(36)=C ∧ χ(38)=C → χ(50) ≠ C`** via triple (36, 38, 50). -/
theorem bAdicEquation_3_chi36_eq_chi18_chi38_eq_chi18_forces_chi50_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h50 : 50 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h38_eq_18 : χ 38 = χ 18) :
    χ 50 ≠ χ 18 := by
  intro h50_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 38) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 38
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_18.trans h38_eq_18.symm
  · show χ 38 = χ (38 + 12)
    rw [show (38 + 12 : ℕ) = 50 by decide]
    exact h38_eq_18.trans h50_eq_18.symm

/-- **R350 Target D — χ(36)/χ(38)/χ(50) cross refinement packaging**:
  And of three same-color implications A/B/C. -/
theorem bAdicEquation_3_branchII_chi36_chi38_chi50_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9) :
    (χ 36 = χ 27 → χ 38 = χ 27 → χ 50 ≠ χ 27) ∧
    (χ 36 = χ 9  → χ 38 = χ 9  → χ 50 ≠ χ 9) ∧
    (χ 36 = χ 18 → χ 38 = χ 18 → χ 50 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h36_eq_27 h38_eq_27
    exact bAdicEquation_3_chi36_eq_chi27_chi38_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h36_eq_27 h38_eq_27
  · intro h36_eq_9 h38_eq_9
    exact bAdicEquation_3_chi36_eq_chi9_chi38_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h36_eq_9 h38_eq_9
  · intro h36_eq_18 h38_eq_18
    exact bAdicEquation_3_chi36_eq_chi18_chi38_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h36_eq_18 h38_eq_18

/-- **R350 Target E-A — χ(50) ∈ ABC refinement under χ(36)=A ∧ χ(38)=A**:
  χ50 ∈ {B, C} (χ50 = A eliminated by Target A). -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi36A_chi38A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27)
    (h38_eq_27 : χ 38 = χ 27)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 9 ∨ χ 50 = χ 18 := by
  have h50_ne_27 :=
    bAdicEquation_3_chi36_eq_chi27_chi38_eq_chi27_forces_chi50_ne_chi27
      χ (by omega) hNoMono h36_eq_27 h38_eq_27
  exact branchII_ABC_refine_neA_to_BC h50ABC h50_ne_27

/-- **R350 Target E-B — χ(50) ∈ ABC refinement under χ(36)=B ∧ χ(38)=B**:
  χ50 ∈ {A, C}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi36B_chi38B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h38_eq_9 : χ 38 = χ 9)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 18 := by
  have h50_ne_9 :=
    bAdicEquation_3_chi36_eq_chi9_chi38_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h36_eq_9 h38_eq_9
  exact branchII_ABC_refine_neB_to_AC h50ABC h50_ne_9

/-- **R350 Target E-C — χ(50) ∈ ABC refinement under χ(36)=C ∧ χ(38)=C**:
  χ50 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi50ABC_refine_of_chi36C_chi38C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h38_eq_18 : χ 38 = χ 18)
    (h50ABC : χ 50 = χ 27 ∨ χ 50 = χ 9 ∨ χ 50 = χ 18) :
    χ 50 = χ 27 ∨ χ 50 = χ 9 := by
  have h50_ne_18 :=
    bAdicEquation_3_chi36_eq_chi18_chi38_eq_chi18_forces_chi50_ne_chi18
      χ (by omega) hNoMono h36_eq_18 h38_eq_18
  exact branchII_ABC_refine_neC_to_AB h50ABC h50_ne_18

/-! ### §191. R351 — Active transfer C-exclusion chain.

  Build short, immediately-active C-exclusion lemmas for current transfer
  terminals χ34 (χ48=B fallback), χ22 (χ72=B fallback), χ28 (χ72=C fallback).
  Each is single-triple, single-color (C), suitable for direct insertion
  into existing summary contexts.

  Deliverables:
  - **Target A** `χ48=C → χ34≠C` via triple (48, 18, 34).
  - **Target B** `χ16=C → χ22≠C` via triple (18, 16, 22).
  - **Target C** `χ22=C → χ28≠C` via triple (18, 22, 28).
  - **Target D** package And of 3 implications.
  - **Target F** optional ABC refinements for χ34/χ22/χ28 under C exclusion.
-/

/-- **R351 Target A — `χ(48)=C → χ(34) ≠ C`** via triple (48, 18, 34) with
  b=3, d=16, y=18 (48 + 3·18 = 102 = 3·34). -/
theorem bAdicEquation_3_chi48_eq_chi18_forces_chi34_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18) :
    χ 34 ≠ χ 18 := by
  intro h34_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 18
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_18
  · show χ 18 = χ (18 + 16)
    rw [show (18 + 16 : ℕ) = 34 by decide]
    exact h34_eq_18.symm

/-- **R351 Target B — `χ(16)=C → χ(22) ≠ C`** via triple (18, 16, 22) with
  b=3, d=6, y=16 (18 + 3·16 = 66 = 3·22). -/
theorem bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h22 : 22 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_18 : χ 16 = χ 18) :
    χ 22 ≠ χ 18 := by
  intro h22_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 16
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h16_eq_18.symm
  · show χ 16 = χ (16 + 6)
    rw [show (16 + 6 : ℕ) = 22 by decide]
    exact h16_eq_18.trans h22_eq_18.symm

/-- **R351 Target C — `χ(22)=C → χ(28) ≠ C`** via triple (18, 22, 28) with
  b=3, d=6, y=22 (18 + 3·22 = 84 = 3·28). -/
theorem bAdicEquation_3_chi22_eq_chi18_forces_chi28_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h28 : 28 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_18 : χ 22 = χ 18) :
    χ 28 ≠ χ 18 := by
  intro h28_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 22) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 22
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h22_eq_18.symm
  · show χ 22 = χ (22 + 6)
    rw [show (22 + 6 : ℕ) = 28 by decide]
    exact h22_eq_18.trans h28_eq_18.symm

/-- **R351 Target D — C-exclusion transfer chain pack**: And of three R351
  C-exclusion implications for χ34/χ22/χ28 transfer terminals. -/
theorem bAdicEquation_3_branchII_C_transfer_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 18 → χ 34 ≠ χ 18) ∧
    (χ 16 = χ 18 → χ 22 ≠ χ 18) ∧
    (χ 22 = χ 18 → χ 28 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_18
    exact bAdicEquation_3_chi48_eq_chi18_forces_chi34_ne_chi18
      χ (by omega) hNoMono h48_eq_18
  · intro h16_eq_18
    exact bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
      χ (by omega) hNoMono h16_eq_18
  · intro h22_eq_18
    exact bAdicEquation_3_chi22_eq_chi18_forces_chi28_ne_chi18
      χ (by omega) hNoMono h22_eq_18

/-- **R351 Target F-1 — χ(34) ∈ ABC refinement under χ(48)=C**:
  combines R351 Target A with χ34 ∈ ABC to narrow to χ34 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi34ABC_refine_of_chi48C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_18 : χ 48 = χ 18)
    (h34ABC : χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :
    χ 34 = χ 27 ∨ χ 34 = χ 9 := by
  have h34_ne_18 :=
    bAdicEquation_3_chi48_eq_chi18_forces_chi34_ne_chi18
      χ (by omega) hNoMono h48_eq_18
  exact branchII_ABC_refine_neC_to_AB h34ABC h34_ne_18

/-- **R351 Target F-2 — χ(22) ∈ ABC refinement under χ(16)=C**:
  combines R351 Target B with χ22 ∈ ABC to narrow to χ22 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi22ABC_refine_of_chi16C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_18 : χ 16 = χ 18)
    (h22ABC : χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) :
    χ 22 = χ 27 ∨ χ 22 = χ 9 := by
  have h22_ne_18 :=
    bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
      χ (by omega) hNoMono h16_eq_18
  exact branchII_ABC_refine_neC_to_AB h22ABC h22_ne_18

/-- **R351 Target F-3 — χ(28) ∈ ABC refinement under χ(22)=C**:
  combines R351 Target C with χ28 ∈ ABC to narrow to χ28 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi28ABC_refine_of_chi22C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_18 : χ 22 = χ 18)
    (h28ABC : χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) :
    χ 28 = χ 27 ∨ χ 28 = χ 9 := by
  have h28_ne_18 :=
    bAdicEquation_3_chi22_eq_chi18_forces_chi28_ne_chi18
      χ (by omega) hNoMono h22_eq_18
  exact branchII_ABC_refine_neC_to_AB h28ABC h28_ne_18

/-! ### §192. R352 — Directional anchor-exclusion packs for χ(48)/χ(16)/χ(22).

  Complete the parallel A/B exclusion lemmas for the χ48 / χ16 / χ22 transfer
  terminals. Audit shows the "same-target A/B/C family" is INVALID: the
  b-adic equation `x + 3y = 3z` couples the y-position to the output z, so
  changing the anchor color (x's value) shifts z.

  Specifically, for each source position s used as y, the output z depends
  on which anchor x:
  - s = y=18, x ∈ {A, B, C}: z = (A+54)/3 = 27 (no), (B+54)/3 = 21 (no), (C+54)/3 = 24.
    Wait — the C case used (x, y, z) = (b·d, y, y+d) shape, so let's
    re-examine each family below.

  **Family 1 (χ48 → varies)**: triple (48, y, 48/3+y) = (48, y, 16+y).
  - y = 27 (A): z = 43. (48, 27, 43). 48+81 = 129 = 3·43 ✓.
  - y = 9  (B): z = 25. (48, 9, 25).  48+27 = 75 = 3·25 ✓.
  - y = 18 (C): z = 34. (48, 18, 34). 48+54 = 102 = 3·34 ✓. R351.

  **Family 2 (χ16 → varies)**: triple (x, 16, x/3+16). x = 3·d, so d = x/3.
  - x = 27 (A): d = 9, z = 25. (27, 16, 25). 27+48 = 75 = 3·25 ✓.
  - x = 9  (B): d = 3, z = 19. (9, 16, 19).  9+48 = 57 = 3·19 ✓.
  - x = 18 (C): d = 6, z = 22. (18, 16, 22). 18+48 = 66 = 3·22 ✓. R351.

  **Family 3 (χ22 → varies)**: triple (x, 22, x/3+22).
  - x = 27 (A): d = 9, z = 31. (27, 22, 31). 27+66 = 93 = 3·31 ✓.
  - x = 9  (B): d = 3, z = 25. (9, 22, 25).  9+66 = 75 = 3·25 ✓.
  - x = 18 (C): d = 6, z = 28. (18, 22, 28). 18+66 = 84 = 3·28 ✓. R351.

  **Repeated transfer node χ25**: emerges 3 times (χ48=B, χ16=A, χ22=B).
  Future round may benefit from a χ25 ∈ ABC dispatcher.

  Deliverables (6 new lemmas + 3 packs):
  - χ48: forces_chi43 (A), forces_chi25 (B); pack.
  - χ16: forces_chi25 (A), forces_chi19 (B); pack.
  - χ22: forces_chi31 (A), forces_chi25 (B); pack.
-/

/-- **R352 χ(48) = A → χ(43) ≠ A** via triple (48, 27, 43): 48 + 3·27 = 129 = 3·43. -/
theorem bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27) :
    χ 43 ≠ χ 27 := by
  intro h43_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 27
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_27
  · show χ 27 = χ (27 + 16)
    rw [show (27 + 16 : ℕ) = 43 by decide]
    exact h43_eq_27.symm

/-- **R352 χ(48) = B → χ(25) ≠ B** via triple (48, 9, 25): 48 + 3·9 = 75 = 3·25. -/
theorem bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9) :
    χ 25 ≠ χ 9 := by
  intro h25_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 16) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 16) = χ 9
    rw [show (3 * 16 : ℕ) = 48 by decide]
    exact h48_eq_9
  · show χ 9 = χ (9 + 16)
    rw [show (9 + 16 : ℕ) = 25 by decide]
    exact h25_eq_9.symm

/-- **R352 χ(48) anchor-exclusion pack**: directional outputs (A → χ43,
  B → χ25, C → χ34) packaged via And. -/
theorem bAdicEquation_3_branchII_chi48_anchor_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 27 → χ 43 ≠ χ 27) ∧
    (χ 48 = χ 9  → χ 25 ≠ χ 9) ∧
    (χ 48 = χ 18 → χ 34 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_27
    exact bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
      χ (by omega) hNoMono h48_eq_27
  · intro h48_eq_9
    exact bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h48_eq_9
  · intro h48_eq_18
    exact bAdicEquation_3_chi48_eq_chi18_forces_chi34_ne_chi18
      χ (by omega) hNoMono h48_eq_18

/-- **R352 χ(16) = A → χ(25) ≠ A** via triple (27, 16, 25): 27 + 3·16 = 75 = 3·25.
  Note: n ≥ 27 required (max position in triple is b·d = 27, not z = 25). -/
theorem bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_27 : χ 16 = χ 27) :
    χ 25 ≠ χ 27 := by
  intro h25_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 16
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h16_eq_27.symm
  · show χ 16 = χ (16 + 9)
    rw [show (16 + 9 : ℕ) = 25 by decide]
    exact h16_eq_27.trans h25_eq_27.symm

/-- **R352 χ(16) = B → χ(19) ≠ B** via triple (9, 16, 19): 9 + 3·16 = 57 = 3·19. -/
theorem bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 19 ≠ χ 9 := by
  intro h19_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 16
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h16_eq_9.symm
  · show χ 16 = χ (16 + 3)
    rw [show (16 + 3 : ℕ) = 19 by decide]
    exact h16_eq_9.trans h19_eq_9.symm

/-- **R352 χ(16) anchor-exclusion pack**: directional outputs (A → χ25,
  B → χ19, C → χ22) packaged via And. -/
theorem bAdicEquation_3_branchII_chi16_anchor_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 16 = χ 27 → χ 25 ≠ χ 27) ∧
    (χ 16 = χ 9  → χ 19 ≠ χ 9) ∧
    (χ 16 = χ 18 → χ 22 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h16_eq_27
    exact bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
      χ (by omega) hNoMono h16_eq_27
  · intro h16_eq_9
    exact bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
      χ (by omega) hNoMono h16_eq_9
  · intro h16_eq_18
    exact bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
      χ (by omega) hNoMono h16_eq_18

/-- **R352 χ(22) = A → χ(31) ≠ A** via triple (27, 22, 31): 27 + 3·22 = 93 = 3·31. -/
theorem bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h31 : 31 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_27 : χ 22 = χ 27) :
    χ 31 ≠ χ 27 := by
  intro h31_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 22) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 22
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h22_eq_27.symm
  · show χ 22 = χ (22 + 9)
    rw [show (22 + 9 : ℕ) = 31 by decide]
    exact h22_eq_27.trans h31_eq_27.symm

/-- **R352 χ(22) = B → χ(25) ≠ B** via triple (9, 22, 25): 9 + 3·22 = 75 = 3·25. -/
theorem bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h25 : 25 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_9 : χ 22 = χ 9) :
    χ 25 ≠ χ 9 := by
  intro h25_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 22) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 22
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h22_eq_9.symm
  · show χ 22 = χ (22 + 3)
    rw [show (22 + 3 : ℕ) = 25 by decide]
    exact h22_eq_9.trans h25_eq_9.symm

/-- **R352 χ(22) anchor-exclusion pack**: directional outputs (A → χ31,
  B → χ25, C → χ28) packaged via And. -/
theorem bAdicEquation_3_branchII_chi22_anchor_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 22 = χ 27 → χ 31 ≠ χ 27) ∧
    (χ 22 = χ 9  → χ 25 ≠ χ 9) ∧
    (χ 22 = χ 18 → χ 28 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h22_eq_27
    exact bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
      χ (by omega) hNoMono h22_eq_27
  · intro h22_eq_9
    exact bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h22_eq_9
  · intro h22_eq_18
    exact bAdicEquation_3_chi22_eq_chi18_forces_chi28_ne_chi18
      χ (by omega) hNoMono h22_eq_18

/-! ### §193. R353 — χ(25) convergence-node exclusion / forcing system.

  R352 revealed χ25 as a convergence transfer node: 3 independent same-color
  exclusion paths from χ48=B, χ16=A, χ22=B. R353 packages these, adds the
  missing C-exclusion via triple (18, 19, 25), and constructs χ25 ABC
  single-color forcing theorems using R349 helpers.

  Deliverables:
  - **Target A** `chi25_exclusion_pack`: And of 3 R352 exclusions.
  - **Target B** `chi19_eq_chi18_forces_chi25_ne_chi18` via (18, 19, 25).
  - **Target C** `chi25_exclusion_pack_extended`: 4-And including Target B.
  - **Target D** 4 χ25ABC single-color forcing theorems combining 2 exclusions
    from {χ48=B, χ16=A, χ22=B, χ19=C}.

  **Audit Target E — χ25ABC availability**: NO unconditional χ25 ∈ ABC
  classification currently exists. χ25 carries only exclusion conditions,
  not positive anchor memberships. The forcing theorems require both
  χ25ABC and 2 exclusions; they are **future leverage** awaiting a
  dispatcher that establishes χ25 ∈ ABC.

  **Audit Target F — Route to χ25ABC**:
  - No direct self-loop (25 ≠ 3·d; xy self-loop (3m, 3m, 4m) at m=25/4
    not integer; xz self-loop (3d, 2d, 3d) doesn't reach 25).
  - Future option: 4-color exhaustion under enough exclusions forces
    χ25 = anchor (the fourth-color analysis pattern from R320/R326).
  - Network connections: χ25 ↔ {χ31 (via R352 χ22=A), χ19 (R352 χ16=B),
    χ43 (R352 χ48=A)} await mutual constraints.
-/

/-- **R353 Target A — χ(25) exclusion pack**: package 3 R352 χ25 same-color
  exclusion implications (χ48=B, χ16=A, χ22=B sources). -/
theorem bAdicEquation_3_branchII_chi25_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 9  → χ 25 ≠ χ 9) ∧
    (χ 16 = χ 27 → χ 25 ≠ χ 27) ∧
    (χ 22 = χ 9  → χ 25 ≠ χ 9) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_9
    exact bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h48_eq_9
  · intro h16_eq_27
    exact bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
      χ (by omega) hNoMono h16_eq_27
  · intro h22_eq_9
    exact bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h22_eq_9

/-- **R353 Target B — `χ(19)=C → χ(25) ≠ C`** via triple (18, 19, 25):
  18 + 3·19 = 75 = 3·25. b=3, d=6, y=19. -/
theorem bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h25 : 25 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h19_eq_18 : χ 19 = χ 18) :
    χ 25 ≠ χ 18 := by
  intro h25_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 19
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h19_eq_18.symm
  · show χ 19 = χ (19 + 6)
    rw [show (19 + 6 : ℕ) = 25 by decide]
    exact h19_eq_18.trans h25_eq_18.symm

/-- **R353 Target C — χ(25) exclusion pack extended**: 4-And including R353
  Target B's C-exclusion. -/
theorem bAdicEquation_3_branchII_chi25_exclusion_pack_extended
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 9  → χ 25 ≠ χ 9) ∧
    (χ 16 = χ 27 → χ 25 ≠ χ 27) ∧
    (χ 22 = χ 9  → χ 25 ≠ χ 9) ∧
    (χ 19 = χ 18 → χ 25 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h48_eq_9
    exact bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h48_eq_9
  · intro h16_eq_27
    exact bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
      χ (by omega) hNoMono h16_eq_27
  · intro h22_eq_9
    exact bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
      χ (by omega) hNoMono h22_eq_9
  · intro h19_eq_18
    exact bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
      χ (by omega) hNoMono h19_eq_18

/-- **R353 Target D-1 — χ16=A + χ48=B + χ25ABC ⇒ χ25 = C**. -/
theorem bAdicEquation_3_branchII_chi25ABC_forces_C_of_chi16A_and_chi48B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_27 : χ 16 = χ 27)
    (h48_eq_9 : χ 48 = χ 9)
    (h25ABC : χ 25 = χ 27 ∨ χ 25 = χ 9 ∨ χ 25 = χ 18) :
    χ 25 = χ 18 := by
  have h25_ne_27 := bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
    χ (by omega) hNoMono h16_eq_27
  have h25_ne_9 := bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
    χ (by omega) hNoMono h48_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h25ABC h25_ne_27 h25_ne_9

/-- **R353 Target D-2 — χ16=A + χ22=B + χ25ABC ⇒ χ25 = C**. -/
theorem bAdicEquation_3_branchII_chi25ABC_forces_C_of_chi16A_and_chi22B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_27 : χ 16 = χ 27)
    (h22_eq_9 : χ 22 = χ 9)
    (h25ABC : χ 25 = χ 27 ∨ χ 25 = χ 9 ∨ χ 25 = χ 18) :
    χ 25 = χ 18 := by
  have h25_ne_27 := bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
    χ (by omega) hNoMono h16_eq_27
  have h25_ne_9 := bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
    χ (by omega) hNoMono h22_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h25ABC h25_ne_27 h25_ne_9

/-- **R353 Target D-3 — χ48=B + χ19=C + χ25ABC ⇒ χ25 = A**. -/
theorem bAdicEquation_3_branchII_chi25ABC_forces_A_of_chi48B_and_chi19C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h19_eq_18 : χ 19 = χ 18)
    (h25ABC : χ 25 = χ 27 ∨ χ 25 = χ 9 ∨ χ 25 = χ 18) :
    χ 25 = χ 27 := by
  have h25_ne_9 := bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
    χ (by omega) hNoMono h48_eq_9
  have h25_ne_18 := bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
    χ (by omega) hNoMono h19_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h25ABC h25_ne_9 h25_ne_18

/-- **R353 Target D-4 — χ16=A + χ19=C + χ25ABC ⇒ χ25 = B**. -/
theorem bAdicEquation_3_branchII_chi25ABC_forces_B_of_chi16A_and_chi19C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_27 : χ 16 = χ 27)
    (h19_eq_18 : χ 19 = χ 18)
    (h25ABC : χ 25 = χ 27 ∨ χ 25 = χ 9 ∨ χ 25 = χ 18) :
    χ 25 = χ 9 := by
  have h25_ne_27 := bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
    χ (by omega) hNoMono h16_eq_27
  have h25_ne_18 := bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
    χ (by omega) hNoMono h19_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h25ABC h25_ne_27 h25_ne_18

/-! ### §194. R354 — χ(19) transfer-control network.

  Audit (Part 1): **χ25 ABC has no direct unconditional source**. χ25 is
  not a self-loop position (25 ≠ 3·d and 25 ≠ 4·m); all χ25 lemmas in
  R353 are conditional same-color exclusions. χ25 ∈ ABC requires
  future 4-color exhaustion or external dispatcher.

  Pivot (Part 2): Build χ19 transfer-control network. χ19 connects to
  χ25/χ22/χ28 outputs AND has its own anchor-exclusion family.

  Deliverables:
  - **Target B** `χ19=B → χ22≠B` via triple (9, 19, 22).
  - **Target C** `χ19=A → χ28≠A` via triple (27, 19, 28).
  - **Target D-A** `χ10=A → χ19≠A` via triple (27, 10, 19).
  - **Target D-C** `χ13=C → χ19≠C` via triple (18, 13, 19).
  - **Target E** `chi19_directional_exclusion_pack`: And of 3 anchor
    exclusions (R352 B-exclusion plus R354 A and C exclusions).
  - **Target F** `chi19_transfer_pack`: And of 4 χ19-related implications.
  - **Target G** 3 χ19ABC forcing theorems (G1/G2/G3) using R349 helpers.

  **Audit Target H — χ19ABC availability**: NO unconditional source. χ19
  shares χ25's structural limitation (non-self-loop position). χ19ABC
  forcing theorems are future leverage.
-/

/-- **R354 Target B — `χ(19)=B → χ(22) ≠ B`** via triple (9, 19, 22):
  9 + 3·19 = 66 = 3·22. -/
theorem bAdicEquation_3_chi19_eq_chi9_forces_chi22_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h22 : 22 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h19_eq_9 : χ 19 = χ 9) :
    χ 22 ≠ χ 9 := by
  intro h22_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 19
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h19_eq_9.symm
  · show χ 19 = χ (19 + 3)
    rw [show (19 + 3 : ℕ) = 22 by decide]
    exact h19_eq_9.trans h22_eq_9.symm

/-- **R354 Target C — `χ(19)=A → χ(28) ≠ A`** via triple (27, 19, 28):
  27 + 3·19 = 84 = 3·28. -/
theorem bAdicEquation_3_chi19_eq_chi27_forces_chi28_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h28 : 28 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h19_eq_27 : χ 19 = χ 27) :
    χ 28 ≠ χ 27 := by
  intro h28_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 19
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h19_eq_27.symm
  · show χ 19 = χ (19 + 9)
    rw [show (19 + 9 : ℕ) = 28 by decide]
    exact h19_eq_27.trans h28_eq_27.symm

/-- **R354 Target D-A — `χ(10)=A → χ(19) ≠ A`** via triple (27, 10, 19):
  27 + 3·10 = 57 = 3·19. n ≥ 27 required (max position is b·d = 27). -/
theorem bAdicEquation_3_chi10_eq_chi27_forces_chi19_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h27 : 27 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h10_eq_27 : χ 10 = χ 27) :
    χ 19 ≠ χ 27 := by
  intro h19_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 10) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 10
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h10_eq_27.symm
  · show χ 10 = χ (10 + 9)
    rw [show (10 + 9 : ℕ) = 19 by decide]
    exact h10_eq_27.trans h19_eq_27.symm

/-- **R354 Target D-C — `χ(13)=C → χ(19) ≠ C`** via triple (18, 13, 19):
  18 + 3·13 = 57 = 3·19. -/
theorem bAdicEquation_3_chi13_eq_chi18_forces_chi19_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h19 : 19 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h13_eq_18 : χ 13 = χ 18) :
    χ 19 ≠ χ 18 := by
  intro h19_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 13) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 13
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h13_eq_18.symm
  · show χ 13 = χ (13 + 6)
    rw [show (13 + 6 : ℕ) = 19 by decide]
    exact h13_eq_18.trans h19_eq_18.symm

/-- **R354 Target E — χ(19) directional exclusion pack**: 3 anchor
  exclusions (A via χ10, B via χ16, C via χ13). -/
theorem bAdicEquation_3_branchII_chi19_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 10 = χ 27 → χ 19 ≠ χ 27) ∧
    (χ 16 = χ 9  → χ 19 ≠ χ 9) ∧
    (χ 13 = χ 18 → χ 19 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h10_eq_27
    exact bAdicEquation_3_chi10_eq_chi27_forces_chi19_ne_chi27
      χ (by omega) hNoMono h10_eq_27
  · intro h16_eq_9
    exact bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
      χ (by omega) hNoMono h16_eq_9
  · intro h13_eq_18
    exact bAdicEquation_3_chi13_eq_chi18_forces_chi19_ne_chi18
      χ (by omega) hNoMono h13_eq_18

/-- **R354 Target F — χ(19) transfer-control pack**: 4-And of χ19-related
  implications (1 incoming exclusion via χ16=B, 3 outgoing to χ25/χ22/χ28). -/
theorem bAdicEquation_3_branchII_chi19_transfer_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 16 = χ 9  → χ 19 ≠ χ 9) ∧
    (χ 19 = χ 18 → χ 25 ≠ χ 18) ∧
    (χ 19 = χ 9  → χ 22 ≠ χ 9) ∧
    (χ 19 = χ 27 → χ 28 ≠ χ 27) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h16_eq_9
    exact bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
      χ (by omega) hNoMono h16_eq_9
  · intro h19_eq_18
    exact bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
      χ (by omega) hNoMono h19_eq_18
  · intro h19_eq_9
    exact bAdicEquation_3_chi19_eq_chi9_forces_chi22_ne_chi9
      χ (by omega) hNoMono h19_eq_9
  · intro h19_eq_27
    exact bAdicEquation_3_chi19_eq_chi27_forces_chi28_ne_chi27
      χ (by omega) hNoMono h19_eq_27

/-- **R354 Target G-1 — χ10=A + χ16=B + χ19ABC ⇒ χ19 = C**. -/
theorem bAdicEquation_3_branchII_chi19ABC_forces_C_of_chi10A_chi16B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h10_eq_27 : χ 10 = χ 27)
    (h16_eq_9 : χ 16 = χ 9)
    (h19ABC : χ 19 = χ 27 ∨ χ 19 = χ 9 ∨ χ 19 = χ 18) :
    χ 19 = χ 18 := by
  have h19_ne_27 := bAdicEquation_3_chi10_eq_chi27_forces_chi19_ne_chi27
    χ (by omega) hNoMono h10_eq_27
  have h19_ne_9 := bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
    χ (by omega) hNoMono h16_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h19ABC h19_ne_27 h19_ne_9

/-- **R354 Target G-2 — χ10=A + χ13=C + χ19ABC ⇒ χ19 = B**. -/
theorem bAdicEquation_3_branchII_chi19ABC_forces_B_of_chi10A_chi13C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h10_eq_27 : χ 10 = χ 27)
    (h13_eq_18 : χ 13 = χ 18)
    (h19ABC : χ 19 = χ 27 ∨ χ 19 = χ 9 ∨ χ 19 = χ 18) :
    χ 19 = χ 9 := by
  have h19_ne_27 := bAdicEquation_3_chi10_eq_chi27_forces_chi19_ne_chi27
    χ (by omega) hNoMono h10_eq_27
  have h19_ne_18 := bAdicEquation_3_chi13_eq_chi18_forces_chi19_ne_chi18
    χ (by omega) hNoMono h13_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h19ABC h19_ne_27 h19_ne_18

/-- **R354 Target G-3 — χ16=B + χ13=C + χ19ABC ⇒ χ19 = A**. -/
theorem bAdicEquation_3_branchII_chi19ABC_forces_A_of_chi16B_chi13C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_9 : χ 16 = χ 9)
    (h13_eq_18 : χ 13 = χ 18)
    (h19ABC : χ 19 = χ 27 ∨ χ 19 = χ 9 ∨ χ 19 = χ 18) :
    χ 19 = χ 27 := by
  have h19_ne_9 := bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
    χ (by omega) hNoMono h16_eq_9
  have h19_ne_18 := bAdicEquation_3_chi13_eq_chi18_forces_chi19_ne_chi18
    χ (by omega) hNoMono h13_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h19ABC h19_ne_9 h19_ne_18

/-! ### §195. R355 — Output-node directional networks for χ(31) and χ(43).

  Part 1: χ31 network. R352 already gave `χ22=A → χ31≠A`. R355 adds
  B and C exclusions, package, and 3 forcing theorems.

  Part 2: χ43 network. R352 already gave `χ48=A → χ43≠A`. R355 adds
  B and C exclusions, package, and 3 forcing theorems.

  Active value:
  - χ31 connects to χ22, χ28, χ25 — all active transfer nodes. High value.
  - χ43 connects to χ48 (active), χ40, χ37 (not yet active). Lower
    immediate value but builds output-node graph for future use.
-/

/-- **R355 χ(28)=B → χ(31) ≠ B** via triple (9, 28, 31): 9 + 3·28 = 93 = 3·31. -/
theorem bAdicEquation_3_chi28_eq_chi9_forces_chi31_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h31 : 31 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h28_eq_9 : χ 28 = χ 9) :
    χ 31 ≠ χ 9 := by
  intro h31_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 28
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h28_eq_9.symm
  · show χ 28 = χ (28 + 3)
    rw [show (28 + 3 : ℕ) = 31 by decide]
    exact h28_eq_9.trans h31_eq_9.symm

/-- **R355 χ(25)=C → χ(31) ≠ C** via triple (18, 25, 31): 18 + 3·25 = 93 = 3·31. -/
theorem bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h31 : 31 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h25_eq_18 : χ 25 = χ 18) :
    χ 31 ≠ χ 18 := by
  intro h31_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 25) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 25
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h25_eq_18.symm
  · show χ 25 = χ (25 + 6)
    rw [show (25 + 6 : ℕ) = 31 by decide]
    exact h25_eq_18.trans h31_eq_18.symm

/-- **R355 χ(31) directional exclusion pack**: A (χ22), B (χ28), C (χ25). -/
theorem bAdicEquation_3_branchII_chi31_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 22 = χ 27 → χ 31 ≠ χ 27) ∧
    (χ 28 = χ 9  → χ 31 ≠ χ 9) ∧
    (χ 25 = χ 18 → χ 31 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h22_eq_27
    exact bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
      χ (by omega) hNoMono h22_eq_27
  · intro h28_eq_9
    exact bAdicEquation_3_chi28_eq_chi9_forces_chi31_ne_chi9
      χ (by omega) hNoMono h28_eq_9
  · intro h25_eq_18
    exact bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
      χ (by omega) hNoMono h25_eq_18

/-- **R355 χ(31)ABC forces C** of χ22=A ∧ χ28=B. -/
theorem bAdicEquation_3_branchII_chi31ABC_forces_C_of_chi22A_chi28B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_27 : χ 22 = χ 27)
    (h28_eq_9 : χ 28 = χ 9)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 18 := by
  have h31_ne_27 := bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
    χ (by omega) hNoMono h22_eq_27
  have h31_ne_9 := bAdicEquation_3_chi28_eq_chi9_forces_chi31_ne_chi9
    χ (by omega) hNoMono h28_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h31ABC h31_ne_27 h31_ne_9

/-- **R355 χ(31)ABC forces B** of χ22=A ∧ χ25=C. -/
theorem bAdicEquation_3_branchII_chi31ABC_forces_B_of_chi22A_chi25C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h22_eq_27 : χ 22 = χ 27)
    (h25_eq_18 : χ 25 = χ 18)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 9 := by
  have h31_ne_27 := bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
    χ (by omega) hNoMono h22_eq_27
  have h31_ne_18 := bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
    χ (by omega) hNoMono h25_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h31ABC h31_ne_27 h31_ne_18

/-- **R355 χ(31)ABC forces A** of χ28=B ∧ χ25=C. -/
theorem bAdicEquation_3_branchII_chi31ABC_forces_A_of_chi28B_chi25C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h28_eq_9 : χ 28 = χ 9)
    (h25_eq_18 : χ 25 = χ 18)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 27 := by
  have h31_ne_9 := bAdicEquation_3_chi28_eq_chi9_forces_chi31_ne_chi9
    χ (by omega) hNoMono h28_eq_9
  have h31_ne_18 := bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
    χ (by omega) hNoMono h25_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h31ABC h31_ne_9 h31_ne_18

/-- **R355 χ(40)=B → χ(43) ≠ B** via triple (9, 40, 43): 9 + 3·40 = 129 = 3·43. -/
theorem bAdicEquation_3_chi40_eq_chi9_forces_chi43_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h43 : 43 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h40_eq_9 : χ 40 = χ 9) :
    χ 43 ≠ χ 9 := by
  intro h43_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 40) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 40
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h40_eq_9.symm
  · show χ 40 = χ (40 + 3)
    rw [show (40 + 3 : ℕ) = 43 by decide]
    exact h40_eq_9.trans h43_eq_9.symm

/-- **R355 χ(37)=C → χ(43) ≠ C** via triple (18, 37, 43): 18 + 3·37 = 129 = 3·43. -/
theorem bAdicEquation_3_chi37_eq_chi18_forces_chi43_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h43 : 43 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h37_eq_18 : χ 37 = χ 18) :
    χ 43 ≠ χ 18 := by
  intro h43_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 37) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 37
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h37_eq_18.symm
  · show χ 37 = χ (37 + 6)
    rw [show (37 + 6 : ℕ) = 43 by decide]
    exact h37_eq_18.trans h43_eq_18.symm

/-- **R355 χ(43) directional exclusion pack**: A (χ48), B (χ40), C (χ37). -/
theorem bAdicEquation_3_branchII_chi43_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 27 → χ 43 ≠ χ 27) ∧
    (χ 40 = χ 9  → χ 43 ≠ χ 9) ∧
    (χ 37 = χ 18 → χ 43 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_27
    exact bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
      χ (by omega) hNoMono h48_eq_27
  · intro h40_eq_9
    exact bAdicEquation_3_chi40_eq_chi9_forces_chi43_ne_chi9
      χ (by omega) hNoMono h40_eq_9
  · intro h37_eq_18
    exact bAdicEquation_3_chi37_eq_chi18_forces_chi43_ne_chi18
      χ (by omega) hNoMono h37_eq_18

/-- **R355 χ(43)ABC forces C** of χ48=A ∧ χ40=B. -/
theorem bAdicEquation_3_branchII_chi43ABC_forces_C_of_chi48A_chi40B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h40_eq_9 : χ 40 = χ 9)
    (h43ABC : χ 43 = χ 27 ∨ χ 43 = χ 9 ∨ χ 43 = χ 18) :
    χ 43 = χ 18 := by
  have h43_ne_27 := bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
    χ (by omega) hNoMono h48_eq_27
  have h43_ne_9 := bAdicEquation_3_chi40_eq_chi9_forces_chi43_ne_chi9
    χ (by omega) hNoMono h40_eq_9
  exact branchII_ABC_refine_neA_neB_to_C h43ABC h43_ne_27 h43_ne_9

/-- **R355 χ(43)ABC forces B** of χ48=A ∧ χ37=C. -/
theorem bAdicEquation_3_branchII_chi43ABC_forces_B_of_chi48A_chi37C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27)
    (h37_eq_18 : χ 37 = χ 18)
    (h43ABC : χ 43 = χ 27 ∨ χ 43 = χ 9 ∨ χ 43 = χ 18) :
    χ 43 = χ 9 := by
  have h43_ne_27 := bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
    χ (by omega) hNoMono h48_eq_27
  have h43_ne_18 := bAdicEquation_3_chi37_eq_chi18_forces_chi43_ne_chi18
    χ (by omega) hNoMono h37_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h43ABC h43_ne_27 h43_ne_18

/-- **R355 χ(43)ABC forces A** of χ40=B ∧ χ37=C. -/
theorem bAdicEquation_3_branchII_chi43ABC_forces_A_of_chi40B_chi37C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h40_eq_9 : χ 40 = χ 9)
    (h37_eq_18 : χ 37 = χ 18)
    (h43ABC : χ 43 = χ 27 ∨ χ 43 = χ 9 ∨ χ 43 = χ 18) :
    χ 43 = χ 27 := by
  have h43_ne_9 := bAdicEquation_3_chi40_eq_chi9_forces_chi43_ne_chi9
    χ (by omega) hNoMono h40_eq_9
  have h43_ne_18 := bAdicEquation_3_chi37_eq_chi18_forces_chi43_ne_chi18
    χ (by omega) hNoMono h37_eq_18
  exact branchII_ABC_refine_neB_neC_to_A h43ABC h43_ne_9 h43_ne_18

/-! ### §196. R356 — χ(25)/χ(19)/χ(31) internal network + cross-chain (36, 19, 31).

  Part 1: package the existing C-chain χ19=C → χ25≠C → χ31≠C (R353 + R355).

  Part 2: C-propagation refinements `χ25ABC + χ19=C → χ25 ∈ {A,B}` and
  `χ31ABC + χ25=C → χ31 ∈ {A,B}` using R349 helper neC_to_AB.

  Part 3: new cross-chain triple (36, 19, 31): 36 + 3·19 = 93 = 3·31.
  Bridges χ36 (active in χ54-chain), χ19 (transfer-control), χ31 (output).
  Same-color exclusions A/B/C + package + χ31ABC refinements.

  Active value: when χ54=C produces χ36 ∈ {A, B} (R326-C / R343) and a
  future context establishes χ19 ∈ {A, B}, the same-color cross-chain
  activates and refines χ31ABC.
-/

/-- **R356 Part 1 — C-chain pack χ19=C → χ25≠C, χ25=C → χ31≠C**. -/
theorem bAdicEquation_3_branchII_chi19_chi25_chi31_C_chain_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 19 = χ 18 → χ 25 ≠ χ 18) ∧
    (χ 25 = χ 18 → χ 31 ≠ χ 18) := by
  refine ⟨?_, ?_⟩
  · intro h19_eq_18
    exact bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
      χ (by omega) hNoMono h19_eq_18
  · intro h25_eq_18
    exact bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
      χ (by omega) hNoMono h25_eq_18

/-- **R356 Part 2-1 — χ25ABC + χ19=C → χ25 ∈ {A, B}**. -/
theorem bAdicEquation_3_branchII_chi25ABC_refine_of_chi19C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h19_eq_18 : χ 19 = χ 18)
    (h25ABC : χ 25 = χ 27 ∨ χ 25 = χ 9 ∨ χ 25 = χ 18) :
    χ 25 = χ 27 ∨ χ 25 = χ 9 := by
  have h25_ne_18 := bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
    χ (by omega) hNoMono h19_eq_18
  exact branchII_ABC_refine_neC_to_AB h25ABC h25_ne_18

/-- **R356 Part 2-2 — χ31ABC + χ25=C → χ31 ∈ {A, B}**. -/
theorem bAdicEquation_3_branchII_chi31ABC_refine_of_chi25C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h25_eq_18 : χ 25 = χ 18)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 27 ∨ χ 31 = χ 9 := by
  have h31_ne_18 := bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
    χ (by omega) hNoMono h25_eq_18
  exact branchII_ABC_refine_neC_to_AB h31ABC h31_ne_18

/-- **R356 Part 3-A — `χ36=A ∧ χ19=A → χ31 ≠ A`** via triple (36, 19, 31):
  36 + 3·19 = 93 = 3·31. b=3, d=12, y=19. -/
theorem bAdicEquation_3_chi36_eq_chi27_chi19_eq_chi27_forces_chi31_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27)
    (h19_eq_27 : χ 19 = χ 27) :
    χ 31 ≠ χ 27 := by
  intro h31_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 19
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_27.trans h19_eq_27.symm
  · show χ 19 = χ (19 + 12)
    rw [show (19 + 12 : ℕ) = 31 by decide]
    exact h19_eq_27.trans h31_eq_27.symm

/-- **R356 Part 3-B — `χ36=B ∧ χ19=B → χ31 ≠ B`**. -/
theorem bAdicEquation_3_chi36_eq_chi9_chi19_eq_chi9_forces_chi31_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h19_eq_9 : χ 19 = χ 9) :
    χ 31 ≠ χ 9 := by
  intro h31_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 19
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_9.trans h19_eq_9.symm
  · show χ 19 = χ (19 + 12)
    rw [show (19 + 12 : ℕ) = 31 by decide]
    exact h19_eq_9.trans h31_eq_9.symm

/-- **R356 Part 3-C — `χ36=C ∧ χ19=C → χ31 ≠ C`**. -/
theorem bAdicEquation_3_chi36_eq_chi18_chi19_eq_chi18_forces_chi31_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h19_eq_18 : χ 19 = χ 18) :
    χ 31 ≠ χ 18 := by
  intro h31_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 19) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 19
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_18.trans h19_eq_18.symm
  · show χ 19 = χ (19 + 12)
    rw [show (19 + 12 : ℕ) = 31 by decide]
    exact h19_eq_18.trans h31_eq_18.symm

/-- **R356 Part 3 package — χ36/χ19/χ31 cross refinement (A/B/C)**. -/
theorem bAdicEquation_3_branchII_chi36_chi19_chi31_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 36 = χ 27 → χ 19 = χ 27 → χ 31 ≠ χ 27) ∧
    (χ 36 = χ 9  → χ 19 = χ 9  → χ 31 ≠ χ 9) ∧
    (χ 36 = χ 18 → χ 19 = χ 18 → χ 31 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h36_eq_27 h19_eq_27
    exact bAdicEquation_3_chi36_eq_chi27_chi19_eq_chi27_forces_chi31_ne_chi27
      χ (by omega) hNoMono h36_eq_27 h19_eq_27
  · intro h36_eq_9 h19_eq_9
    exact bAdicEquation_3_chi36_eq_chi9_chi19_eq_chi9_forces_chi31_ne_chi9
      χ (by omega) hNoMono h36_eq_9 h19_eq_9
  · intro h36_eq_18 h19_eq_18
    exact bAdicEquation_3_chi36_eq_chi18_chi19_eq_chi18_forces_chi31_ne_chi18
      χ (by omega) hNoMono h36_eq_18 h19_eq_18

/-- **R356 χ31ABC refinement under χ36=A ∧ χ19=A**: χ31 ∈ {B, C}. -/
theorem bAdicEquation_3_branchII_chi31ABC_refine_of_chi36A_chi19A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27)
    (h19_eq_27 : χ 19 = χ 27)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 9 ∨ χ 31 = χ 18 := by
  have h31_ne_27 :=
    bAdicEquation_3_chi36_eq_chi27_chi19_eq_chi27_forces_chi31_ne_chi27
      χ (by omega) hNoMono h36_eq_27 h19_eq_27
  exact branchII_ABC_refine_neA_to_BC h31ABC h31_ne_27

/-- **R356 χ31ABC refinement under χ36=B ∧ χ19=B**: χ31 ∈ {A, C}. -/
theorem bAdicEquation_3_branchII_chi31ABC_refine_of_chi36B_chi19B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h19_eq_9 : χ 19 = χ 9)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 27 ∨ χ 31 = χ 18 := by
  have h31_ne_9 :=
    bAdicEquation_3_chi36_eq_chi9_chi19_eq_chi9_forces_chi31_ne_chi9
      χ (by omega) hNoMono h36_eq_9 h19_eq_9
  exact branchII_ABC_refine_neB_to_AC h31ABC h31_ne_9

/-- **R356 χ31ABC refinement under χ36=C ∧ χ19=C**: χ31 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_chi31ABC_refine_of_chi36C_chi19C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h19_eq_18 : χ 19 = χ 18)
    (h31ABC : χ 31 = χ 27 ∨ χ 31 = χ 9 ∨ χ 31 = χ 18) :
    χ 31 = χ 27 ∨ χ 31 = χ 9 := by
  have h31_ne_18 :=
    bAdicEquation_3_chi36_eq_chi18_chi19_eq_chi18_forces_chi31_ne_chi18
      χ (by omega) hNoMono h36_eq_18 h19_eq_18
  exact branchII_ABC_refine_neC_to_AB h31ABC h31_ne_18

/-! ### §197. R357 — Transfer-node ABC activation audit (χ19 / χ25 / χ31).

  **Audit-only round**: no new theorem can honestly be added; documenting
  findings to halt unnecessary expansion of the transfer-control graph.

  **Setup**: many R353–R356 forcing theorems take a hypothesis
  `χ k = χ 27 ∨ χ k = χ 9 ∨ χ k = χ 18` (call this χkABC) for
  `k ∈ {19, 25, 31}`. R357 audits whether any existing theorem PRODUCES
  this hypothesis as a CONCLUSION (i.e., establishes χkABC unconditionally
  under Branch II).

  **Verification method**: grep over Bridge.lean for both hypothesis
  (`(h...ABC : ...)`) and conclusion (`:    χ k = χ 27 ∨ ... :=`) patterns.

  **Findings**:

  1. **χ19ABC**: NOT derivable.
     - All 3 R354 χ19 exclusions are conditional (χ10=A / χ16=B / χ13=C).
     - No unconditional χ19 ≠ D fourth-color exclusion.
     - χ19 is non-self-loop (19 ≠ 3·d, 19 ≠ 4·m); no positive-classifier triple.
     - All grep hits are hypothesis-position consumers.

  2. **χ25ABC**: NOT derivable.
     - All 4 R353 χ25 exclusions are conditional.
     - χ25 is non-self-loop (25 ≠ 3·d, 25 ≠ 4·m); no positive-classifier triple.
     - All grep hits are hypothesis-position consumers.

  3. **χ31ABC**: NOT derivable.
     - All R355 / R356 χ31 exclusions are conditional.
     - χ31 is non-self-loop (31 ≠ 3·d, 31 ≠ 4·m); no positive-classifier triple.
     - All grep hits are hypothesis-position consumers.

  **Verdict**: the transfer-control graph (R353–R356) is currently NOT
  self-activating. It produces forcing/refinement theorems that all require
  external χkABC inputs which do not yet exist.

  **Strategic implication**: stop expanding the χ19/χ25/χ31 transfer graph.
  Future ABC activation must come from one of:
  (a) Direct positive triple — none found by exhaustive search for χ19/25/31.
  (b) 4-color exhaustion in concrete dispatcher context — requires
      establishing all of {A, B, C, D} pairwise distinct AND χk ≠ D.
  (c) IsKColoring 4 + sufficient exclusions to corner χk into ABC by
      arithmetic (omega) — requires ≥ 1 unconditional ≠ to a non-anchor.

  **R358 recommendation**: pivot to the χ54 = C ∧ χ72 = B ∧ χ48 = B
  concrete leaf case where R341 (`chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage`)
  already provides a strong joint coverage. Apply the transfer-graph
  forcing infrastructure there only via the χkABC hypotheses that the
  R341 conclusion itself provides (e.g., χ34 ∈ ABC fallback).
-/

/-! ### §198. R358 — Concrete leaf case χ(54)=C ∧ χ(72)=B ∧ χ(48)=B projections.

  Enter the high-leverage concrete leaf case. R341 (`chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage`)
  provides 3-way over χ33 (A / C / χ22ABC), each carrying a χ51/χ34 coverage
  sub-conclusion. R358 extracts each as a focused projection.

  Deliverables:
  - **Target A** (χ33=C branch): pruned χ51/χ34 coverage via R340-G.
    Conclusion: `(χ51=A ∧ χ44≠A) ∨ χ34 ∈ ABC` — χ51=C eliminated.
  - **Target B** (χ33=A branch): full R335-D χ51/χ34 coverage.
    Conclusion: `((χ51=A ∧ χ44≠A) ∨ (χ51=C ∧ χ35≠C)) ∨ χ34 ∈ ABC`.
  - **Target C** (χ22ABC branch): full R335-D χ51/χ34 coverage. Same
    structure as Target B; h22ABC is a branch label.

  **Audit Target E — direct closure**: NO direct closure. All three
  branches retain χ51 sub-cases and χ34 ∈ ABC fallback. χ34 is the
  common fallback across all three branches.

  **R359 recommendation**: enter the χ34 ∈ ABC sub-branch (the common
  fallback). Split on χ34 = A / B / C:
  - χ34 = B: R347-B gives χ48=B ∧ χ34=B → χ50 ≠ B (active under h48_eq_9).
  - χ34 = A / C: audit for direct interactions.
  R359 should perform this χ34 sub-split and apply R347 cross-chain.
-/

/-- **R358 Target A — χ(54)=C ∧ χ(72)=B ∧ χ(48)=B ∧ χ(33)=C projection**:
  pruned χ51/χ34 coverage. The χ51=C sub-branch is eliminated by R340-G's
  three-chain cross-chain (54, 33, 51). Conclusion: only χ51 = A path
  (with χ44 ≠ A) survives, plus χ34 ∈ ABC fallback. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_33C_refines_chi51_chi34
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h33_eq_18 : χ 33 = χ 18) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :=
  bAdicEquation_3_branchII_chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9 h54_eq_18 h33_eq_18

/-- **R358 Target B — χ(54)=C ∧ χ(72)=B ∧ χ(48)=B ∧ χ(33)=A projection**:
  full R335-D χ51/χ34 coverage. The χ33=A condition (via R337-D) gives
  χ38≠A but does not interact with χ51/χ34 directly, so R335-D coverage
  is unchanged. Both χ51=A and χ51=C sub-cases remain. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_33A_refines_chi51_chi34
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (_h33_eq_27 : χ 33 = χ 27) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :=
  bAdicEquation_3_branchII_chi48_eq9_branch_expanded
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9

/-- **R358 Target C — χ(54)=C ∧ χ(72)=B ∧ χ(48)=B ∧ χ(22) ∈ ABC projection**:
  full R335-D χ51/χ34 coverage. The h22ABC hypothesis is a branch label
  (from R337-D fallback); it does not interact with χ51/χ34, so R335-D
  coverage is unchanged. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_22ABC_refines_chi51_chi34
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (_h22ABC : χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18)) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :=
  bAdicEquation_3_branchII_chi48_eq9_branch_expanded
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9

/-! ### §199. R359 — χ(34) ∈ ABC split under concrete leaf χ(48)=B.

  R358 left χ34 ∈ ABC as the common fallback across all three branches
  of the χ54=C ∧ χ72=B ∧ χ48=B context. R359 enters this χ34 ∈ ABC
  sub-split.

  Deliverables:
  - **Part 2** `chi34_eq_chi27_forces_chi43_ne_chi27` via (27, 34, 43).
  - **Part 3** `chi34_eq_chi9_forces_chi37_ne_chi9` via (9, 34, 37).
  - **Part 4** `chi34_eq_chi18_forces_chi40_ne_chi18` via (18, 34, 40).
  - **Part 5** `chi34_directional_output_pack`: And of 3 implications.
  - **Part 6** `chi34ABC_split_outputs` under h48_eq_9: 3-way over χ34,
    χ34=B branch includes BOTH χ37 ≠ B AND χ50 ≠ B (R347-B activation).

  Note: R347-B `chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9` and
  R347's `chi50ABC_refine_of_chi48B_chi34B` already exist; Part 1's
  refined theorems are NOT duplicated. The χ34=B branch in Part 6
  combines them.

  **Audit**: no direct closure. χ34ABC now refines to {A → χ43≠A,
  B → χ37≠B ∧ χ50≠B, C → χ40≠C}. The χ34=B sub-branch is most
  constrained (2 forced exclusions).
-/

/-- **R359 χ(34) = A → χ(43) ≠ A** via triple (27, 34, 43): 27 + 3·34 = 129 = 3·43. -/
theorem bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h43 : 43 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h34_eq_27 : χ 34 = χ 27) :
    χ 43 ≠ χ 27 := by
  intro h43_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 34
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h34_eq_27.symm
  · show χ 34 = χ (34 + 9)
    rw [show (34 + 9 : ℕ) = 43 by decide]
    exact h34_eq_27.trans h43_eq_27.symm

/-- **R359 χ(34) = B → χ(37) ≠ B** via triple (9, 34, 37): 9 + 3·34 = 111 = 3·37. -/
theorem bAdicEquation_3_chi34_eq_chi9_forces_chi37_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h37 : 37 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h34_eq_9 : χ 34 = χ 9) :
    χ 37 ≠ χ 9 := by
  intro h37_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 34
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h34_eq_9.symm
  · show χ 34 = χ (34 + 3)
    rw [show (34 + 3 : ℕ) = 37 by decide]
    exact h34_eq_9.trans h37_eq_9.symm

/-- **R359 χ(34) = C → χ(40) ≠ C** via triple (18, 34, 40): 18 + 3·34 = 120 = 3·40. -/
theorem bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h40 : 40 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h34_eq_18 : χ 34 = χ 18) :
    χ 40 ≠ χ 18 := by
  intro h40_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 34
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h34_eq_18.symm
  · show χ 34 = χ (34 + 6)
    rw [show (34 + 6 : ℕ) = 40 by decide]
    exact h34_eq_18.trans h40_eq_18.symm

/-- **R359 χ(34) directional output pack**: A (→ χ43), B (→ χ37), C (→ χ40). -/
theorem bAdicEquation_3_branchII_chi34_directional_output_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 34 = χ 27 → χ 43 ≠ χ 27) ∧
    (χ 34 = χ 9  → χ 37 ≠ χ 9) ∧
    (χ 34 = χ 18 → χ 40 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h34_eq_27
    exact bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
      χ (by omega) hNoMono h34_eq_27
  · intro h34_eq_9
    exact bAdicEquation_3_chi34_eq_chi9_forces_chi37_ne_chi9
      χ (by omega) hNoMono h34_eq_9
  · intro h34_eq_18
    exact bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
      χ (by omega) hNoMono h34_eq_18

/-- **R359 Part 6 — χ(34) ∈ ABC split under χ(48)=B**: 3-way over χ34
  cases. The χ34=B middle branch carries BOTH χ37 ≠ B (R359) AND χ50 ≠ B
  (R347-B activated by h48_eq_9 ∧ χ34=B). -/
theorem bAdicEquation_3_branchII_case_48B_chi34ABC_split_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34ABC : χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :
    (χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
    (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
    (χ 34 = χ 18 ∧ χ 40 ≠ χ 18) := by
  rcases h34ABC with h34A | h34BC
  · -- χ34 = A: R359 χ43 ≠ A
    have h43_ne_27 :=
      bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
        χ (by omega) hNoMono h34A
    exact Or.inl ⟨h34A, h43_ne_27⟩
  · rcases h34BC with h34B | h34C
    · -- χ34 = B: combine R359 χ37 ≠ B and R347-B χ50 ≠ B.
      have h37_ne_9 :=
        bAdicEquation_3_chi34_eq_chi9_forces_chi37_ne_chi9
          χ (by omega) hNoMono h34B
      have h50_ne_9 :=
        bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
          χ (by omega) hNoMono h48_eq_9 h34B
      exact Or.inr (Or.inl ⟨h34B, h37_ne_9, h50_ne_9⟩)
    · -- χ34 = C: R359 χ40 ≠ C.
      have h40_ne_18 :=
        bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
          χ (by omega) hNoMono h34C
      exact Or.inr (Or.inr ⟨h34C, h40_ne_18⟩)

/-! ### §200. R360 — χ(34)=B focused theorem + χ(51) directional outputs.

  **Part 1**: χ34=B focused alias combining R359 + R347-B (And of two
  exclusions in the joint context χ48=B ∧ χ34=B).

  **Audit Parts 2 & 3**: in the current leaf χ54=C ∧ χ72=B ∧ χ48=B ∧
  χ34=B:
  - **χ50ABC unavailable**: R331-A / R333 / R334 / R342-C produce χ50ABC
    only on the χ48=A path. Under χ48=B (current leaf), no χ50ABC source.
    Therefore χ50 ≠ B (from R347-B) is future leverage.
  - **χ37ABC unavailable**: χ37 appears only as output target (χ34=B →
    χ37≠B; χ37=C → χ43≠C in R355 χ43 network). No χ37 ABC dispatcher.
    Therefore χ37 ≠ B is future leverage.

  **Part 4**: New χ51 directional outputs:
  - χ51=A → χ44≠A (R335, existing)
  - χ51=B → χ54≠B via (9, 51, 54)
  - χ51=C → χ57≠C via (18, 51, 57)
  Note: χ51=C → χ35≠C (R335) and χ51=C → χ57≠C (new) are BOTH valid;
  the R360 directional pack uses χ57 as the new output to keep
  per-anchor output uniformity (44 / 54 / 57).

  **Part 5**: χ54=C ∧ χ51=C → χ57≠C focused alias (delegates to χ51=C → χ57≠C;
  χ54=C hypothesis is context-marker only).

  **R361 recommendation**: explore χ57 ABC source (χ57 = 3·19, layer
  position) since χ51=C output χ57≠C now exists. Or pivot to combine
  R358 χ51 sub-cases with R360 χ51 outputs in the χ54=C leaf.
-/

/-- **R360 Part 1 — χ(34)=B focused theorem under χ(48)=B**: And of χ37≠B
  (R359) and χ50≠B (R347-B). Both forced under h48_eq_9 ∧ h34_eq_9. -/
theorem bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9) :
    χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9 := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi34_eq_chi9_forces_chi37_ne_chi9
      χ (by omega) hNoMono h34_eq_9
  · exact bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
      χ (by omega) hNoMono h48_eq_9 h34_eq_9

/-- **R360 Part 4 — χ(51)=B → χ(54) ≠ B** via triple (9, 51, 54):
  9 + 3·51 = 162 = 3·54. -/
theorem bAdicEquation_3_chi51_eq_chi9_forces_chi54_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h54 : 54 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_9 : χ 51 = χ 9) :
    χ 54 ≠ χ 9 := by
  intro h54_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 51) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 51
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h51_eq_9.symm
  · show χ 51 = χ (51 + 3)
    rw [show (51 + 3 : ℕ) = 54 by decide]
    exact h51_eq_9.trans h54_eq_9.symm

/-- **R360 Part 4 — χ(51)=C → χ(57) ≠ C** via triple (18, 51, 57):
  18 + 3·51 = 171 = 3·57. χ57 is layer (3·19); new layer output. -/
theorem bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18) :
    χ 57 ≠ χ 18 := by
  intro h57_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 51) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 51
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h51_eq_18.symm
  · show χ 51 = χ (51 + 6)
    rw [show (51 + 6 : ℕ) = 57 by decide]
    exact h51_eq_18.trans h57_eq_18.symm

/-- **R360 χ(51) directional output pack**: A → χ44 (R335), B → χ54 (R360),
  C → χ57 (R360). -/
theorem bAdicEquation_3_branchII_chi51_directional_output_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 51 = χ 27 → χ 44 ≠ χ 27) ∧
    (χ 51 = χ 9  → χ 54 ≠ χ 9) ∧
    (χ 51 = χ 18 → χ 57 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h51_eq_27
    exact bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
      χ (by omega) hNoMono h51_eq_27
  · intro h51_eq_9
    exact bAdicEquation_3_chi51_eq_chi9_forces_chi54_ne_chi9
      χ (by omega) hNoMono h51_eq_9
  · intro h51_eq_18
    exact bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
      χ (by omega) hNoMono h51_eq_18

/-- **R360 Part 5 — χ(54)=C ∧ χ(51)=C → χ(57) ≠ C focused alias**.
  Delegates to R360 χ51=C → χ57≠C. h54_eq_18 is context-marker only. -/
theorem bAdicEquation_3_branchII_case_54C_chi51C_forces_chi57_ne_C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h54_eq_18 : χ 54 = χ 18)
    (h51_eq_18 : χ 51 = χ 18) :
    χ 57 ≠ χ 18 :=
  bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
    χ (by omega) hNoMono h51_eq_18

/-! ### §201. R361 — χ(51) double exclusions + layer output pack.

  Strengthen χ51 sub-branches that appear in R358 projections by combining
  existing transfer exclusions (R335) with R360 layer outputs.

  Deliverables:
  - **Part 1** chi51C_forces_chi35_and_chi57_ne_C: χ51=C double exclusion
    (R335 χ35≠C + R360 χ57≠C).
  - **Part 2** chi51_eq_chi27_forces_chi60_ne_chi27: new χ51=A → χ60≠A
    via (27, 51, 60). χ60 = 3·20 is layer.
  - **Part 2 combined** chi51A_forces_chi44_and_chi60_ne_A: χ51=A double
    exclusion (R335 χ44≠A + R361 χ60≠A).
  - **Part 3** chi51_layer_output_pack: A → χ60, B → χ54, C → χ57.
  - **Part 4** case_54C_72B_48B_51A_forces_layer60_ne_A: leaf alias.

  **Audit Part 5 — χ57ABC / χ60ABC availability**: NEITHER is currently
  derivable. χ57 = 3·19 and χ60 = 3·20 are both layer positions but no
  ABC dispatcher targets them. The new layer exclusions are future
  leverage; they refine the χ51 branches into stronger hypotheses but
  do not close in the current concrete leaf.

  **Part 6 — Current leaf impact**:
  - χ33=C branch (R358 Target A): χ51=A now gives χ44≠A ∧ χ60≠A; χ34ABC
    uses R359 split.
  - χ33=A / χ22ABC branches (R358 Targets B, C): χ51=A gives χ44≠A ∧ χ60≠A;
    χ51=C gives χ35≠C ∧ χ57≠C; χ34ABC uses R359 split.

  All R358 projections now have richer χ51 exclusions, but the
  fundamental χ51/χ34 disjunction structure unchanged.
-/

/-- **R361 Part 1 — χ(51)=C double exclusion**: combine R335 χ35≠C with
  R360 χ57≠C. -/
theorem bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18) :
    χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18 := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
      χ (by omega) hNoMono h51_eq_18
  · exact bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
      χ (by omega) hNoMono h51_eq_18

/-- **R361 Part 2 — χ(51)=A → χ(60) ≠ A** via triple (27, 51, 60):
  27 + 3·51 = 180 = 3·60. χ60 = 3·20 (layer position). -/
theorem bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_27 : χ 51 = χ 27) :
    χ 60 ≠ χ 27 := by
  intro h60_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 51) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 51
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h51_eq_27.symm
  · show χ 51 = χ (51 + 9)
    rw [show (51 + 9 : ℕ) = 60 by decide]
    exact h51_eq_27.trans h60_eq_27.symm

/-- **R361 Part 2 combined — χ(51)=A double exclusion**: combine R335 χ44≠A
  with R361 χ60≠A. -/
theorem bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_27 : χ 51 = χ 27) :
    χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27 := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
      χ (by omega) hNoMono h51_eq_27
  · exact bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
      χ (by omega) hNoMono h51_eq_27

/-- **R361 Part 3 — χ(51) layer output pack**: A → χ60, B → χ54, C → χ57. -/
theorem bAdicEquation_3_branchII_chi51_layer_output_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 51 = χ 27 → χ 60 ≠ χ 27) ∧
    (χ 51 = χ 9  → χ 54 ≠ χ 9) ∧
    (χ 51 = χ 18 → χ 57 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h51_eq_27
    exact bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
      χ (by omega) hNoMono h51_eq_27
  · intro h51_eq_9
    exact bAdicEquation_3_chi51_eq_chi9_forces_chi54_ne_chi9
      χ (by omega) hNoMono h51_eq_9
  · intro h51_eq_18
    exact bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
      χ (by omega) hNoMono h51_eq_18

/-- **R361 Part 4 — current leaf χ54=C ∧ χ72=B ∧ χ48=B ∧ χ51=A forces χ60 ≠ A**:
  leaf alias delegating to R361 χ51=A → χ60≠A. Context hypotheses are markers. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_51A_forces_layer60_ne_A
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (_h48_eq_9 : χ 48 = χ 9)
    (h51_eq_27 : χ 51 = χ 27) :
    χ 60 ≠ χ 27 :=
  bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
    χ (by omega) hNoMono h51_eq_27

/-! ### §202. R362 — Refined output projections for χ(54)=C ∧ χ(72)=B ∧ χ(48)=B.

  Integrate R358 + R359 + R361 into refined leaf-output projections,
  one per R358 sub-branch (χ33=C, χ33=A, χ22ABC). Each refined projection
  enriches:
  - χ51=A sub-branch with χ60 ≠ A (R361);
  - χ51=C sub-branch with χ57 ≠ C (R361);
  - χ34ABC fallback with R359 split (3 sub-cases with forced exclusions).

  **Output Frontier** (Part 4 audit):

  | branch         | exclusion(s)              | classification |
  |----------------|---------------------------|----------------|
  | χ51=A          | χ44 ≠ A, χ60 ≠ A          | χ60 is layer (3·20); χ44 transfer |
  | χ51=C          | χ35 ≠ C, χ57 ≠ C          | χ57 is layer (3·19); χ35 transfer |
  | χ34=A          | χ43 ≠ A                   | χ43 transfer |
  | χ34=B          | χ37 ≠ B, χ50 ≠ B          | both transfer |
  | χ34=C          | χ40 ≠ C                   | χ40 transfer |

  **No direct closure**. The refined projections expose 2 layer outputs
  (χ60, χ57) and 5 transfer outputs (χ44, χ35, χ43, χ37, χ50, χ40).

  **R363 recommendation**: attack the 2 layer outputs (χ60, χ57) first:
  audit χ60ABC / χ57ABC direct sources; build directional output packs
  for χ60 and χ57; or search cross-chain triples involving these layers
  with active nodes.
-/

/-- **R362 χ33=C refined output projection**: under R358 χ33=C branch,
  enrich χ51=A with χ60≠A and χ34ABC with R359 split.

  Conclusion has 4 leaves: χ51=A (with 2 exclusions) ∨ χ34=A (1 excl)
  ∨ χ34=B (2 excl) ∨ χ34=C (1 excl). -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_33C_refined_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h33_eq_18 : χ 33 = χ 18) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
    ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
     (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
     (χ 34 = χ 18 ∧ χ 40 ≠ χ 18)) := by
  have hR358A := bAdicEquation_3_branchII_case_54C_72B_48B_33C_refines_chi51_chi34
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h72_eq_9 h48_eq_9 h33_eq_18
  rcases hR358A with h51A_44 | h34ABC
  · -- χ51 = A branch: add χ60 ≠ A from R361.
    obtain ⟨h51_eq_27, h44_ne_27⟩ := h51A_44
    have h60_ne_27 := bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
      χ (by omega) hNoMono h51_eq_27
    exact Or.inl ⟨h51_eq_27, h44_ne_27, h60_ne_27⟩
  · -- χ34ABC branch: use R359 split.
    exact Or.inr
      (bAdicEquation_3_branchII_case_48B_chi34ABC_split_outputs
        χ h81 hNoMono h48_eq_9 h34ABC)

/-- **R362 χ33=A refined output projection**: under R358 χ33=A branch,
  enrich χ51=A with χ60≠A and χ51=C with χ57≠C, plus R359 split on χ34ABC.

  Conclusion has 5 leaves: χ51=A (2 excl) ∨ χ51=C (2 excl) ∨ 3 × χ34=X
  with respective exclusions. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_33A_refined_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h33_eq_27 : χ 33 = χ 27) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18)) ∨
    ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
     (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
     (χ 34 = χ 18 ∧ χ 40 ≠ χ 18)) := by
  have hR358B := bAdicEquation_3_branchII_case_54C_72B_48B_33A_refines_chi51_chi34
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h72_eq_9 h48_eq_9 h33_eq_27
  rcases hR358B with h51AC | h34ABC
  · rcases h51AC with h51A_44 | h51C_35
    · -- χ51 = A: add χ60 ≠ A.
      obtain ⟨h51_eq_27, h44_ne_27⟩ := h51A_44
      have h60_ne_27 := bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
        χ (by omega) hNoMono h51_eq_27
      exact Or.inl (Or.inl ⟨h51_eq_27, h44_ne_27, h60_ne_27⟩)
    · -- χ51 = C: add χ57 ≠ C.
      obtain ⟨h51_eq_18, h35_ne_18⟩ := h51C_35
      have h57_ne_18 := bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
        χ (by omega) hNoMono h51_eq_18
      exact Or.inl (Or.inr ⟨h51_eq_18, h35_ne_18, h57_ne_18⟩)
  · -- χ34ABC branch.
    exact Or.inr
      (bAdicEquation_3_branchII_case_48B_chi34ABC_split_outputs
        χ h81 hNoMono h48_eq_9 h34ABC)

/-- **R362 χ22ABC fallback refined output projection**: same enrichment as
  χ33=A. h22ABC is branch label only. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_22ABC_refined_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9)
    (h22ABC : χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) :
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18)) ∨
    ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
     (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
     (χ 34 = χ 18 ∧ χ 40 ≠ χ 18)) := by
  have hR358C := bAdicEquation_3_branchII_case_54C_72B_48B_22ABC_refines_chi51_chi34
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h72_eq_9 h48_eq_9 h22ABC
  rcases hR358C with h51AC | h34ABC
  · rcases h51AC with h51A_44 | h51C_35
    · obtain ⟨h51_eq_27, h44_ne_27⟩ := h51A_44
      have h60_ne_27 := bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
        χ (by omega) hNoMono h51_eq_27
      exact Or.inl (Or.inl ⟨h51_eq_27, h44_ne_27, h60_ne_27⟩)
    · obtain ⟨h51_eq_18, h35_ne_18⟩ := h51C_35
      have h57_ne_18 := bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
        χ (by omega) hNoMono h51_eq_18
      exact Or.inl (Or.inr ⟨h51_eq_18, h35_ne_18, h57_ne_18⟩)
  · exact Or.inr
      (bAdicEquation_3_branchII_case_48B_chi34ABC_split_outputs
        χ h81 hNoMono h48_eq_9 h34ABC)

/-! ### §203. R363 — χ(60) and χ(57) layer-output directional infrastructure.

  Target: build complete A/B/C directional exclusion packs for χ60 and
  χ57 layer outputs. Current leaf χ54=C ∧ χ72=B ∧ χ48=B activates one
  χ60 exclusion (χ60 ≠ C via χ54=C) but NO χ57 exclusion directly.

  **χ60 active leverage**: under χ54=C ∧ χ51=A ∧ χ60ABC, χ60=B is FORCED
  (two exclusions: χ60≠A from χ51=A R361, χ60≠C from χ54=C R363).

  **χ57 weaker**: under χ51=C ∧ χ57ABC, χ57 ∈ {A, B} only (one exclusion).

  Deliverables:
  - **Part 1** new χ60 exclusions:
    * chi54_eq_chi18_forces_chi60_ne_chi18 via (18, 54, 60).
    * chi57_eq_chi9_forces_chi60_ne_chi9 via (9, 57, 60).
    chi60_directional_exclusion_pack: A (R361) + B (new) + C (new).
  - **Part 2** chi60_current_leaf_B_forcing: under χ54=C ∧ χ51=A ∧ χ60ABC,
    χ60 = B.
  - **Part 3** new χ57 exclusions:
    * chi48_eq_chi27_forces_chi57_ne_chi27 via (27, 48, 57).
    * chi54_eq_chi9_forces_chi57_ne_chi9 via (9, 54, 57).
    chi57_directional_exclusion_pack: A (new) + B (new) + C (R360).
  - **Part 4** chi57_chi51C_refines_to_AB: under χ51=C ∧ χ57ABC, χ57 ∈ {A, B}.

  Audit Part 5: no direct closure. χ60 / χ57 ABC sources still absent.
  But χ60 is closer to closure (2 active exclusions in χ51=A path).
-/

/-- **R363 χ(54)=C → χ(60) ≠ C** via triple (18, 54, 60): 18 + 3·54 = 180 = 3·60. -/
theorem bAdicEquation_3_chi54_eq_chi18_forces_chi60_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18) :
    χ 60 ≠ χ 18 := by
  intro h60_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 54) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 54
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h54_eq_18.symm
  · show χ 54 = χ (54 + 6)
    rw [show (54 + 6 : ℕ) = 60 by decide]
    exact h54_eq_18.trans h60_eq_18.symm

/-- **R363 χ(57)=B → χ(60) ≠ B** via triple (9, 57, 60): 9 + 3·57 = 180 = 3·60. -/
theorem bAdicEquation_3_chi57_eq_chi9_forces_chi60_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h57_eq_9 : χ 57 = χ 9) :
    χ 60 ≠ χ 9 := by
  intro h60_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 57) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 57
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h57_eq_9.symm
  · show χ 57 = χ (57 + 3)
    rw [show (57 + 3 : ℕ) = 60 by decide]
    exact h57_eq_9.trans h60_eq_9.symm

/-- **R363 χ(60) directional exclusion pack**: A (R361 χ51=A), B (R363 χ57=B),
  C (R363 χ54=C). -/
theorem bAdicEquation_3_branchII_chi60_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 51 = χ 27 → χ 60 ≠ χ 27) ∧
    (χ 57 = χ 9  → χ 60 ≠ χ 9) ∧
    (χ 54 = χ 18 → χ 60 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h51_eq_27
    exact bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
      χ (by omega) hNoMono h51_eq_27
  · intro h57_eq_9
    exact bAdicEquation_3_chi57_eq_chi9_forces_chi60_ne_chi9
      χ (by omega) hNoMono h57_eq_9
  · intro h54_eq_18
    exact bAdicEquation_3_chi54_eq_chi18_forces_chi60_ne_chi18
      χ (by omega) hNoMono h54_eq_18

/-- **R363 Part 2 — χ(60) current-leaf B-forcing**: under χ54=C ∧ χ51=A ∧ χ60 ∈ ABC,
  χ60 = B (forced by R361 χ60≠A + R363 χ60≠C + R349 helper). -/
theorem bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18) :
    χ 60 = χ 9 := by
  have h60_ne_27 := bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
    χ (by omega) hNoMono h51_eq_27
  have h60_ne_18 := bAdicEquation_3_chi54_eq_chi18_forces_chi60_ne_chi18
    χ (by omega) hNoMono h54_eq_18
  exact branchII_ABC_refine_neA_neC_to_B h60ABC h60_ne_27 h60_ne_18

/-- **R363 χ(48)=A → χ(57) ≠ A** via triple (27, 48, 57): 27 + 3·48 = 171 = 3·57. -/
theorem bAdicEquation_3_chi48_eq_chi27_forces_chi57_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_27 : χ 48 = χ 27) :
    χ 57 ≠ χ 27 := by
  intro h57_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 48) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 48
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h48_eq_27.symm
  · show χ 48 = χ (48 + 9)
    rw [show (48 + 9 : ℕ) = 57 by decide]
    exact h48_eq_27.trans h57_eq_27.symm

/-- **R363 χ(54)=B → χ(57) ≠ B** via triple (9, 54, 57): 9 + 3·54 = 171 = 3·57. -/
theorem bAdicEquation_3_chi54_eq_chi9_forces_chi57_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_9 : χ 54 = χ 9) :
    χ 57 ≠ χ 9 := by
  intro h57_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 54) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 54
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h54_eq_9.symm
  · show χ 54 = χ (54 + 3)
    rw [show (54 + 3 : ℕ) = 57 by decide]
    exact h54_eq_9.trans h57_eq_9.symm

/-- **R363 χ(57) directional exclusion pack**: A (R363 χ48=A), B (R363 χ54=B),
  C (R360 χ51=C). -/
theorem bAdicEquation_3_branchII_chi57_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 48 = χ 27 → χ 57 ≠ χ 27) ∧
    (χ 54 = χ 9  → χ 57 ≠ χ 9) ∧
    (χ 51 = χ 18 → χ 57 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h48_eq_27
    exact bAdicEquation_3_chi48_eq_chi27_forces_chi57_ne_chi27
      χ (by omega) hNoMono h48_eq_27
  · intro h54_eq_9
    exact bAdicEquation_3_chi54_eq_chi9_forces_chi57_ne_chi9
      χ (by omega) hNoMono h54_eq_9
  · intro h51_eq_18
    exact bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
      χ (by omega) hNoMono h51_eq_18

/-- **R363 Part 4 — χ(57) refinement under χ(51)=C**: combine R360 χ57≠C
  with χ57 ∈ ABC to narrow to χ57 ∈ {A, B}. -/
theorem bAdicEquation_3_branchII_case_51C_chi57ABC_refines_to_AB
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h51_eq_18 : χ 51 = χ 18)
    (h57ABC : χ 57 = χ 27 ∨ χ 57 = χ 9 ∨ χ 57 = χ 18) :
    χ 57 = χ 27 ∨ χ 57 = χ 9 := by
  have h57_ne_18 := bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
    χ (by omega) hNoMono h51_eq_18
  exact branchII_ABC_refine_neC_to_AB h57ABC h57_ne_18

/-! ### §204. R364 — χ(60)=B downstream cascade + χ(63) directional infrastructure.

  R363 produced conditional `χ54=C ∧ χ51=A ∧ χ60ABC → χ60=B`. R364 builds
  the downstream consequences of χ60=B, in particular the layer exclusion
  χ63 ≠ B, and the complete χ63 directional pack (A/B/C).

  Deliverables:
  - **Part 1** chi60_eq_chi9_forces_chi63_ne_chi9 via (9, 60, 63).
  - **Part 2** chi60_eq_chi9_forces_chi29_ne_chi9 via (60, 9, 29).
  - **Part 3** chi60B_downstream_pack: And of χ63 ≠ B and χ29 ≠ B.
  - **Part 4** case_54C_51A_chi60ABC_forces_chi60B_and_downstream:
    full conditional cascade.
  - **Part 5** χ63 directional pack: A via (27, 54, 63), B via (9, 60, 63),
    C via (18, 57, 63).

  **Conditional value**: under χ54=C ∧ χ51=A ∧ χ60ABC, χ60=B is forced
  (R363), then χ63 ≠ B and χ29 ≠ B follow. χ63 = 3·21 (layer) is the
  main hLayer value.

  **Audit**: no unconditional closure. χ60ABC source still absent.
  R365 should audit χ60ABC direct sources.
-/

/-- **R364 Part 1 — χ(60)=B → χ(63) ≠ B** via triple (9, 60, 63):
  9 + 3·60 = 189 = 3·63. χ63 = 3·21 is layer. -/
theorem bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_9 : χ 60 = χ 9) :
    χ 63 ≠ χ 9 := by
  intro h63_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 60) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 60
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h60_eq_9.symm
  · show χ 60 = χ (60 + 3)
    rw [show (60 + 3 : ℕ) = 63 by decide]
    exact h60_eq_9.trans h63_eq_9.symm

/-- **R364 Part 2 — χ(60)=B → χ(29) ≠ B** via triple (60, 9, 29):
  60 + 3·9 = 87 = 3·29. χ29 non-layer; useful for R337 χ33=C
  branch context where χ29 ≠ C already appears. -/
theorem bAdicEquation_3_chi60_eq_chi9_forces_chi29_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_9 : χ 60 = χ 9) :
    χ 29 ≠ χ 9 := by
  intro h29_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 20) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 20) = χ 9
    rw [show (3 * 20 : ℕ) = 60 by decide]
    exact h60_eq_9
  · show χ 9 = χ (9 + 20)
    rw [show (9 + 20 : ℕ) = 29 by decide]
    exact h29_eq_9.symm

/-- **R364 Part 3 — χ(60)=B downstream pack**: And of χ63 ≠ B and χ29 ≠ B. -/
theorem bAdicEquation_3_branchII_chi60B_downstream_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_9 : χ 60 = χ 9) :
    χ 63 ≠ χ 9 ∧ χ 29 ≠ χ 9 := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
      χ (by omega) hNoMono h60_eq_9
  · exact bAdicEquation_3_chi60_eq_chi9_forces_chi29_ne_chi9
      χ (by omega) hNoMono h60_eq_9

/-- **R364 Part 4 — Full conditional cascade**: under χ54=C ∧ χ51=A ∧ χ60ABC,
  χ60 = B AND χ63 ≠ B AND χ29 ≠ B. -/
theorem bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_chi60B_and_downstream
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18) :
    χ 60 = χ 9 ∧ χ 63 ≠ χ 9 ∧ χ 29 ≠ χ 9 := by
  have h60_eq_9 := bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
    χ h81 hNoMono h54_eq_18 h51_eq_27 h60ABC
  refine ⟨h60_eq_9, ?_, ?_⟩
  · exact bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
      χ (by omega) hNoMono h60_eq_9
  · exact bAdicEquation_3_chi60_eq_chi9_forces_chi29_ne_chi9
      χ (by omega) hNoMono h60_eq_9

/-- **R364 Part 5-A — χ(54)=A → χ(63) ≠ A** via triple (27, 54, 63):
  27 + 3·54 = 189 = 3·63. -/
theorem bAdicEquation_3_chi54_eq_chi27_forces_chi63_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_27 : χ 54 = χ 27) :
    χ 63 ≠ χ 27 := by
  intro h63_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 54) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 54
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h54_eq_27.symm
  · show χ 54 = χ (54 + 9)
    rw [show (54 + 9 : ℕ) = 63 by decide]
    exact h54_eq_27.trans h63_eq_27.symm

/-- **R364 Part 5-C — χ(57)=C → χ(63) ≠ C** via triple (18, 57, 63):
  18 + 3·57 = 189 = 3·63. -/
theorem bAdicEquation_3_chi57_eq_chi18_forces_chi63_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h57_eq_18 : χ 57 = χ 18) :
    χ 63 ≠ χ 18 := by
  intro h63_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 57) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 57
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h57_eq_18.symm
  · show χ 57 = χ (57 + 6)
    rw [show (57 + 6 : ℕ) = 63 by decide]
    exact h57_eq_18.trans h63_eq_18.symm

/-- **R364 Part 5 — χ(63) directional exclusion pack**: A via (27, 54, 63),
  B via (9, 60, 63), C via (18, 57, 63). -/
theorem bAdicEquation_3_branchII_chi63_directional_exclusion_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 54 = χ 27 → χ 63 ≠ χ 27) ∧
    (χ 60 = χ 9  → χ 63 ≠ χ 9) ∧
    (χ 57 = χ 18 → χ 63 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h54_eq_27
    exact bAdicEquation_3_chi54_eq_chi27_forces_chi63_ne_chi27
      χ (by omega) hNoMono h54_eq_27
  · intro h60_eq_9
    exact bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
      χ (by omega) hNoMono h60_eq_9
  · intro h57_eq_18
    exact bAdicEquation_3_chi57_eq_chi18_forces_chi63_ne_chi18
      χ (by omega) hNoMono h57_eq_18

/-! ### §205. R365 — χ(63) alternative triggers + fourth-color dispatcher + dichotomy.

  Goal: turn χ(63) into a structural dispatcher.

  Three new isolated trigger lemmas:
  - **Part 1-A** `chi36_eq_chi27_forces_chi63_ne_chi27` via (81, 36, 63):
    81 + 3·36 = 189 = 3·63. Uses h27_eq_81 to bridge χ81 ↔ χ27.
  - **Part 1-B** `chi54_eq_chi18_chi45_eq_chi18_forces_chi63_ne_chi18` via (54, 45, 63):
    54 + 3·45 = 189 = 3·63. Joint χ54=C ∧ χ45=C trigger.
  - **Part 4-A** `chi42_ne_chi63_in_monoFree` via self-loop (63, 42, 63):
    63 + 3·42 = 189 = 3·63. Universal.

  Trigger pack:
  - **Part 2** `case_54C_chi63_trigger_pack`: four triggers
    χ36=A → χ63≠A, χ60=B → χ63≠B, χ45=C → χ63≠C, χ57=C → χ63≠C.

  Fourth-color dispatcher:
  - **Part 4-B** `chi63_fourth_forces_chi42ABC`: under IsKColoring n 4 χ +
    Branch II anchors + χ63 ≠ all 3 anchors, then χ42 ∈ {A, B, C}.

  Current-leaf χ(63) dichotomy:
  - **Part 5** `case_54C_51A_chi60ABC_chi63_dichotomy`: under
    χ54=C ∧ χ51=A ∧ χ60ABC, conclude
    χ63 = A ∨ χ63 = C ∨ χ42ABC.

  Removes the χ63ABC three-way split and replaces it with a 3-branch
  dispatcher (χ63=A, χ63=C, fourth-color → χ42ABC). -/

/-- **R365 Part 1-A — χ(36)=A → χ(63) ≠ A** via triple (81, 36, 63):
  81 + 3·36 = 189 = 3·63. Uses h27_eq_81 to translate χ81 ↔ χ27. -/
theorem bAdicEquation_3_chi36_eq_chi27_forces_chi63_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h36_eq_27 : χ 36 = χ 27) :
    χ 63 ≠ χ 27 := by
  intro h63_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 27) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 27) = χ 36
    rw [show (3 * 27 : ℕ) = 81 by decide]
    exact h27_eq_81.symm.trans h36_eq_27.symm
  · show χ 36 = χ (36 + 27)
    rw [show (36 + 27 : ℕ) = 63 by decide]
    exact h36_eq_27.trans h63_eq_27.symm

/-- **R365 Part 1-B — χ(54)=C ∧ χ(45)=C → χ(63) ≠ C** via triple (54, 45, 63):
  54 + 3·45 = 189 = 3·63. -/
theorem bAdicEquation_3_chi54_eq_chi18_chi45_eq_chi18_forces_chi63_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h54_eq_18 : χ 54 = χ 18)
    (h45_eq_18 : χ 45 = χ 18) :
    χ 63 ≠ χ 18 := by
  intro h63_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 18) (y := 45) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 18) = χ 45
    rw [show (3 * 18 : ℕ) = 54 by decide]
    exact h54_eq_18.trans h45_eq_18.symm
  · show χ 45 = χ (45 + 18)
    rw [show (45 + 18 : ℕ) = 63 by decide]
    exact h45_eq_18.trans h63_eq_18.symm

/-- **R365 Part 2 — χ(63) trigger pack under χ(54)=C**:
  bundles four trigger implications for χ(63) ≠ A/B/C.
  Triggers: χ36=A via (81,36,63); χ60=B via (9,60,63); χ45=C via (54,45,63);
  χ57=C via (18,57,63). -/
theorem bAdicEquation_3_branchII_case_54C_chi63_trigger_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h54_eq_18 : χ 54 = χ 18) :
    (χ 36 = χ 27 → χ 63 ≠ χ 27) ∧
    (χ 60 = χ 9  → χ 63 ≠ χ 9) ∧
    (χ 45 = χ 18 → χ 63 ≠ χ 18) ∧
    (χ 57 = χ 18 → χ 63 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h36_eq_27
    exact bAdicEquation_3_chi36_eq_chi27_forces_chi63_ne_chi27
      χ h81 hNoMono h27_eq_81 h36_eq_27
  · intro h60_eq_9
    exact bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
      χ (by omega) hNoMono h60_eq_9
  · intro h45_eq_18
    exact bAdicEquation_3_chi54_eq_chi18_chi45_eq_chi18_forces_chi63_ne_chi18
      χ (by omega) hNoMono h54_eq_18 h45_eq_18
  · intro h57_eq_18
    exact bAdicEquation_3_chi57_eq_chi18_forces_chi63_ne_chi18
      χ (by omega) hNoMono h57_eq_18

/-- **R365 Part 4-A — χ(42) ≠ χ(63)** universal self-loop via triple (63, 42, 63):
  63 + 3·42 = 189 = 3·63. xz self-loop at d=21. -/
theorem bAdicEquation_3_chi42_ne_chi63_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 42 ≠ χ 63 := by
  intro h42_eq_63
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 21) (y := 42) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 21) = χ 42
    rw [show (3 * 21 : ℕ) = 63 by decide]
    exact h42_eq_63.symm
  · show χ 42 = χ (42 + 21)
    rw [show (42 + 21 : ℕ) = 63 by decide]
    exact h42_eq_63

/-- **R365 Part 4-B — χ(63) fourth-color dispatcher → χ(42)ABC**.

  Under IsKColoring n 4 χ + Branch II anchors h27_eq_81, h9_ne_27, h18_ne_9
  and χ(63) ≠ all three anchors A := χ27, B := χ9, C := χ18, the 4-coloring
  saturates {χ27, χ9, χ18, χ63} = {0,1,2,3}. Combined with χ42 < 4 and the
  self-loop χ42 ≠ χ63 (R365 Part 4-A), force χ42 ∈ {χ27, χ9, χ18}.

  Mechanism (same as R320): collect IsKColoring `< 4` bounds + pairwise
  distinctness, then close by omega on integer enumeration. -/
theorem bAdicEquation_3_branchII_chi63_fourth_forces_chi42ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h63_ne_27 : χ 63 ≠ χ 27)
    (h63_ne_9  : χ 63 ≠ χ 9)
    (h63_ne_18 : χ 63 ≠ χ 18) :
    χ 42 = χ 27 ∨ χ 42 = χ 9 ∨ χ 42 = χ 18 := by
  have h18_ne_27 : χ 18 ≠ χ 27 :=
    bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  have h42_ne_63 : χ 42 ≠ χ 63 :=
    bAdicEquation_3_chi42_ne_chi63_in_monoFree χ (by omega) hNoMono
  have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
  have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
  have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
  have h42_lt : χ 42 < 4 := hχk 42 (by omega) (by omega)
  have h63_lt : χ 63 < 4 := hχk 63 (by omega) (by omega)
  omega

/-- **R365 Part 5 — χ(63) dichotomy under current leaf (χ54=C ∧ χ51=A ∧ χ60ABC)**.

  Combining R363 `case_54C_51A_chi60ABC_forces_B` (χ60=B), R364
  `chi60B_downstream_pack` (χ63≠B), and the fourth-color dispatcher
  Part 4-B, reduces the χ63ABC three-way split to a 3-branch dispatcher:

    χ63 = A   (χ63 = χ27)
    ∨ χ63 = C (χ63 = χ18)
    ∨ χ42ABC  (χ42 ∈ {A, B, C}).

  Each branch is structurally different from "more χ63 exclusions":
  - First two pin χ63 down to a specific anchor color.
  - Third re-injects an ABC disjunction at the non-layer position χ42,
    where R337-onwards transfer machinery becomes available.

  Decidable case split on χ63 = χ27 and χ63 = χ18 (both ℕ-decidable).
  Fourth case (χ63 ≠ A, B, C) feeds into Part 4-B. -/
theorem bAdicEquation_3_branchII_case_54C_51A_chi60ABC_chi63_dichotomy
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18) :
    (χ 63 = χ 27) ∨ (χ 63 = χ 18) ∨
    (χ 42 = χ 27 ∨ χ 42 = χ 9 ∨ χ 42 = χ 18) := by
  -- Force χ60 = χ9 (= B) from R363 cascade.
  have h60_eq_9 := bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
    χ h81 hNoMono h54_eq_18 h51_eq_27 h60ABC
  -- R364 part 1 ⟹ χ63 ≠ χ9 (= B).
  have h63_ne_9 := bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
    χ (by omega) hNoMono h60_eq_9
  by_cases h63_eq_27 : χ 63 = χ 27
  · exact Or.inl h63_eq_27
  · by_cases h63_eq_18 : χ 63 = χ 18
    · exact Or.inr (Or.inl h63_eq_18)
    · -- Fourth-color case: χ63 ≠ A, B, C.
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi63_fourth_forces_chi42ABC
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
          h63_eq_27 h63_ne_9 h63_eq_18))

/-! ### §206. R366 — Consume χ(63) dichotomy: branch outputs + χ(42)ABC expansion.

  R365 reduced the active disjunction to:
    χ63 = A  ∨  χ63 = C  ∨  χ42ABC
  R366 develops downstream outputs for all three branches.

  - **Part A-1** `chi63_eq_chi27_forces_chi48_ne_chi27` via (63, 27, 48):
    63 + 3·27 = 144 = 3·48.  Globally valid; redundant in current leaf
    (h48_eq_9 already implies χ48 = B ≠ A), but standalone infra.
  - **Part A-2** `chi63_eq_chi18_forces_chi39_ne_chi18` via (63, 18, 39):
    63 + 3·18 = 117 = 3·39.  Activates a new χ39 ≠ C exclusion in the
    χ63=C branch.
  - **Part B-1** `chi42_eq_chi18_forces_chi48_ne_chi18` via (18, 42, 48):
    18 + 3·42 = 144 = 3·48.  Completes χ42=C direction (R337 only had A/B).
    Redundant in current leaf (χ48=B ≠ C), but standalone infra.
  - **Part B-2** `chi42_full_ABC_expansion`: bundles the three χ42=A/B/C
    directional outputs (χ41/χ23/χ48 exclusions).

  Audit: no branch closes the current leaf. All three branches are
  future-leverage in scope. Decision on continuation deferred to R367. -/

/-- **R366 Part A-1 — χ(63)=A → χ(48) ≠ A** via triple (63, 27, 48):
  63 + 3·27 = 144 = 3·48. -/
theorem bAdicEquation_3_chi63_eq_chi27_forces_chi48_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h63_eq_27 : χ 63 = χ 27) :
    χ 48 ≠ χ 27 := by
  intro h48_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 21) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 21) = χ 27
    rw [show (3 * 21 : ℕ) = 63 by decide]
    exact h63_eq_27
  · show χ 27 = χ (27 + 21)
    rw [show (27 + 21 : ℕ) = 48 by decide]
    exact h48_eq_27.symm

/-- **R366 Part A-2 — χ(63)=C → χ(39) ≠ C** via triple (63, 18, 39):
  63 + 3·18 = 117 = 3·39. -/
theorem bAdicEquation_3_chi63_eq_chi18_forces_chi39_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h63 : 63 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h63_eq_18 : χ 63 = χ 18) :
    χ 39 ≠ χ 18 := by
  intro h39_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 21) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 21) = χ 18
    rw [show (3 * 21 : ℕ) = 63 by decide]
    exact h63_eq_18
  · show χ 18 = χ (18 + 21)
    rw [show (18 + 21 : ℕ) = 39 by decide]
    exact h39_eq_18.symm

/-- **R366 Part B-1 — χ(42)=C → χ(48) ≠ C** via triple (18, 42, 48):
  18 + 3·42 = 144 = 3·48.  Completes χ42 C-direction. -/
theorem bAdicEquation_3_chi42_eq_chi18_forces_chi48_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_18 : χ 42 = χ 18) :
    χ 48 ≠ χ 18 := by
  intro h48_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 42) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 42
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h42_eq_18.symm
  · show χ 42 = χ (42 + 6)
    rw [show (42 + 6 : ℕ) = 48 by decide]
    exact h42_eq_18.trans h48_eq_18.symm

/-- **R366 Part B-2 — χ(42) full ABC directional expansion**:
  bundles R337 F-1/F-2 (χ42=A→χ41≠A, χ42=B→χ23≠B) with new
  R366 Part B-1 (χ42=C→χ48≠C). -/
theorem bAdicEquation_3_branchII_chi42_full_ABC_expansion
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 42 = χ 27 → χ 41 ≠ χ 27) ∧
    (χ 42 = χ 9  → χ 23 ≠ χ 9) ∧
    (χ 42 = χ 18 → χ 48 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h42_eq_27
    exact bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
      χ (by omega) hNoMono h42_eq_27
  · intro h42_eq_9
    exact bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
      χ (by omega) hNoMono h42_eq_9
  · intro h42_eq_18
    exact bAdicEquation_3_chi42_eq_chi18_forces_chi48_ne_chi18
      χ (by omega) hNoMono h42_eq_18

/-! ### §207. R367 — χ(60)/χ(63) line stopping round + final local summary.

  Stop decision: per the round-protocol stop conditions, the χ(60)/χ(63)
  line is no longer productive in the current leaf:

  - Stop condition (3) triggered: R366 produced only future-leverage
    exclusions without branch closure (χ39≠C, χ48≠A, χ48≠C are
    all globally valid but do not close the current leaf, which already
    has χ48 pinned to B).
  - Stop condition (5) NOT triggered: R365 Part 4-B did produce a new
    ABC conclusion (χ42ABC) from the fourth-color case, so the round
    was structurally productive.

  Conclusion: STOP the χ(60)/χ(63) line as a closure attempt. Continue
  using R365/R366 infrastructure when the χ54=C ∧ χ51=A subcase arises,
  but no further rounds invested in deepening χ(60)/χ(63) cascades.

  **R367 deliverable** — `full_chi63_42_summary`: a single packaging
  theorem that combines R363 + R364 + R365 + R366 into one statement.
  Given the current-leaf hypotheses, conclude
    χ60 = B ∧ χ63 ≠ B ∧
    (χ63=A ∧ χ48≠A  ∨  χ63=C ∧ χ39≠C  ∨
     (χ42=A ∧ χ41≠A  ∨  χ42=B ∧ χ23≠B  ∨  χ42=C ∧ χ48≠C))

  This summary is the canonical entry point for any future consumer
  that needs to act inside the χ54=C ∧ χ51=A region.

  **Recommended pivot for R368**: return to the parallel R362 frontier
  branch  `χ51=C → χ35≠C ∧ χ57≠C`.  This is the symmetric layer-output
  branch still underexplored.  The χ51=A line is now packaged. -/

/-- **R367 final local summary — χ(54)=C ∧ χ(51)=A ∧ χ(60)ABC closure summary**.

  Packages R363 (χ60=B), R364 (χ63≠B), R365 Part 5 (χ63 dichotomy),
  R366 Parts A/B (per-branch outputs) into a single statement.

  No new arithmetic; pure composition of earlier theorems. -/
theorem bAdicEquation_3_branchII_case_54C_51A_chi60ABC_full_chi63_42_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18) :
    χ 60 = χ 9 ∧ χ 63 ≠ χ 9 ∧
    ((χ 63 = χ 27 ∧ χ 48 ≠ χ 27) ∨
     (χ 63 = χ 18 ∧ χ 39 ≠ χ 18) ∨
     ((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
      (χ 42 = χ 9  ∧ χ 23 ≠ χ 9) ∨
      (χ 42 = χ 18 ∧ χ 48 ≠ χ 18))) := by
  have h60_eq_9 := bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
    χ h81 hNoMono h54_eq_18 h51_eq_27 h60ABC
  have h63_ne_9 := bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
    χ (by omega) hNoMono h60_eq_9
  have hDichotomy := bAdicEquation_3_branchII_case_54C_51A_chi60ABC_chi63_dichotomy
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h51_eq_27 h60ABC
  refine ⟨h60_eq_9, h63_ne_9, ?_⟩
  rcases hDichotomy with h63_eq_27 | h63_eq_18 | h42ABC
  · exact Or.inl ⟨h63_eq_27,
      bAdicEquation_3_chi63_eq_chi27_forces_chi48_ne_chi27
        χ (by omega) hNoMono h63_eq_27⟩
  · exact Or.inr (Or.inl ⟨h63_eq_18,
      bAdicEquation_3_chi63_eq_chi18_forces_chi39_ne_chi18
        χ (by omega) hNoMono h63_eq_18⟩)
  · refine Or.inr (Or.inr ?_)
    rcases h42ABC with h42_eq_27 | h42_eq_9 | h42_eq_18
    · exact Or.inl ⟨h42_eq_27,
        bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
          χ (by omega) hNoMono h42_eq_27⟩
    · exact Or.inr (Or.inl ⟨h42_eq_9,
        bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
          χ (by omega) hNoMono h42_eq_9⟩)
    · exact Or.inr (Or.inr ⟨h42_eq_18,
        bAdicEquation_3_chi42_eq_chi18_forces_chi48_ne_chi18
          χ (by omega) hNoMono h42_eq_18⟩)

/-! ### §208. R368 — χ(51)=C / χ(57) line: activation audit + extended trigger pack.

  Pivot from the stopped χ(60)/χ(63) line (R367) to the parallel χ(51)=C
  branch. R361 gave the layer-output `χ51=C → χ57≠C`. Goal: audit whether
  a second exclusion (χ57≠A or χ57≠B) is derivable in the current leaf
  (χ54=C ∧ χ72=B ∧ χ48=B) extended by χ51=C.

  **Audit conclusions** (proved + documented):
  - **A-exclusion**: only one extra trigger via `(81, 30, 57)` (uses h27_eq_81
    to translate χ81 ↔ χ27). Requires χ30=A, which is not active in current
    leaf (χ30 has no prior classification).
  - **B-exclusion**: no triple with z=57 produces a B-exclusion from
    χ48=B or χ72=B inputs. χ48=B → χ27=B reduces to a no-mono check that
    is vacuous since χ27=A. χ72=B requires y=-15 (invalid).

  **New theorem** (Part 1):
  - `chi30_eq_chi27_forces_chi57_ne_chi27` via (81, 30, 57): 81 + 3·30 = 171 = 3·57.

  **Pack** (Part 3):
  - `chi57_extended_trigger_pack`: combines R363 A/B/C triggers with new
    R368 χ30=A trigger.

  **Audit result** (Part 5): no second active χ57 exclusion in current leaf.
  R369 should attempt fourth-color dispatcher / weak dichotomy. -/

/-- **R368 Part 1 — χ(30)=A → χ(57) ≠ A** via triple (81, 30, 57):
  81 + 3·30 = 171 = 3·57. Uses h27_eq_81 to translate χ81 ↔ χ27. -/
theorem bAdicEquation_3_chi30_eq_chi27_forces_chi57_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h30_eq_27 : χ 30 = χ 27) :
    χ 57 ≠ χ 27 := by
  intro h57_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 27) (y := 30) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 27) = χ 30
    rw [show (3 * 27 : ℕ) = 81 by decide]
    exact h27_eq_81.symm.trans h30_eq_27.symm
  · show χ 30 = χ (30 + 27)
    rw [show (30 + 27 : ℕ) = 57 by decide]
    exact h30_eq_27.trans h57_eq_27.symm

/-- **R368 Part 3 — χ(57) extended trigger pack**: combines R363 triggers
  (χ48=A, χ54=B, χ51=C) with new R368 χ30=A trigger. Four trigger
  implications for χ(57) ≠ A/B/C. -/
theorem bAdicEquation_3_branchII_chi57_extended_trigger_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81) :
    (χ 48 = χ 27 → χ 57 ≠ χ 27) ∧
    (χ 30 = χ 27 → χ 57 ≠ χ 27) ∧
    (χ 54 = χ 9  → χ 57 ≠ χ 9) ∧
    (χ 51 = χ 18 → χ 57 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h48_eq_27
    exact bAdicEquation_3_chi48_eq_chi27_forces_chi57_ne_chi27
      χ (by omega) hNoMono h48_eq_27
  · intro h30_eq_27
    exact bAdicEquation_3_chi30_eq_chi27_forces_chi57_ne_chi27
      χ h81 hNoMono h27_eq_81 h30_eq_27
  · intro h54_eq_9
    exact bAdicEquation_3_chi54_eq_chi9_forces_chi57_ne_chi9
      χ (by omega) hNoMono h54_eq_9
  · intro h51_eq_18
    exact bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
      χ (by omega) hNoMono h51_eq_18

/-! ### §209. R369 — χ(57) fourth-color dispatcher + χ(51)=C weak dichotomy.

  Under χ51=C, only χ57≠C is currently forced. To turn χ(57) into a
  structural dispatcher, mirror R365's χ(63) construction:

  - **Part A** `chi38_ne_chi57_in_monoFree` via self-loop (57, 38, 57):
    57 + 3·38 = 171 = 3·57. xz self-loop at d=19. Universal.
  - **Part B** `chi57_fourth_forces_chi38ABC`: IsKColoring 4 + Branch II
    anchors + χ57 ≠ all three anchors ⟹ χ38 ∈ {A, B, C}.
  - **Part C** `case_51C_chi57_dichotomy`: under χ51=C,
      χ57 = A  ∨  χ57 = B  ∨  χ38ABC.

  The dichotomy is **weak** in the sense that only one χ57 exclusion is
  forced (χ57≠C). The "A" and "B" branches remain open disjuncts rather
  than narrow pins. Still structurally productive: the fourth-color
  case injects ABC at non-layer position χ38, where R350 χ36∧χ38 cross
  refinements can engage. -/

/-- **R369 Part A — χ(38) ≠ χ(57)** universal self-loop via (57, 38, 57):
  57 + 3·38 = 171 = 3·57. xz self-loop at d=19. -/
theorem bAdicEquation_3_chi38_ne_chi57_in_monoFree
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    χ 38 ≠ χ 57 := by
  intro h38_eq_57
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 19) (y := 38) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 19) = χ 38
    rw [show (3 * 19 : ℕ) = 57 by decide]
    exact h38_eq_57.symm
  · show χ 38 = χ (38 + 19)
    rw [show (38 + 19 : ℕ) = 57 by decide]
    exact h38_eq_57

/-- **R369 Part B — χ(57) fourth-color dispatcher → χ(38)ABC**.

  Under IsKColoring n 4 χ + Branch II + χ57 ≠ all three anchors,
  the 4-coloring saturates {χ27, χ9, χ18, χ57} = {0,1,2,3} so χ38<4 +
  χ38≠χ57 (Part A self-loop) ⟹ χ38 ∈ {χ27, χ9, χ18}.

  Mechanism identical to R365 Part 4-B (`chi63_fourth_forces_chi42ABC`). -/
theorem bAdicEquation_3_branchII_chi57_fourth_forces_chi38ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h57_ne_27 : χ 57 ≠ χ 27)
    (h57_ne_9  : χ 57 ≠ χ 9)
    (h57_ne_18 : χ 57 ≠ χ 18) :
    χ 38 = χ 27 ∨ χ 38 = χ 9 ∨ χ 38 = χ 18 := by
  have h18_ne_27 : χ 18 ≠ χ 27 :=
    bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  have h38_ne_57 : χ 38 ≠ χ 57 :=
    bAdicEquation_3_chi38_ne_chi57_in_monoFree χ (by omega) hNoMono
  have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
  have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
  have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
  have h38_lt : χ 38 < 4 := hχk 38 (by omega) (by omega)
  have h57_lt : χ 57 < 4 := hχk 57 (by omega) (by omega)
  -- h27_eq_81 unused locally; retained in signature to match R365 Part 4-B
  -- and Branch II convention. Closure by numeric enumeration on 5 distinct
  -- values in {0,1,2,3}: contradiction unless χ38 ∈ {χ27, χ9, χ18}.
  omega

/-- **R369 Part C — χ(57) weak dichotomy under χ(51)=C**.

  Under Branch II + χ(51)=C, R361 gives χ57≠C. Combined with the
  fourth-color dispatcher (Part B), conclude

    χ57 = A  ∨  χ57 = B  ∨  χ38ABC.

  This is "weak" because the A/B branches remain disjunctive (not pinned
  to a specific value). Decidable case split on χ57=χ27 / χ57=χ9. -/
theorem bAdicEquation_3_branchII_case_51C_chi57_dichotomy
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h51_eq_18 : χ 51 = χ 18) :
    (χ 57 = χ 27) ∨ (χ 57 = χ 9) ∨
    (χ 38 = χ 27 ∨ χ 38 = χ 9 ∨ χ 38 = χ 18) := by
  have h57_ne_18 := bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
    χ (by omega) hNoMono h51_eq_18
  by_cases h57_eq_27 : χ 57 = χ 27
  · exact Or.inl h57_eq_27
  · by_cases h57_eq_9 : χ 57 = χ 9
    · exact Or.inr (Or.inl h57_eq_9)
    · -- fourth-color case: χ57 ≠ A, B, C
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi57_fourth_forces_chi38ABC
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
          h57_eq_27 h57_eq_9 h57_ne_18))

/-! ### §210. R370 — Consume or stop χ(57) line.

  R369 produced the weak dichotomy
    χ57 = A  ∨  χ57 = B  ∨  χ38ABC.

  R370 develops downstream outputs and decides on continuation:

  - **Part A** `chi57_eq_chi27_forces_chi46_ne_chi27` via (57, 27, 46):
    57 + 3·27 = 138 = 3·46. New χ46 ≠ A exclusion (future leverage).
  - **Part B** `chi57_eq_chi9_forces_chi28_ne_chi9` via (57, 9, 28):
    57 + 3·9 = 84 = 3·28. New χ28 ≠ B exclusion (future leverage).
  - **Part C** `case_51C_chi57_dichotomy_outputs`: full consumption
    packaging — each branch carries its downstream exclusion.

  **Stop decision** (R370 final):
  All three branch outputs are future-leverage rather than closures:
  - χ46 has no prior classification → χ46≠A is a new constraint, not
    a contradiction inducer.
  - χ28 has no prior classification → χ28≠B is a new constraint, not
    a contradiction inducer.
  - χ38ABC injects ABC at a transfer position; only consumable via
    R350 χ36∧χ38 cross refinements if χ36 becomes pinned, which the
    current leaf does not force.

  Stop conditions (3) and (5) trigger:
  - (3): R370 outputs only future-leverage exclusions, no closure.
  - (5): The χ38ABC ABC conclusion has no existing active consumer in
    the current leaf (R350 χ36 cross-refinement is not active because
    χ36 is not pinned).

  Conclusion: STOP the χ57 line. Pivot recommendation in R371. -/

/-- **R370 Part A — χ(57)=A → χ(46) ≠ A** via triple (57, 27, 46):
  57 + 3·27 = 138 = 3·46. -/
theorem bAdicEquation_3_chi57_eq_chi27_forces_chi46_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h57_eq_27 : χ 57 = χ 27) :
    χ 46 ≠ χ 27 := by
  intro h46_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 19) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 19) = χ 27
    rw [show (3 * 19 : ℕ) = 57 by decide]
    exact h57_eq_27
  · show χ 27 = χ (27 + 19)
    rw [show (27 + 19 : ℕ) = 46 by decide]
    exact h46_eq_27.symm

/-- **R370 Part B — χ(57)=B → χ(28) ≠ B** via triple (57, 9, 28):
  57 + 3·9 = 84 = 3·28. -/
theorem bAdicEquation_3_chi57_eq_chi9_forces_chi28_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h57 : 57 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h57_eq_9 : χ 57 = χ 9) :
    χ 28 ≠ χ 9 := by
  intro h28_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 19) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 19) = χ 9
    rw [show (3 * 19 : ℕ) = 57 by decide]
    exact h57_eq_9
  · show χ 9 = χ (9 + 19)
    rw [show (9 + 19 : ℕ) = 28 by decide]
    exact h28_eq_9.symm

/-- **R370 Part C — χ(57) dichotomy full consumption packaging**.

  Composes R369 weak dichotomy with R370 Part A/B downstream exclusions.
  Under Branch II + χ51=C:
    (χ57=A ∧ χ46≠A) ∨ (χ57=B ∧ χ28≠B) ∨ χ38ABC.

  This is the canonical entry point for χ(51)=C / χ(57) region. -/
theorem bAdicEquation_3_branchII_case_51C_chi57_dichotomy_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h51_eq_18 : χ 51 = χ 18) :
    (χ 57 = χ 27 ∧ χ 46 ≠ χ 27) ∨
    (χ 57 = χ 9 ∧ χ 28 ≠ χ 9) ∨
    (χ 38 = χ 27 ∨ χ 38 = χ 9 ∨ χ 38 = χ 18) := by
  have hDichotomy := bAdicEquation_3_branchII_case_51C_chi57_dichotomy
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h51_eq_18
  rcases hDichotomy with h57_eq_27 | h57_eq_9 | h38ABC
  · exact Or.inl ⟨h57_eq_27,
      bAdicEquation_3_chi57_eq_chi27_forces_chi46_ne_chi27
        χ (by omega) hNoMono h57_eq_27⟩
  · exact Or.inr (Or.inl ⟨h57_eq_9,
      bAdicEquation_3_chi57_eq_chi9_forces_chi28_ne_chi9
        χ (by omega) hNoMono h57_eq_9⟩)
  · exact Or.inr (Or.inr h38ABC)

/-! ### §211. R371 — χ(51) classification audit + joint current-leaf summary.

  Pivot upward from stopped layer-output lines (R367, R370). Audit whether
  χ(51) can serve as a top-level case-split variable in the current leaf
  (χ54=C ∧ χ72=B ∧ χ48=B).

  **Discovery**: R329 already gives `χ48=B → χ51≠B`. So in the current
  leaf χ51 ≠ B; χ51 ∈ {A, C, fourth}. Combined with the R331 self-loop
  `χ34 ≠ χ51`, this yields a clean χ51 dichotomy:

    χ51 = A  ∨  χ51 = C  ∨  χ34ABC.

  This is the **direct top-level joint split** that aligns with the
  R362 frontier projections.

  **R331 already proved this** as `chi48_eq9_chi51_or_chi34_in_AC_or_ABC`
  in nested form `((χ51=A ∨ χ51=C) ∨ χ34ABC)`. R371 produces:
  - **Part 2-B** `chi51_fourth_forces_chi34ABC`: standalone fourth-color
    dispatcher (parity with R365 Part 4-B, R369 Part B).
  - **Part 3** `case_48B_chi51_dichotomy`: flat 3-branch form.
  - **Part 4** `case_54C_72B_48B_chi51_joint_summary`: integrates R361
    χ51=A/C double exclusions + R359 χ34=A/C exclusions + R360 χ34=B
    double exclusion into the canonical leaf summary.

  R371 is a strong **integration** round, not a new-arithmetic round. -/

/-- **R371 Part 2-B — χ(51) fourth-color dispatcher → χ(34)ABC**.

  Mirror of R365 Part 4-B / R369 Part B. Under IsKColoring n 4 χ +
  Branch II + χ51 ≠ all three anchors,
    χ34 ∈ {χ27, χ9, χ18}.

  Uses R331 universal self-loop `χ34 ≠ χ51` + 4-color exhaustion. -/
theorem bAdicEquation_3_branchII_chi51_fourth_forces_chi34ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h51_ne_27 : χ 51 ≠ χ 27)
    (h51_ne_9  : χ 51 ≠ χ 9)
    (h51_ne_18 : χ 51 ≠ χ 18) :
    χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18 := by
  have h18_ne_27 : χ 18 ≠ χ 27 :=
    bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  have h34_ne_51 : χ 34 ≠ χ 51 :=
    bAdicEquation_3_chi_34_ne_chi_51_in_monoFree χ (by omega) hNoMono
  have h9_lt : χ 9 < 4 := hχk 9 (by omega) (by omega)
  have h18_lt : χ 18 < 4 := hχk 18 (by omega) (by omega)
  have h27_lt : χ 27 < 4 := hχk 27 (by omega) (by omega)
  have h34_lt : χ 34 < 4 := hχk 34 (by omega) (by omega)
  have h51_lt : χ 51 < 4 := hχk 51 (by omega) (by omega)
  -- h27_eq_81 retained for Branch II convention consistency; not used locally.
  omega

/-- **R371 Part 3 — χ(51) dichotomy under χ(48)=B (flat 3-branch form)**.

  Under Branch II + χ48=B:
    χ51 = A  ∨  χ51 = C  ∨  χ34ABC.

  Decidable case split on χ51 = A / χ51 = C; fourth-color case delegates
  to Part 2-B.  Logically equivalent to the nested form in R331
  `chi48_eq9_chi51_or_chi34_in_AC_or_ABC`. -/
theorem bAdicEquation_3_branchII_case_48B_chi51_dichotomy
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 51 = χ 27) ∨ (χ 51 = χ 18) ∨
    (χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) := by
  have h51_ne_9 :=
    bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
      χ h81 hNoMono h48_eq_9
  by_cases h51_eq_27 : χ 51 = χ 27
  · exact Or.inl h51_eq_27
  · by_cases h51_eq_18 : χ 51 = χ 18
    · exact Or.inr (Or.inl h51_eq_18)
    · -- fourth-color case
      exact Or.inr (Or.inr
        (bAdicEquation_3_branchII_chi51_fourth_forces_chi34ABC
          χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
          h51_eq_27 h51_ne_9 h51_eq_18))

/-- **R371 Part 4 — current-leaf canonical joint summary**.

  Direct top-level summary for the χ54=C ∧ χ72=B ∧ χ48=B leaf, integrating
  R361 (χ51=A/C double exclusions) + R359 (χ34=A/C exclusions) +
  R360 Part 1 (χ34=B double exclusion).  Output structure:

  (χ51=A ∧ χ44≠A ∧ χ60≠A)
    ∨ (χ51=C ∧ χ35≠C ∧ χ57≠C)
    ∨ ((χ34=A ∧ χ43≠A) ∨ (χ34=B ∧ χ37≠B ∧ χ50≠B) ∨ (χ34=C ∧ χ40≠C))

  Bypasses χ33 / χ22ABC projection labels — direct from current leaf. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_chi51_joint_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
    (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18) ∨
    ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
     (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
     (χ 34 = χ 18 ∧ χ 40 ≠ χ 18)) := by
  have hDichotomy := bAdicEquation_3_branchII_case_48B_chi51_dichotomy
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  rcases hDichotomy with h51A | h51C | h34ABC
  · -- χ51=A branch: invoke R361 double exclusion.
    refine Or.inl ⟨h51A, ?_, ?_⟩
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51A).1
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51A).2
  · -- χ51=C branch: invoke R361 double exclusion.
    refine Or.inr (Or.inl ⟨h51C, ?_, ?_⟩)
    · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
        χ h81 hNoMono h51C).1
    · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
        χ h81 hNoMono h51C).2
  · -- χ34ABC branch: invoke R359 A/C + R360 Part 1 B-double.
    refine Or.inr (Or.inr ?_)
    rcases h34ABC with h34A | h34B | h34C
    · exact Or.inl ⟨h34A,
        bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
          χ (by omega) hNoMono h34A⟩
    · refine Or.inr (Or.inl ⟨h34B, ?_, ?_⟩)
      · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
          χ h81 hNoMono h48_eq_9 h34B).1
      · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
          χ h81 hNoMono h48_eq_9 h34B).2
    · exact Or.inr (Or.inr ⟨h34C,
        bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
          χ (by omega) hNoMono h34C⟩)

/-! ### §212. R372 — Refined joint summary preserving χ(51)-fourth-color tag.

  R371 gave the flat summary
    (χ51=A ∧ ...) ∨ (χ51=C ∧ ...) ∨ χ34ABC ∧ ...

  In the χ34ABC branch the only forced fact is that χ51 was fourth-color
  (i.e. χ51≠A, χ51≠B, χ51≠C). R372 preserves this tag for downstream
  consumers that need to track χ51's status.

  **Audit conclusion**: The refined summary is metadata-only. No branch
  reduction occurs beyond R371. χ34≠χ51 self-loop is already absorbed
  inside the dichotomy proof; carrying the fourth-color tag explicitly
  does not unlock new exclusions.

  Stop conditions (2), (3), (4) all candidate to trigger; consolidated
  decision in R373. -/

/-- **R372 — refined joint summary preserving χ(51)-fourth-color tag**.

  Same outputs as R371 Part 4 but the third branch carries the explicit
  `χ51 ≠ A ∧ χ51 ≠ B ∧ χ51 ≠ C` triple, enabling downstream consumers
  to reason about χ(51)'s fourth-color status. -/
theorem bAdicEquation_3_branchII_case_54C_72B_48B_chi51_joint_summary_with_fourth_tag
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h54_eq_18 : χ 54 = χ 18)
    (_h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
    (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18) ∨
    (χ 51 ≠ χ 27 ∧ χ 51 ≠ χ 9 ∧ χ 51 ≠ χ 18 ∧
     ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
      (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
      (χ 34 = χ 18 ∧ χ 40 ≠ χ 18))) := by
  have h51_ne_9 :=
    bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
      χ h81 hNoMono h48_eq_9
  by_cases h51_eq_27 : χ 51 = χ 27
  · -- χ51=A branch (R361 double exclusion).
    refine Or.inl ⟨h51_eq_27, ?_, ?_⟩
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51_eq_27).1
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51_eq_27).2
  · by_cases h51_eq_18 : χ 51 = χ 18
    · -- χ51=C branch (R361 double exclusion).
      refine Or.inr (Or.inl ⟨h51_eq_18, ?_, ?_⟩)
      · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
          χ h81 hNoMono h51_eq_18).1
      · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
          χ h81 hNoMono h51_eq_18).2
    · -- fourth-color branch: χ51 ≠ A, B, C, and χ34ABC.
      have h34ABC := bAdicEquation_3_branchII_chi51_fourth_forces_chi34ABC
        χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
        h51_eq_27 h51_ne_9 h51_eq_18
      refine Or.inr (Or.inr ⟨h51_eq_27, h51_ne_9, h51_eq_18, ?_⟩)
      rcases h34ABC with h34A | h34B | h34C
      · exact Or.inl ⟨h34A,
          bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
            χ (by omega) hNoMono h34A⟩
      · refine Or.inr (Or.inl ⟨h34B, ?_, ?_⟩)
        · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
            χ h81 hNoMono h48_eq_9 h34B).1
        · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
            χ h81 hNoMono h48_eq_9 h34B).2
      · exact Or.inr (Or.inr ⟨h34C,
          bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
            χ (by omega) hNoMono h34C⟩)

/-! ### §213. R374 — χ(54)=B ∧ χ(72)=B ∧ χ(48)=B macro summary (symmetric sibling leaf).

  Pivot from the saturated χ54=C leaf to the symmetric χ54=B leaf. Anchors
  unchanged: A := χ27 = χ81, B := χ9, C := χ18. Leaf hypotheses now:
    h54_eq_9 : χ54 = χ9    (χ54 = B, was C in previous leaf)
    h72_eq_9 : χ72 = χ9    (same)
    h48_eq_9 : χ48 = χ9    (same)

  **Discovery**: all three macro components have existing infrastructure:
  - **Part 1** (χ54=B): R326 Target B `chi54_eq9_chi36_or_chi24_dispatch`
    gives (χ36∈{A,C}) ∨ χ24ABC. Direct reuse.
  - **Part 2** (χ72=B): R337 Target D `chi72_eq9_branch_expanded_chi33`
    gives ((χ33=A ∧ χ38≠A) ∨ (χ33=C ∧ χ29≠C)) ∨ χ22ABC. Direct reuse.
  - **Part 3** (χ48=B): R371's joint summary (Part 4) used h54/h72
    only as markers. Build clean h48=B-only χ51/χ34 summary as
    `case_48B_chi51_chi34_summary`.

  **Macro summary** (Part 4): bundles Parts 1-3 as a 3-conjunct And.
  Macro summary, not closure claim.

  **B/C asymmetry audit**:
  - χ54=B → χ36 ∈ {A, C} (R326-B); χ54=C → χ36 ∈ {A, B} (R326-C).
    The dispatcher color pair flips B↔C with leaf polarity.
  - χ54=C eliminated χ48=C via R342 (specific to C-leaf chain).
    χ54=B has NO analogous χ48 color elimination → current leaf χ48=B
    is the only fixing, all χ48-color analyses remain available.
  - R321 dispatcher and R325/R337 chains are B/C-symmetric in form. -/

/-- **R374 Part 3 — χ(48)=B χ(51)/χ(34) joint summary**.

  Clean h48=B-only version of R371 Part 4 joint summary.  R371 used
  leaf markers `_h54/_h72` only; the underlying proof needs only h48=B
  plus Branch II anchors. -/
theorem bAdicEquation_3_branchII_case_48B_chi51_chi34_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    (χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
    (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18) ∨
    ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
     (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
     (χ 34 = χ 18 ∧ χ 40 ≠ χ 18)) := by
  have hDichotomy := bAdicEquation_3_branchII_case_48B_chi51_dichotomy
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9
  rcases hDichotomy with h51A | h51C | h34ABC
  · refine Or.inl ⟨h51A, ?_, ?_⟩
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51A).1
    · exact (bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
        χ h81 hNoMono h51A).2
  · refine Or.inr (Or.inl ⟨h51C, ?_, ?_⟩)
    · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
        χ h81 hNoMono h51C).1
    · exact (bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
        χ h81 hNoMono h51C).2
  · refine Or.inr (Or.inr ?_)
    rcases h34ABC with h34A | h34B | h34C
    · exact Or.inl ⟨h34A,
        bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
          χ (by omega) hNoMono h34A⟩
    · refine Or.inr (Or.inl ⟨h34B, ?_, ?_⟩)
      · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
          χ h81 hNoMono h48_eq_9 h34B).1
      · exact (bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
          χ h81 hNoMono h48_eq_9 h34B).2
    · exact Or.inr (Or.inr ⟨h34C,
        bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
          χ (by omega) hNoMono h34C⟩)

/-- **R374 Part 4 — χ(54)=B ∧ χ(72)=B ∧ χ(48)=B macro summary**.

  3-conjunct And summary for the χ54=B symmetric sibling leaf:
  - Component A: χ54=B dispatcher (χ36∈{A,C} ∨ χ24ABC) — R326 Target B.
  - Component B: χ72=B refined dispatcher (R337 Target D).
  - Component C: χ48=B χ51/χ34 joint summary (R374 Part 3).

  Macro summary, not closure claim. -/
theorem bAdicEquation_3_branchII_case_54B_72B_48B_macro_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_9 : χ 54 = χ 9)
    (h72_eq_9 : χ 72 = χ 9)
    (h48_eq_9 : χ 48 = χ 9) :
    ((χ 36 = χ 27 ∨ χ 36 = χ 18) ∨
     (χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18)) ∧
    (((χ 33 = χ 27 ∧ χ 38 ≠ χ 27) ∨
      (χ 33 = χ 18 ∧ χ 29 ≠ χ 18)) ∨
     (χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18)) ∧
    ((χ 51 = χ 27 ∧ χ 44 ≠ χ 27 ∧ χ 60 ≠ χ 27) ∨
     (χ 51 = χ 18 ∧ χ 35 ≠ χ 18 ∧ χ 57 ≠ χ 18) ∨
     ((χ 34 = χ 27 ∧ χ 43 ≠ χ 27) ∨
      (χ 34 = χ 9 ∧ χ 37 ≠ χ 9 ∧ χ 50 ≠ χ 9) ∨
      (χ 34 = χ 18 ∧ χ 40 ≠ χ 18))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9
  · exact bAdicEquation_3_branchII_chi72_eq9_branch_expanded_chi33
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_9
  · exact bAdicEquation_3_branchII_case_48B_chi51_chi34_summary
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h48_eq_9

/-! ### §214. R375 — (24, 34, 42) cross-macro coupling chain.

  Test whether the macro components of R374 can couple. R340 same-color
  chain `(54, 33, 51)` is non-active in χ54=B leaf (χ33 ∈ {A,C} from
  R325-A, never B; χ54=B; χ51 not classified). Search for an active
  cross-chain.

  **Candidate**: (24, 34, 42) — 24 + 3·34 = 126 = 3·42. Links the two
  fourth-color fallback positions χ24 (from χ54=B macro Part 1) and χ34
  (from χ48=B macro Part 3). Same-color cases produce χ42 exclusions.

  - **Part A** `chi24_chi34_eq_chi27_forces_chi42_ne_chi27`: same A path.
  - **Part B** `chi24_chi34_eq_chi9_forces_chi42_ne_chi9`: same B path.
  - **Part C** `chi24_chi34_eq_chi18_forces_chi42_ne_chi18`: same C path.
  - **Part D** `chi24_chi34_chi42_cross_refinement`: full ABC packaging.

  **Active reduction audit**:
  χ42 has no prior classification in current leaf, so the cross-chain
  produces transfer-frontier exclusions (future leverage), not live
  branch reductions. Joint χ24ABC ∧ χ34ABC scenario is the 2D
  fourth-color path of the macro summary. -/

/-- **R375 Part A — χ(24)=A ∧ χ(34)=A → χ(42) ≠ A** via triple (24, 34, 42):
  24 + 3·34 = 126 = 3·42. -/
theorem bAdicEquation_3_chi24_eq_chi27_chi34_eq_chi27_forces_chi42_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_27 : χ 24 = χ 27)
    (h34_eq_27 : χ 34 = χ 27) :
    χ 42 ≠ χ 27 := by
  intro h42_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 34
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_27.trans h34_eq_27.symm
  · show χ 34 = χ (34 + 8)
    rw [show (34 + 8 : ℕ) = 42 by decide]
    exact h34_eq_27.trans h42_eq_27.symm

/-- **R375 Part B — χ(24)=B ∧ χ(34)=B → χ(42) ≠ B** via triple (24, 34, 42). -/
theorem bAdicEquation_3_chi24_eq_chi9_chi34_eq_chi9_forces_chi42_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_9 : χ 24 = χ 9)
    (h34_eq_9 : χ 34 = χ 9) :
    χ 42 ≠ χ 9 := by
  intro h42_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 34
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_9.trans h34_eq_9.symm
  · show χ 34 = χ (34 + 8)
    rw [show (34 + 8 : ℕ) = 42 by decide]
    exact h34_eq_9.trans h42_eq_9.symm

/-- **R375 Part C — χ(24)=C ∧ χ(34)=C → χ(42) ≠ C** via triple (24, 34, 42). -/
theorem bAdicEquation_3_chi24_eq_chi18_chi34_eq_chi18_forces_chi42_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_18 : χ 24 = χ 18)
    (h34_eq_18 : χ 34 = χ 18) :
    χ 42 ≠ χ 18 := by
  intro h42_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 34
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_18.trans h34_eq_18.symm
  · show χ 34 = χ (34 + 8)
    rw [show (34 + 8 : ℕ) = 42 by decide]
    exact h34_eq_18.trans h42_eq_18.symm

/-- **R375 Part D — χ(24)/χ(34)/χ(42) cross-refinement pack**: 3 same-color
  implications bundled. -/
theorem bAdicEquation_3_branchII_chi24_chi34_chi42_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 24 = χ 27 ∧ χ 34 = χ 27 → χ 42 ≠ χ 27) ∧
    (χ 24 = χ 9  ∧ χ 34 = χ 9  → χ 42 ≠ χ 9) ∧
    (χ 24 = χ 18 ∧ χ 34 = χ 18 → χ 42 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨h24_eq_27, h34_eq_27⟩
    exact bAdicEquation_3_chi24_eq_chi27_chi34_eq_chi27_forces_chi42_ne_chi27
      χ (by omega) hNoMono h24_eq_27 h34_eq_27
  · intro ⟨h24_eq_9, h34_eq_9⟩
    exact bAdicEquation_3_chi24_eq_chi9_chi34_eq_chi9_forces_chi42_ne_chi9
      χ (by omega) hNoMono h24_eq_9 h34_eq_9
  · intro ⟨h24_eq_18, h34_eq_18⟩
    exact bAdicEquation_3_chi24_eq_chi18_chi34_eq_chi18_forces_chi42_ne_chi18
      χ (by omega) hNoMono h24_eq_18 h34_eq_18

/-! ### §215. R377 — χ(36)-half canonical entry: directional outputs + χ36BC focus.

  Pivot from the saturated χ54-half (R321 lower) to the χ36-half (R321 upper).
  R321 dispatcher: `(χ54 ∈ {B,C}) ∨ (χ36 ∈ {B,C})`. χ54 half closed at R373/R376.

  **R377 deliverables**:
  - **Part 2** χ36 directional outputs:
    * `chi36_eq_chi27_forces_chi45_ne_chi27` via (27, 36, 45):
      27 + 3·36 = 135 = 3·45.
    * `chi36_eq_chi9_forces_chi39_ne_chi9` via (9, 36, 39):
      9 + 3·36 = 117 = 3·39.
    * `chi36_eq_chi18_forces_chi42_ne_chi18` via (18, 36, 42):
      18 + 3·36 = 126 = 3·42.
  - **Part 2b** `chi36_directional_output_pack`: 3 directional implications.
  - **Part 3** `chi36BC_outputs`: focused χ36 ∈ {B,C} output bundle.

  **Cross-chain audit** (Part 4 documented in comments, no new theorems):
  - R348 χ42=X ∧ χ36=X → χ50≠X: in χ36=C, R377 gives χ42≠C, blocking
    R348-C; in χ36=B, R348-B needs χ42=B source (none active).
  - R356 χ36=X ∧ χ19=X → χ31≠X: needs χ19 classification (none active).
  - R350 χ36=X ∧ χ38=X → χ50≠X: needs χ38 classification (only as
    χ57 fourth-color output, currently inactive). -/

/-- **R377 Part 2-A — χ(36)=A → χ(45) ≠ A** via triple (27, 36, 45):
  27 + 3·36 = 135 = 3·45. -/
theorem bAdicEquation_3_chi36_eq_chi27_forces_chi45_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h45 : 45 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27) :
    χ 45 ≠ χ 27 := by
  intro h45_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 9) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 9) = χ 36
    rw [show (3 * 9 : ℕ) = 27 by decide]
    exact h36_eq_27.symm
  · show χ 36 = χ (36 + 9)
    rw [show (36 + 9 : ℕ) = 45 by decide]
    exact h36_eq_27.trans h45_eq_27.symm

/-- **R377 Part 2-B — χ(36)=B → χ(39) ≠ B** via triple (9, 36, 39):
  9 + 3·36 = 117 = 3·39. -/
theorem bAdicEquation_3_chi36_eq_chi9_forces_chi39_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h39 : 39 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9) :
    χ 39 ≠ χ 9 := by
  intro h39_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 3) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 3) = χ 36
    rw [show (3 * 3 : ℕ) = 9 by decide]
    exact h36_eq_9.symm
  · show χ 36 = χ (36 + 3)
    rw [show (36 + 3 : ℕ) = 39 by decide]
    exact h36_eq_9.trans h39_eq_9.symm

/-- **R377 Part 2-C — χ(36)=C → χ(42) ≠ C** via triple (18, 36, 42):
  18 + 3·36 = 126 = 3·42. -/
theorem bAdicEquation_3_chi36_eq_chi18_forces_chi42_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h42 : 42 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18) :
    χ 42 ≠ χ 18 := by
  intro h42_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 36) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 36
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h36_eq_18.symm
  · show χ 36 = χ (36 + 6)
    rw [show (36 + 6 : ℕ) = 42 by decide]
    exact h36_eq_18.trans h42_eq_18.symm

/-- **R377 Part 2-D — χ(36) directional output pack**: A → χ45, B → χ39, C → χ42. -/
theorem bAdicEquation_3_branchII_chi36_directional_output_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 36 = χ 27 → χ 45 ≠ χ 27) ∧
    (χ 36 = χ 9  → χ 39 ≠ χ 9) ∧
    (χ 36 = χ 18 → χ 42 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h36_eq_27
    exact bAdicEquation_3_chi36_eq_chi27_forces_chi45_ne_chi27
      χ (by omega) hNoMono h36_eq_27
  · intro h36_eq_9
    exact bAdicEquation_3_chi36_eq_chi9_forces_chi39_ne_chi9
      χ (by omega) hNoMono h36_eq_9
  · intro h36_eq_18
    exact bAdicEquation_3_chi36_eq_chi18_forces_chi42_ne_chi18
      χ (by omega) hNoMono h36_eq_18

/-- **R377 Part 3 — χ(36) ∈ {B, C} focused outputs**: canonical entry for the
  R321 upper-half branch. Outputs the χ36=B and χ36=C branches each tagged
  with their forced exclusion. -/
theorem bAdicEquation_3_branchII_chi36BC_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36BC : χ 36 = χ 9 ∨ χ 36 = χ 18) :
    (χ 36 = χ 9 ∧ χ 39 ≠ χ 9) ∨
    (χ 36 = χ 18 ∧ χ 42 ≠ χ 18) := by
  rcases h36BC with h36B | h36C
  · exact Or.inl ⟨h36B,
      bAdicEquation_3_chi36_eq_chi9_forces_chi39_ne_chi9
        χ (by omega) hNoMono h36B⟩
  · exact Or.inr ⟨h36C,
      bAdicEquation_3_chi36_eq_chi18_forces_chi42_ne_chi18
        χ (by omega) hNoMono h36C⟩

/-! ### §216. R378 — χ54/χ36 same-BC mismatch forces χ24ABC.

  Active branch-reduction theorems. The R326 dispatchers excluded one
  χ36 color per χ54 polarity:
  - χ54=B → χ36 ∈ {A, C} (or χ24ABC); χ36=B excluded.
  - χ54=C → χ36 ∈ {A, B} (or χ24ABC); χ36=C excluded.

  Therefore "same-BC" between χ54 and χ36 forces the fallback χ24ABC.
  This is a genuine branch reduction because it converts the χ54 ∧ χ36
  combined disjunction directly into χ24ABC, removing intermediate
  χ36 ABC possibilities.

  - **Part A** `chi54C_chi36C_forces_chi24ABC`: χ54=C ∧ χ36=C → χ24ABC.
  - **Part B** `chi54B_chi36B_forces_chi24ABC`: χ54=B ∧ χ36=B → χ24ABC.

  Combining with R321 dispatcher: when both halves agree, χ24ABC is
  forced as fallback. -/

/-- **R378 Part A — χ(54)=C ∧ χ(36)=C → χ(24)ABC** (mismatch forces fallback).

  Mechanism: R326-C gives `(χ36=A ∨ χ36=B) ∨ χ24ABC`. Under χ36=C, both
  `χ36=A` and `χ36=B` lead to anchor-collision contradictions
  (χ18=χ27 or χ18=χ9). Therefore χ24ABC is the only surviving disjunct. -/
theorem bAdicEquation_3_branchII_chi54C_chi36C_forces_chi24ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h36_eq_18 : χ 36 = χ 18) :
    χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18 := by
  have h18_ne_27 : χ 18 ≠ χ 27 :=
    bAdicEquation_3_chi_18_ne_chi_27_in_monoFree χ (by omega) hNoMono
  have hR326C := bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18
  rcases hR326C with hAorB | h24ABC
  · -- χ36 ∈ {A, B}: collide with χ36 = C.
    exfalso
    rcases hAorB with h36_eq_27 | h36_eq_9
    · -- χ36 = A and χ36 = C ⟹ χ27 = χ18, contradiction.
      exact h18_ne_27 (h36_eq_18.symm.trans h36_eq_27)
    · -- χ36 = B and χ36 = C ⟹ χ18 = χ9, contradiction.
      exact h18_ne_9 (h36_eq_18.symm.trans h36_eq_9)
  · exact h24ABC

/-- **R378 Part B — χ(54)=B ∧ χ(36)=B → χ(24)ABC** (symmetric mismatch).

  Mechanism: R326-B gives `(χ36=A ∨ χ36=C) ∨ χ24ABC`. Under χ36=B, both
  `χ36=A` and `χ36=C` lead to anchor-collision contradictions
  (χ9=χ27 or χ9=χ18). χ24ABC survives. -/
theorem bAdicEquation_3_branchII_chi54B_chi36B_forces_chi24ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_9 : χ 54 = χ 9)
    (h36_eq_9 : χ 36 = χ 9) :
    χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18 := by
  have hR326B := bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9
  rcases hR326B with hAorC | h24ABC
  · -- χ36 ∈ {A, C}: collide with χ36 = B.
    exfalso
    rcases hAorC with h36_eq_27 | h36_eq_18
    · -- χ36 = A and χ36 = B ⟹ χ9 = χ27, contradiction.
      exact h9_ne_27 (h36_eq_9.symm.trans h36_eq_27)
    · -- χ36 = C and χ36 = B ⟹ χ18 = χ9, contradiction.
      exact h18_ne_9 (h36_eq_18.symm.trans h36_eq_9)
  · exact h24ABC

/-- **R378 Part C — χ54/χ36 same-BC pack**: bundles Parts A/B as a single
  same-color implication.  Combines into one statement: any same-BC pair
  (B-B or C-C) between χ54 and χ36 forces χ24ABC. -/
theorem bAdicEquation_3_branchII_chi54_chi36_same_BC_forces_chi24ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (hPair : (χ 54 = χ 9 ∧ χ 36 = χ 9) ∨ (χ 54 = χ 18 ∧ χ 36 = χ 18)) :
    χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18 := by
  rcases hPair with ⟨h54B, h36B⟩ | ⟨h54C, h36C⟩
  · exact bAdicEquation_3_branchII_chi54B_chi36B_forces_chi24ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54B h36B
  · exact bAdicEquation_3_branchII_chi54C_chi36C_forces_chi24ABC
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54C h36C

/-! ### §217. R379 — χ(24)ABC refined consumer + same-BC combined paths.

  Consume R378 same-BC reductions through the R324 χ24/χ16 dispatcher.
  Result: any same-BC pair χ54-χ36 collapses to `χ24 ∈ {A,B} ∨ χ16ABC`,
  pushing the open frontier from χ24 down to χ16 in the C-channel.

  **Important observation**: R324 conclusion `(χ24 ∈ {A,B}) ∨ χ16ABC`
  holds **unconditionally** (no h24ABC needed). So R378 → R324
  composition is purely structural: R378 establishes χ24ABC, R324
  refines χ24=C into χ16ABC, but R324 alone already gives the same
  refinement.

  Deliverables:
  - **Part 1** `chi24ABC_refined_to_AB_or_chi16ABC`: focused alias
    delegating to R324 main (consumes h24ABC; ignores it since R324
    is unconditional).
  - **Part 2** `case_chi54C_chi36C_chi24_refined`: combined path under
    χ54=C ∧ χ36=C; outputs (χ24 ∈ {A,B}) ∨ χ16ABC.
  - **Part 3** `case_chi54B_chi36B_chi24_refined`: symmetric combined path
    under χ54=B ∧ χ36=B.

  **Branch reduction audit**:
  - R378 reduced χ54 ∧ χ36 same-BC into χ24ABC (a 3-value disjunct).
  - R324 further reduces χ24=C into χ16ABC (transfer-position fallback).
  - Net: χ54 ∧ χ36 same-BC → (χ24 ∈ {A,B}) ∨ χ16ABC. **2-value layer
    disjunct + 3-value transfer fallback** is a strict reduction from
    χ24's 3-value original disjunct.

  However, χ16 is a deeper transfer position (3^2 layer below χ72), so
  continuing into χ16 frontier requires committing to R380+ rounds. -/

/-- **R379 Part 1 — χ(24)ABC refined consumer**: focused alias delegating
  to R324 main `chi24_or_chi16_in_ABC` dispatcher.  R324 is unconditional,
  so h24ABC is consumed as marker for downstream call-site clarity. -/
theorem bAdicEquation_3_branchII_chi24ABC_refined_to_AB_or_chi16ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (_h24ABC : χ 24 = χ 27 ∨ χ 24 = χ 9 ∨ χ 24 = χ 18) :
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) :=
  bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9

/-- **R379 Part 2 — χ(54)=C ∧ χ(36)=C combined refined path**: chains
  R378 Part A (χ24ABC) with R324 dispatcher to output the canonical
  2-value layer disjunct + 3-value χ16 fallback. -/
theorem bAdicEquation_3_branchII_case_chi54C_chi36C_chi24_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h36_eq_18 : χ 36 = χ 18) :
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) := by
  have h24ABC := bAdicEquation_3_branchII_chi54C_chi36C_forces_chi24ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_18 h36_eq_18
  exact bAdicEquation_3_branchII_chi24ABC_refined_to_AB_or_chi16ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h24ABC

/-- **R379 Part 3 — χ(54)=B ∧ χ(36)=B combined refined path**: symmetric
  to Part 2 via R378 Part B + R324 dispatcher. -/
theorem bAdicEquation_3_branchII_case_chi54B_chi36B_chi24_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h54_eq_9 : χ 54 = χ 9)
    (h36_eq_9 : χ 36 = χ 9) :
    (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) := by
  have h24ABC := bAdicEquation_3_branchII_chi54B_chi36B_forces_chi24ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h54_eq_9 h36_eq_9
  exact bAdicEquation_3_branchII_chi24ABC_refined_to_AB_or_chi16ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h24ABC

/-! ### §218. R380 — χ(24)/χ(16) canonical downstream entry.

  Build the canonical entry for the R379 same-BC downstream:

    (χ24 = A ∨ χ24 = B) ∨ χ16ABC.

  Each branch is given directional outputs.

  - **Part 1** χ24 directional outputs as x-position (better than y-position):
    * `chi24_eq_chi27_forces_chi35_ne_chi27` via (24, 27, 35):
      24 + 3·27 = 105 = 3·35.
    * `chi24_eq_chi9_forces_chi17_ne_chi9` via (24, 9, 17):
      24 + 3·9 = 51 = 3·17.
    * `chi24_eq_chi18_forces_chi26_ne_chi18` via (24, 18, 26):
      24 + 3·18 = 78 = 3·26.
  - **Part 1-D** `chi24_directional_output_pack`: A/B/C 3-implication pack.
  - **Part 2** `chi24AB_outputs`: χ24 ∈ {A, B} focused output bundle.
  - **Part 3** `chi16ABC_directional_outputs`: focused alias to R352
    `chi16_anchor_exclusion_pack` outputs in branch form.
  - **Part 4** `sameBC_chi24_chi16_downstream_summary`: chains R379
    refined input into Part 2 ∨ Part 3 output structure.

  All outputs are exclusions on layer/transfer positions; no closure. -/

/-- **R380 Part 1-A — χ(24)=A → χ(35) ≠ A** via triple (24, 27, 35):
  24 + 3·27 = 105 = 3·35. -/
theorem bAdicEquation_3_chi24_eq_chi27_forces_chi35_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h35 : 35 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_27 : χ 24 = χ 27) :
    χ 35 ≠ χ 27 := by
  intro h35_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 27) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 27
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_27
  · show χ 27 = χ (27 + 8)
    rw [show (27 + 8 : ℕ) = 35 by decide]
    exact h35_eq_27.symm

/-- **R380 Part 1-B — χ(24)=B → χ(17) ≠ B** via triple (24, 9, 17):
  24 + 3·9 = 51 = 3·17. -/
theorem bAdicEquation_3_chi24_eq_chi9_forces_chi17_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h24 : 24 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_9 : χ 24 = χ 9) :
    χ 17 ≠ χ 9 := by
  intro h17_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 9) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 9
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_9
  · show χ 9 = χ (9 + 8)
    rw [show (9 + 8 : ℕ) = 17 by decide]
    exact h17_eq_9.symm

/-- **R380 Part 1-C — χ(24)=C → χ(26) ≠ C** via triple (24, 18, 26):
  24 + 3·18 = 78 = 3·26. -/
theorem bAdicEquation_3_chi24_eq_chi18_forces_chi26_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h26 : 26 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_18 : χ 24 = χ 18) :
    χ 26 ≠ χ 18 := by
  intro h26_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 18) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 18
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_18
  · show χ 18 = χ (18 + 8)
    rw [show (18 + 8 : ℕ) = 26 by decide]
    exact h26_eq_18.symm

/-- **R380 Part 1-D — χ(24) directional output pack**: A → χ35, B → χ17, C → χ26. -/
theorem bAdicEquation_3_branchII_chi24_directional_output_pack
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 24 = χ 27 → χ 35 ≠ χ 27) ∧
    (χ 24 = χ 9  → χ 17 ≠ χ 9) ∧
    (χ 24 = χ 18 → χ 26 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h24_eq_27
    exact bAdicEquation_3_chi24_eq_chi27_forces_chi35_ne_chi27
      χ (by omega) hNoMono h24_eq_27
  · intro h24_eq_9
    exact bAdicEquation_3_chi24_eq_chi9_forces_chi17_ne_chi9
      χ (by omega) hNoMono h24_eq_9
  · intro h24_eq_18
    exact bAdicEquation_3_chi24_eq_chi18_forces_chi26_ne_chi18
      χ (by omega) hNoMono h24_eq_18

/-- **R380 Part 2 — χ(24) ∈ {A, B} focused outputs**. -/
theorem bAdicEquation_3_branchII_chi24AB_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24AB : χ 24 = χ 27 ∨ χ 24 = χ 9) :
    (χ 24 = χ 27 ∧ χ 35 ≠ χ 27) ∨
    (χ 24 = χ 9 ∧ χ 17 ≠ χ 9) := by
  rcases h24AB with h24A | h24B
  · exact Or.inl ⟨h24A,
      bAdicEquation_3_chi24_eq_chi27_forces_chi35_ne_chi27
        χ (by omega) hNoMono h24A⟩
  · exact Or.inr ⟨h24B,
      bAdicEquation_3_chi24_eq_chi9_forces_chi17_ne_chi9
        χ (by omega) hNoMono h24B⟩

/-- **R380 Part 3 — χ(16)ABC directional outputs (focused alias)**: delegates
  to R352 `chi16_anchor_exclusion_pack` for the χ25/χ19/χ22 outputs. -/
theorem bAdicEquation_3_branchII_chi16ABC_directional_outputs
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16ABC : χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18) :
    (χ 16 = χ 27 ∧ χ 25 ≠ χ 27) ∨
    (χ 16 = χ 9  ∧ χ 19 ≠ χ 9) ∨
    (χ 16 = χ 18 ∧ χ 22 ≠ χ 18) := by
  rcases h16ABC with h16A | h16B | h16C
  · exact Or.inl ⟨h16A,
      bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
        χ (by omega) hNoMono h16A⟩
  · exact Or.inr (Or.inl ⟨h16B,
      bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
        χ (by omega) hNoMono h16B⟩)
  · exact Or.inr (Or.inr ⟨h16C,
      bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
        χ (by omega) hNoMono h16C⟩)

/-- **R380 Part 4 — same-BC χ(24)/χ(16) downstream output summary**.

  Consumes R379-style refined input `(χ24 ∈ {A,B}) ∨ χ16ABC` and outputs
  the per-branch exclusion bundle.  No new arithmetic. -/
theorem bAdicEquation_3_branchII_sameBC_chi24_chi16_downstream_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (_hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (_h27_eq_81 : χ 27 = χ 81)
    (_h9_ne_27 : χ 9 ≠ χ 27)
    (_h18_ne_9 : χ 18 ≠ χ 9)
    (h24_refined : (χ 24 = χ 27 ∨ χ 24 = χ 9) ∨
                    (χ 16 = χ 27 ∨ χ 16 = χ 9 ∨ χ 16 = χ 18)) :
    ((χ 24 = χ 27 ∧ χ 35 ≠ χ 27) ∨
     (χ 24 = χ 9 ∧ χ 17 ≠ χ 9)) ∨
    ((χ 16 = χ 27 ∧ χ 25 ≠ χ 27) ∨
     (χ 16 = χ 9 ∧ χ 19 ≠ χ 9) ∨
     (χ 16 = χ 18 ∧ χ 22 ≠ χ 18)) := by
  rcases h24_refined with h24AB | h16ABC
  · exact Or.inl
      (bAdicEquation_3_branchII_chi24AB_outputs χ h81 hNoMono h24AB)
  · exact Or.inr
      (bAdicEquation_3_branchII_chi16ABC_directional_outputs χ h81 hNoMono h16ABC)

/-! ### §219. R381 — χ(16)=C ∧ χ(22)ABC joint refinement.

  Test whether the χ16ABC output χ22 ≠ C couples actively with the χ22ABC
  disjunct that appears in multiple macro summaries (R325-A fallback,
  R337 expanded, R374 macro Component B).

  **Branch reduction theorem**:
  - `chi16C_chi22ABC_refines_to_AB`: under χ16=C ∧ χ22ABC, derive
    χ22 ∈ {A, B}.

  **Mechanism**: R352 (`chi16_eq_chi18_forces_chi22_ne_chi18`) gives
  χ22 ≠ C from χ16=C. Then R349 helper `branchII_ABC_refine_neC_to_AB`
  collapses χ22ABC into χ22 ∈ {A, B}.

  **Active reduction audit**:
  Co-occurrence of χ16=C and χ22ABC happens when:
  - χ54-χ36 same-BC enters χ16ABC fallback (R379), AND
  - χ72=B macro Component B (or similar) lands on χ22ABC fallback.
  Both are disjunctive disjuncts in current macro summaries, so the
  conjunction is a real co-occurrence scenario in 2D fourth-color paths.
  When activated, this collapses χ22 from 3-value to 2-value. -/

/-- **R381 — χ(16)=C ∧ χ(22)ABC → χ(22) ∈ {A, B}**.

  Under χ16=C, R352 gives χ22 ≠ C. R349 helper neC_to_AB then collapses
  the χ22ABC disjunct. -/
theorem bAdicEquation_3_branchII_chi16C_chi22ABC_refines_to_AB
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h16_eq_18 : χ 16 = χ 18)
    (h22ABC : χ 22 = χ 27 ∨ χ 22 = χ 9 ∨ χ 22 = χ 18) :
    χ 22 = χ 27 ∨ χ 22 = χ 9 := by
  have h22_ne_18 : χ 22 ≠ χ 18 :=
    bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
      χ (by omega) hNoMono h16_eq_18
  exact branchII_ABC_refine_neC_to_AB h22ABC h22_ne_18

/-! ### §220. R383 — χ(72)=C sibling leaf macro entry.

  Pivot to χ72=C sibling leaf (where χ42 becomes active). R337 F-4
  `chi72_eq18_branch_expanded_chi42` already provides the exact χ72=C
  summary:
    ((χ42=A ∧ χ41≠A) ∨ (χ42=B ∧ χ23≠B)) ∨ χ28ABC

  R383 deliverables:
  - **Part 1** `case_72C_chi42_or_chi28_summary`: focused alias to
    R337 F-4 with case-convention naming.
  - **Part 3** `case_72C_macro_entry`: macro entry combining R321
    dispatcher with Part 1 summary as a 2-conjunct And.

  R383 audit (Part 2 χ48 interaction + Part 4 active overlap):
  - **Part 2 χ48 interaction**: R336 `chi72_eq18_chi48ABC_crossed_expansion`
    and R338 `chi72_eq18_chi48ABC_crossed_with_chi42_expanded` exist for
    full crossed coverage. Their statements are large; deferring direct
    expansion. Document as available infrastructure.
  - **Part 4 active overlap**:
    * χ72=C summary: χ42 ∈ {A, B}; χ42=C explicitly excluded by R319.
    * R321 χ36 half: χ36 ∈ {B, C}.
    * Overlap of same-color: only χ42=B ∧ χ36=B (R348-B).
    * χ42=A ∧ χ36=A: blocked because χ36 ∈ {B, C} excludes A.
    * χ42=B ∧ χ36=C: not same-color, no R348 firing.
    * χ42=A ∧ χ36=B/C: not same-color.
  Active cross-chain target for R384: χ42=B ∧ χ36=B → χ50 ≠ B (R348-B). -/

/-- **R383 Part 1 — χ(72)=C compact χ(42)/χ(28) summary**: focused alias to
  R337 F-4 `chi72_eq18_branch_expanded_chi42` with `case_*` convention. -/
theorem bAdicEquation_3_branchII_case_72C_chi42_or_chi28_summary
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18) :
    ((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
     (χ 42 = χ 9 ∧ χ 23 ≠ χ 9)) ∨
    (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) :=
  bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18

/-- **R383 Part 3 — χ(72)=C macro entry with R321 split**: 2-conjunct And
  combining R321 dispatcher (`χ54 ∈ {B,C}) ∨ (χ36 ∈ {B,C})`) with
  Part 1 χ72=C summary. Canonical entry for χ72=C sibling leaf. -/
theorem bAdicEquation_3_branchII_case_72C_macro_entry
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18) :
    ((χ 54 = χ 9 ∨ χ 54 = χ 18) ∨ (χ 36 = χ 9 ∨ χ 36 = χ 18)) ∧
    (((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
      (χ 42 = χ 9 ∧ χ 23 ≠ χ 9)) ∨
     (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18)) := by
  refine ⟨?_, ?_⟩
  · exact bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9
  · exact bAdicEquation_3_branchII_case_72C_chi42_or_chi28_summary
      χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18

/-! ### §221. R384 — active χ(42)=B ∧ χ(36)=B coupling under χ(72)=C.

  R383 identified the only active same-color overlap between R337 F-4
  χ72=C summary (χ42 ∈ {A, B}) and R321 χ36-half (χ36 ∈ {B, C}):
  the χ42=B ∧ χ36=B path, which triggers R348-B (`χ50 ≠ B`).

  R384 enriches the χ42=B sub-branch with the χ50≠B exclusion when
  χ36=B is additionally available.

  **Part 1** R348-B reuse (already in §188; no alias).
  **Part 2** `case_72C_36B_chi42_refined`: under χ72=C ∧ χ36=B, output
    ((χ42=A ∧ χ41≠A) ∨ (χ42=B ∧ χ23≠B ∧ χ50≠B)) ∨ χ28ABC.
  **Part 3** χ36=C audit: under χ72=C ∧ χ36=C, R377 gives χ42 ≠ C;
    R348-C requires χ42=C (now blocked); no firing. Documented only.
  **Part 4** χ50≠B consumption audit:
    - χ50ABC sources: R331-A (χ48=A path), R334/R342 (crossed χ48
      paths). Current χ72=C + χ36=B branch does NOT directly fix χ48,
      so χ50ABC is not in the active disjunct.
    - Conclusion: χ50≠B is **future leverage**, not closure. Active
      only when paired with χ48=A path that brings χ50ABC. -/

/-- **R384 Part 2 — χ(72)=C ∧ χ(36)=B refined χ(42) summary**.

  Enriches R337 F-4 χ72=C summary with χ50≠B in the χ42=B sub-branch
  via R348-B (which fires under χ42=B ∧ χ36=B).  Other sub-branches
  pass through unchanged. -/
theorem bAdicEquation_3_branchII_case_72C_36B_chi42_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h36_eq_9 : χ 36 = χ 9) :
    ((χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
     (χ 42 = χ 9 ∧ χ 23 ≠ χ 9 ∧ χ 50 ≠ χ 9)) ∨
    (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) := by
  have hR337F4 := bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18
  rcases hR337F4 with h42AB | h28ABC
  · rcases h42AB with ⟨h42A, h41_ne_A⟩ | ⟨h42B, h23_ne_B⟩
    · exact Or.inl (Or.inl ⟨h42A, h41_ne_A⟩)
    · -- χ42=B ∧ χ36=B: invoke R348-B to add χ50 ≠ B.
      have h50_ne_9 := bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
        χ (by omega) hNoMono h42B h36_eq_9
      exact Or.inl (Or.inr ⟨h42B, h23_ne_B, h50_ne_9⟩)
  · exact Or.inr h28ABC

/-! ### §222. R387 — Top R386 frontier-search candidates: (24,28,36) + (42,34,48).

  Formalize the two highest-value NEW cross-chain triples identified by
  the R386 frontier search:

  **(24, 28, 36)**: 24 + 3·28 = 108 = 3·36; same-color reading
    χ24=X ∧ χ28=X → χ36 ≠ X.
  Bridges chi36_chi24 + chi42_chi28/chi72_chi42 + chi54_chi36 components.
  Active in 2D fourth-color paths (R321 χ54-half χ24ABC + χ72=C χ28ABC).

  **(42, 34, 48)**: 42 + 3·34 = 144 = 3·48; same-color reading
    χ42=X ∧ χ34=X → χ48 ≠ X.
  Bridges chi42_chi28/chi72_chi42 + chi51_chi34 components. Active in
  χ48=B saturated leaves (contrapositive: χ48=B ∧ χ34=B → χ42 ≠ B).

  Each family has A/B/C variants and a 3-implication pack. -/

/-- **R387 Part 1-A — χ(24)=A ∧ χ(28)=A → χ(36) ≠ A** via triple (24, 28, 36):
  24 + 3·28 = 108 = 3·36. -/
theorem bAdicEquation_3_chi24_eq_chi27_chi28_eq_chi27_forces_chi36_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_27 : χ 24 = χ 27)
    (h28_eq_27 : χ 28 = χ 27) :
    χ 36 ≠ χ 27 := by
  intro h36_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 28
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_27.trans h28_eq_27.symm
  · show χ 28 = χ (28 + 8)
    rw [show (28 + 8 : ℕ) = 36 by decide]
    exact h28_eq_27.trans h36_eq_27.symm

/-- **R387 Part 1-B — χ(24)=B ∧ χ(28)=B → χ(36) ≠ B** via triple (24, 28, 36). -/
theorem bAdicEquation_3_chi24_eq_chi9_chi28_eq_chi9_forces_chi36_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_9 : χ 24 = χ 9)
    (h28_eq_9 : χ 28 = χ 9) :
    χ 36 ≠ χ 9 := by
  intro h36_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 28
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_9.trans h28_eq_9.symm
  · show χ 28 = χ (28 + 8)
    rw [show (28 + 8 : ℕ) = 36 by decide]
    exact h28_eq_9.trans h36_eq_9.symm

/-- **R387 Part 1-C — χ(24)=C ∧ χ(28)=C → χ(36) ≠ C** via triple (24, 28, 36). -/
theorem bAdicEquation_3_chi24_eq_chi18_chi28_eq_chi18_forces_chi36_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_18 : χ 24 = χ 18)
    (h28_eq_18 : χ 28 = χ 18) :
    χ 36 ≠ χ 18 := by
  intro h36_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 8) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 8) = χ 28
    rw [show (3 * 8 : ℕ) = 24 by decide]
    exact h24_eq_18.trans h28_eq_18.symm
  · show χ 28 = χ (28 + 8)
    rw [show (28 + 8 : ℕ) = 36 by decide]
    exact h28_eq_18.trans h36_eq_18.symm

/-- **R387 Part 1-D — χ(24)/χ(28)/χ(36) cross-refinement pack**: 3 same-color
  implications bundled. -/
theorem bAdicEquation_3_branchII_chi24_chi28_chi36_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 24 = χ 27 → χ 28 = χ 27 → χ 36 ≠ χ 27) ∧
    (χ 24 = χ 9  → χ 28 = χ 9  → χ 36 ≠ χ 9) ∧
    (χ 24 = χ 18 → χ 28 = χ 18 → χ 36 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h24_eq_27 h28_eq_27
    exact bAdicEquation_3_chi24_eq_chi27_chi28_eq_chi27_forces_chi36_ne_chi27
      χ h36 hNoMono h24_eq_27 h28_eq_27
  · intro h24_eq_9 h28_eq_9
    exact bAdicEquation_3_chi24_eq_chi9_chi28_eq_chi9_forces_chi36_ne_chi9
      χ h36 hNoMono h24_eq_9 h28_eq_9
  · intro h24_eq_18 h28_eq_18
    exact bAdicEquation_3_chi24_eq_chi18_chi28_eq_chi18_forces_chi36_ne_chi18
      χ h36 hNoMono h24_eq_18 h28_eq_18

/-- **R387 Part 2-A — χ(42)=A ∧ χ(34)=A → χ(48) ≠ A** via triple (42, 34, 48):
  42 + 3·34 = 144 = 3·48. -/
theorem bAdicEquation_3_chi42_eq_chi27_chi34_eq_chi27_forces_chi48_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_27 : χ 42 = χ 27)
    (h34_eq_27 : χ 34 = χ 27) :
    χ 48 ≠ χ 27 := by
  intro h48_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 34
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_27.trans h34_eq_27.symm
  · show χ 34 = χ (34 + 14)
    rw [show (34 + 14 : ℕ) = 48 by decide]
    exact h34_eq_27.trans h48_eq_27.symm

/-- **R387 Part 2-B — χ(42)=B ∧ χ(34)=B → χ(48) ≠ B** via triple (42, 34, 48). -/
theorem bAdicEquation_3_chi42_eq_chi9_chi34_eq_chi9_forces_chi48_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_9 : χ 42 = χ 9)
    (h34_eq_9 : χ 34 = χ 9) :
    χ 48 ≠ χ 9 := by
  intro h48_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 34
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_9.trans h34_eq_9.symm
  · show χ 34 = χ (34 + 14)
    rw [show (34 + 14 : ℕ) = 48 by decide]
    exact h34_eq_9.trans h48_eq_9.symm

/-- **R387 Part 2-C — χ(42)=C ∧ χ(34)=C → χ(48) ≠ C** via triple (42, 34, 48). -/
theorem bAdicEquation_3_chi42_eq_chi18_chi34_eq_chi18_forces_chi48_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h42_eq_18 : χ 42 = χ 18)
    (h34_eq_18 : χ 34 = χ 18) :
    χ 48 ≠ χ 18 := by
  intro h48_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 14) (y := 34) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 14) = χ 34
    rw [show (3 * 14 : ℕ) = 42 by decide]
    exact h42_eq_18.trans h34_eq_18.symm
  · show χ 34 = χ (34 + 14)
    rw [show (34 + 14 : ℕ) = 48 by decide]
    exact h34_eq_18.trans h48_eq_18.symm

/-- **R387 Part 2-D — χ(42)/χ(34)/χ(48) cross-refinement pack**: 3 same-color
  implications bundled. -/
theorem bAdicEquation_3_branchII_chi42_chi34_chi48_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 42 = χ 27 → χ 34 = χ 27 → χ 48 ≠ χ 27) ∧
    (χ 42 = χ 9  → χ 34 = χ 9  → χ 48 ≠ χ 9) ∧
    (χ 42 = χ 18 → χ 34 = χ 18 → χ 48 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h42_eq_27 h34_eq_27
    exact bAdicEquation_3_chi42_eq_chi27_chi34_eq_chi27_forces_chi48_ne_chi27
      χ h48 hNoMono h42_eq_27 h34_eq_27
  · intro h42_eq_9 h34_eq_9
    exact bAdicEquation_3_chi42_eq_chi9_chi34_eq_chi9_forces_chi48_ne_chi9
      χ h48 hNoMono h42_eq_9 h34_eq_9
  · intro h42_eq_18 h34_eq_18
    exact bAdicEquation_3_chi42_eq_chi18_chi34_eq_chi18_forces_chi48_ne_chi18
      χ h48 hNoMono h42_eq_18 h34_eq_18

/-! ### §223. R388 — Integrate R387 cross-chains into active macro summaries.

  Test whether the two R387 candidates reduce live branches.

  - **Part 1** (42, 34, 48) closure: in χ48=B leaf, the triple gives
    `χ48=B ∧ χ34=B ∧ χ42=B → False`. This is a **branch closure**
    (3-conjunct contradiction).
  - **Part 2** χ72=C ∧ χ48=B ∧ χ34=B refined χ42 summary: collapses the
    χ72=C dispatcher's χ42=B branch via Part 1, leaving only
    `(χ42=A ∧ χ41≠A) ∨ χ28ABC`.
  - **Part 3-B** χ24=B ∧ χ28=B ∧ χ36BC → χ36 = C.
  - **Part 3-C** χ24=C ∧ χ28=C ∧ χ36BC → χ36 = B.

  Part 1-2: active in χ48=B ∧ χ72=C cross-leaf scenario.
  Part 3: active in 2D fourth-color paths (R321 χ54-half fallback +
    χ72=C χ28ABC fallback). -/

/-- **R388 Part 1 — χ(48)=B ∧ χ(34)=B ∧ χ(42)=B → False**.

  Direct contradiction from R387 Part 2-B (`chi42=B ∧ χ34=B → χ48≠B`).
  Branch closure for the 3-conjunct simultaneously-B state. -/
theorem bAdicEquation_3_branchII_chi48B_chi34B_chi42B_false
    {n : ℕ} (χ : ℕ → ℕ) (h48 : 48 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9)
    (h42_eq_9 : χ 42 = χ 9) :
    False :=
  bAdicEquation_3_chi42_eq_chi9_chi34_eq_chi9_forces_chi48_ne_chi9
    χ h48 hNoMono h42_eq_9 h34_eq_9 h48_eq_9

/-- **R388 Part 2 — χ(72)=C ∧ χ(48)=B ∧ χ(34)=B refines χ(42) summary**.

  Under χ72=C, R337 F-4 gives `(χ42=A ∧ χ41≠A) ∨ (χ42=B ∧ χ23≠B) ∨ χ28ABC`.
  Under the additional χ48=B ∧ χ34=B, the χ42=B branch is impossible
  (Part 1 contradiction). Remaining disjuncts: `χ42=A ∧ χ41≠A` or χ28ABC.

  **Real branch reduction**: 3-disjunct → 2-disjunct. -/
theorem bAdicEquation_3_branchII_case_72C_48B_34B_refines_chi42_to_A_or_chi28ABC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9) :
    (χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
    (χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) := by
  have hR337F4 := bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18
  rcases hR337F4 with h42AB | h28ABC
  · rcases h42AB with ⟨h42A, h41_ne_A⟩ | ⟨h42B, _h23_ne_B⟩
    · exact Or.inl ⟨h42A, h41_ne_A⟩
    · -- χ42=B contradicts χ48=B ∧ χ34=B via Part 1.
      exfalso
      exact bAdicEquation_3_branchII_chi48B_chi34B_chi42B_false
        χ (by omega) hNoMono h48_eq_9 h34_eq_9 h42B
  · exact Or.inr h28ABC

/-- **R388 Part 3-B — χ(24)=B ∧ χ(28)=B ∧ χ(36) ∈ {B,C} → χ(36) = C**.

  R387 Part 1-B gives χ24=B ∧ χ28=B → χ36 ≠ B. Combined with R321
  χ36 ∈ {B, C} restriction, forces χ36 = C. -/
theorem bAdicEquation_3_branchII_chi24B_chi28B_chi36BC_forces_chi36C
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_9 : χ 24 = χ 9)
    (h28_eq_9 : χ 28 = χ 9)
    (h36BC : χ 36 = χ 9 ∨ χ 36 = χ 18) :
    χ 36 = χ 18 := by
  have h36_ne_9 := bAdicEquation_3_chi24_eq_chi9_chi28_eq_chi9_forces_chi36_ne_chi9
    χ h36 hNoMono h24_eq_9 h28_eq_9
  rcases h36BC with h36B | h36C
  · exact absurd h36B h36_ne_9
  · exact h36C

/-- **R388 Part 3-C — χ(24)=C ∧ χ(28)=C ∧ χ(36) ∈ {B,C} → χ(36) = B**.

  R387 Part 1-C gives χ24=C ∧ χ28=C → χ36 ≠ C. Combined with R321
  χ36 ∈ {B, C}, forces χ36 = B. -/
theorem bAdicEquation_3_branchII_chi24C_chi28C_chi36BC_forces_chi36B
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h24_eq_18 : χ 24 = χ 18)
    (h28_eq_18 : χ 28 = χ 18)
    (h36BC : χ 36 = χ 9 ∨ χ 36 = χ 18) :
    χ 36 = χ 9 := by
  have h36_ne_18 := bAdicEquation_3_chi24_eq_chi18_chi28_eq_chi18_forces_chi36_ne_chi18
    χ h36 hNoMono h24_eq_18 h28_eq_18
  rcases h36BC with h36B | h36C
  · exact h36B
  · exact absurd h36C h36_ne_18

/-! ### §224. R391 — R390 active candidates: (60,28,48), (36,16,28), (18,28,34).

  Formalize the three highest-value ACTIVE candidates identified by the
  R390 targeted frontier search:

  **(60, 28, 48)**: 60 + 3·28 = 144 = 3·48; χ60=X ∧ χ28=X → χ48 ≠ X.
  Closure-type: in χ48=B leaf, χ60=B ∧ χ28=B → False.

  **(36, 16, 28)**: 36 + 3·16 = 84 = 3·28; χ36=X ∧ χ16=X → χ28 ≠ X.
  Active in 2D fallback paths (R321 χ36-half + R324 χ16ABC + χ72=C χ28ABC).

  **(18, 28, 34)**: 18 + 3·28 = 102 = 3·34; χ28=C → χ34 ≠ C.
  Anchor-driven; narrows χ72=C dispatcher's χ28ABC fourth-color path. -/

/-- **R391 Part 1-A — χ(60)=A ∧ χ(28)=A → χ(48) ≠ A** via triple (60, 28, 48):
  60 + 3·28 = 144 = 3·48. -/
theorem bAdicEquation_3_chi60_eq_chi27_chi28_eq_chi27_forces_chi48_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_27 : χ 60 = χ 27)
    (h28_eq_27 : χ 28 = χ 27) :
    χ 48 ≠ χ 27 := by
  intro h48_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 20) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 20) = χ 28
    rw [show (3 * 20 : ℕ) = 60 by decide]
    exact h60_eq_27.trans h28_eq_27.symm
  · show χ 28 = χ (28 + 20)
    rw [show (28 + 20 : ℕ) = 48 by decide]
    exact h28_eq_27.trans h48_eq_27.symm

/-- **R391 Part 1-B — χ(60)=B ∧ χ(28)=B → χ(48) ≠ B** via triple (60, 28, 48). -/
theorem bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_9 : χ 60 = χ 9)
    (h28_eq_9 : χ 28 = χ 9) :
    χ 48 ≠ χ 9 := by
  intro h48_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 20) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 20) = χ 28
    rw [show (3 * 20 : ℕ) = 60 by decide]
    exact h60_eq_9.trans h28_eq_9.symm
  · show χ 28 = χ (28 + 20)
    rw [show (28 + 20 : ℕ) = 48 by decide]
    exact h28_eq_9.trans h48_eq_9.symm

/-- **R391 Part 1-C — χ(60)=C ∧ χ(28)=C → χ(48) ≠ C** via triple (60, 28, 48). -/
theorem bAdicEquation_3_chi60_eq_chi18_chi28_eq_chi18_forces_chi48_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h60_eq_18 : χ 60 = χ 18)
    (h28_eq_18 : χ 28 = χ 18) :
    χ 48 ≠ χ 18 := by
  intro h48_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 20) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 20) = χ 28
    rw [show (3 * 20 : ℕ) = 60 by decide]
    exact h60_eq_18.trans h28_eq_18.symm
  · show χ 28 = χ (28 + 20)
    rw [show (28 + 20 : ℕ) = 48 by decide]
    exact h28_eq_18.trans h48_eq_18.symm

/-- **R391 Part 1-D — χ(60)/χ(28)/χ(48) cross-refinement pack**. -/
theorem bAdicEquation_3_branchII_chi60_chi28_chi48_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 60 = χ 27 → χ 28 = χ 27 → χ 48 ≠ χ 27) ∧
    (χ 60 = χ 9  → χ 28 = χ 9  → χ 48 ≠ χ 9) ∧
    (χ 60 = χ 18 → χ 28 = χ 18 → χ 48 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h60_eq_27 h28_eq_27
    exact bAdicEquation_3_chi60_eq_chi27_chi28_eq_chi27_forces_chi48_ne_chi27
      χ h60 hNoMono h60_eq_27 h28_eq_27
  · intro h60_eq_9 h28_eq_9
    exact bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
      χ h60 hNoMono h60_eq_9 h28_eq_9
  · intro h60_eq_18 h28_eq_18
    exact bAdicEquation_3_chi60_eq_chi18_chi28_eq_chi18_forces_chi48_ne_chi18
      χ h60 hNoMono h60_eq_18 h28_eq_18

/-- **R391 Part 1-E — χ(48)=B ∧ χ(60)=B ∧ χ(28)=B → False** (closure-type). -/
theorem bAdicEquation_3_branchII_chi48B_chi60B_chi28B_false
    {n : ℕ} (χ : ℕ → ℕ) (h60 : 60 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h60_eq_9 : χ 60 = χ 9)
    (h28_eq_9 : χ 28 = χ 9) :
    False :=
  bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
    χ h60 hNoMono h60_eq_9 h28_eq_9 h48_eq_9

/-- **R391 Part 2-A — χ(36)=A ∧ χ(16)=A → χ(28) ≠ A** via triple (36, 16, 28):
  36 + 3·16 = 84 = 3·28. -/
theorem bAdicEquation_3_chi36_eq_chi27_chi16_eq_chi27_forces_chi28_ne_chi27
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_27 : χ 36 = χ 27)
    (h16_eq_27 : χ 16 = χ 27) :
    χ 28 ≠ χ 27 := by
  intro h28_eq_27
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 16
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_27.trans h16_eq_27.symm
  · show χ 16 = χ (16 + 12)
    rw [show (16 + 12 : ℕ) = 28 by decide]
    exact h16_eq_27.trans h28_eq_27.symm

/-- **R391 Part 2-B — χ(36)=B ∧ χ(16)=B → χ(28) ≠ B** via triple (36, 16, 28). -/
theorem bAdicEquation_3_chi36_eq_chi9_chi16_eq_chi9_forces_chi28_ne_chi9
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h16_eq_9 : χ 16 = χ 9) :
    χ 28 ≠ χ 9 := by
  intro h28_eq_9
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 16
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_9.trans h16_eq_9.symm
  · show χ 16 = χ (16 + 12)
    rw [show (16 + 12 : ℕ) = 28 by decide]
    exact h16_eq_9.trans h28_eq_9.symm

/-- **R391 Part 2-C — χ(36)=C ∧ χ(16)=C → χ(28) ≠ C** via triple (36, 16, 28). -/
theorem bAdicEquation_3_chi36_eq_chi18_chi16_eq_chi18_forces_chi28_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h16_eq_18 : χ 16 = χ 18) :
    χ 28 ≠ χ 18 := by
  intro h28_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 12) (y := 16) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 12) = χ 16
    rw [show (3 * 12 : ℕ) = 36 by decide]
    exact h36_eq_18.trans h16_eq_18.symm
  · show χ 16 = χ (16 + 12)
    rw [show (16 + 12 : ℕ) = 28 by decide]
    exact h16_eq_18.trans h28_eq_18.symm

/-- **R391 Part 2-D — χ(36)/χ(16)/χ(28) cross-refinement pack**. -/
theorem bAdicEquation_3_branchII_chi36_chi16_chi28_cross_refinement
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ) :
    (χ 36 = χ 27 → χ 16 = χ 27 → χ 28 ≠ χ 27) ∧
    (χ 36 = χ 9  → χ 16 = χ 9  → χ 28 ≠ χ 9) ∧
    (χ 36 = χ 18 → χ 16 = χ 18 → χ 28 ≠ χ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h36_eq_27 h16_eq_27
    exact bAdicEquation_3_chi36_eq_chi27_chi16_eq_chi27_forces_chi28_ne_chi27
      χ h36 hNoMono h36_eq_27 h16_eq_27
  · intro h36_eq_9 h16_eq_9
    exact bAdicEquation_3_chi36_eq_chi9_chi16_eq_chi9_forces_chi28_ne_chi9
      χ h36 hNoMono h36_eq_9 h16_eq_9
  · intro h36_eq_18 h16_eq_18
    exact bAdicEquation_3_chi36_eq_chi18_chi16_eq_chi18_forces_chi28_ne_chi18
      χ h36 hNoMono h36_eq_18 h16_eq_18

/-- **R391 Part 3 — χ(28)=C → χ(34) ≠ C** via triple (18, 28, 34):
  18 + 3·28 = 102 = 3·34. C-anchor-driven single variant. -/
theorem bAdicEquation_3_chi28_eq_chi18_forces_chi34_ne_chi18
    {n : ℕ} (χ : ℕ → ℕ) (h34 : 34 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h28_eq_18 : χ 28 = χ 18) :
    χ 34 ≠ χ 18 := by
  intro h34_eq_18
  have hRado := bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := 6) (y := 28) (by omega) (by omega) (by omega) (by omega)
  apply hRado
  refine ⟨?_, ?_⟩
  · show χ (3 * 6) = χ 28
    rw [show (3 * 6 : ℕ) = 18 by decide]
    exact h28_eq_18.symm
  · show χ 28 = χ (28 + 6)
    rw [show (28 + 6 : ℕ) = 34 by decide]
    exact h28_eq_18.trans h34_eq_18.symm

/-! ### §225. R392 — Integrate R391 cross-chains into active reduced branches.

  Test whether the R391 candidates further reduce R388/R390 live branches.

  - **Part 1** χ48=B ∧ χ54=C ∧ χ51=A ∧ χ60ABC ∧ χ28ABC → χ28 ∈ {A, C}.
    Uses R363 chain (forces χ60=B) + R391 Part 1-E closure.
  - **Part 2** Combined with R388 Part 2 under shared hypotheses:
    `(χ42=A ∧ χ41≠A) ∨ (χ28 ∈ {A, C})`.
  - **Part 3-B** χ36=B ∧ χ16=B ∧ χ28ABC → χ28 ∈ {A, C}.
  - **Part 3-C** χ36=C ∧ χ16=C ∧ χ28ABC → χ28 ∈ {A, B}.
  - **Part 4** χ28=C ∧ χ34ABC → χ34 ∈ {A, B}. -/

/-- **R392 Part 1 — χ48=B ∧ χ54=C ∧ χ51=A ∧ χ60ABC ∧ χ28ABC → χ28 ∈ {A, C}**.

  Cascades through R363 (χ60=B from χ54=C ∧ χ51=A ∧ χ60ABC) and R391
  Part 1-E (χ48=B ∧ χ60=B ∧ χ28=B → False) to eliminate χ28=B. -/
theorem bAdicEquation_3_branchII_case_48B_54C_51A_chi60ABC_chi28ABC_refines_to_AC
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h48_eq_9 : χ 48 = χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18)
    (h28ABC : χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) :
    χ 28 = χ 27 ∨ χ 28 = χ 18 := by
  have h60_eq_9 := bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
    χ h81 hNoMono h54_eq_18 h51_eq_27 h60ABC
  rcases h28ABC with h28A | h28B | h28C
  · exact Or.inl h28A
  · -- χ28=B: closure contradiction via R391 Part 1-E.
    exact absurd
      (bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
        χ (by omega) hNoMono h60_eq_9 h28B)
      (fun h => h h48_eq_9)
  · exact Or.inr h28C

/-- **R392 Part 2 — combined R388 Part 2 + R392 Part 1 refinement**.

  Under χ72=C ∧ χ48=B ∧ χ34=B ∧ χ54=C ∧ χ51=A ∧ χ60ABC, the R388
  output `(χ42=A ∧ χ41≠A) ∨ χ28ABC` further refines to:
    (χ42=A ∧ χ41≠A) ∨ (χ28 ∈ {A, C}). -/
theorem bAdicEquation_3_branchII_case_72C_48B_34B_54C_51A_chi60ABC_refined
    {n : ℕ} (χ : ℕ → ℕ) (h81 : 81 ≤ n)
    (hχk : IsKColoring n 4 χ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h27_eq_81 : χ 27 = χ 81)
    (h9_ne_27 : χ 9 ≠ χ 27)
    (h18_ne_9 : χ 18 ≠ χ 9)
    (h72_eq_18 : χ 72 = χ 18)
    (h48_eq_9 : χ 48 = χ 9)
    (h34_eq_9 : χ 34 = χ 9)
    (h54_eq_18 : χ 54 = χ 18)
    (h51_eq_27 : χ 51 = χ 27)
    (h60ABC : χ 60 = χ 27 ∨ χ 60 = χ 9 ∨ χ 60 = χ 18) :
    (χ 42 = χ 27 ∧ χ 41 ≠ χ 27) ∨
    (χ 28 = χ 27 ∨ χ 28 = χ 18) := by
  have hR388 := bAdicEquation_3_branchII_case_72C_48B_34B_refines_chi42_to_A_or_chi28ABC
    χ h81 hχk hNoMono h27_eq_81 h9_ne_27 h18_ne_9 h72_eq_18 h48_eq_9 h34_eq_9
  rcases hR388 with h42A | h28ABC
  · exact Or.inl h42A
  · exact Or.inr
      (bAdicEquation_3_branchII_case_48B_54C_51A_chi60ABC_chi28ABC_refines_to_AC
        χ h81 hNoMono h48_eq_9 h54_eq_18 h51_eq_27 h60ABC h28ABC)

/-- **R392 Part 3-B — χ(36)=B ∧ χ(16)=B ∧ χ(28)ABC → χ(28) ∈ {A, C}**. -/
theorem bAdicEquation_3_branchII_chi36B_chi16B_chi28ABC_refines_to_AC
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_9 : χ 36 = χ 9)
    (h16_eq_9 : χ 16 = χ 9)
    (h28ABC : χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) :
    χ 28 = χ 27 ∨ χ 28 = χ 18 := by
  have h28_ne_9 := bAdicEquation_3_chi36_eq_chi9_chi16_eq_chi9_forces_chi28_ne_chi9
    χ h36 hNoMono h36_eq_9 h16_eq_9
  rcases h28ABC with h28A | h28B | h28C
  · exact Or.inl h28A
  · exact absurd h28B h28_ne_9
  · exact Or.inr h28C

/-- **R392 Part 3-C — χ(36)=C ∧ χ(16)=C ∧ χ(28)ABC → χ(28) ∈ {A, B}**. -/
theorem bAdicEquation_3_branchII_chi36C_chi16C_chi28ABC_refines_to_AB
    {n : ℕ} (χ : ℕ → ℕ) (h36 : 36 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h36_eq_18 : χ 36 = χ 18)
    (h16_eq_18 : χ 16 = χ 18)
    (h28ABC : χ 28 = χ 27 ∨ χ 28 = χ 9 ∨ χ 28 = χ 18) :
    χ 28 = χ 27 ∨ χ 28 = χ 9 := by
  have h28_ne_18 := bAdicEquation_3_chi36_eq_chi18_chi16_eq_chi18_forces_chi28_ne_chi18
    χ h36 hNoMono h36_eq_18 h16_eq_18
  rcases h28ABC with h28A | h28B | h28C
  · exact Or.inl h28A
  · exact Or.inr h28B
  · exact absurd h28C h28_ne_18

/-- **R392 Part 4 — χ(28)=C ∧ χ(34)ABC → χ(34) ∈ {A, B}**. -/
theorem bAdicEquation_3_branchII_chi28C_chi34ABC_refines_to_AB
    {n : ℕ} (χ : ℕ → ℕ) (h34 : 34 ≤ n)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    (h28_eq_18 : χ 28 = χ 18)
    (h34ABC : χ 34 = χ 27 ∨ χ 34 = χ 9 ∨ χ 34 = χ 18) :
    χ 34 = χ 27 ∨ χ 34 = χ 9 := by
  have h34_ne_18 := bAdicEquation_3_chi28_eq_chi18_forces_chi34_ne_chi18
    χ h34 hNoMono h28_eq_18
  rcases h34ABC with h34A | h34B | h34C
  · exact Or.inl h34A
  · exact Or.inr h34B
  · exact absurd h34C h34_ne_18

/-! ### §226. R397 — Generic same-color exclusion theorem for SAT-MUS bulk import.

  R396 verified n=81 UNSAT under Branch II anchor setup. The minimum UNSAT
  core has 872 unique triples × up to 4 colors = 1504 no-mono clauses.

  To avoid writing 1504 individual same-color exclusion lemmas by hand,
  we provide a **single generic theorem** that, given:

    - a triple (3·d, y, y+d) (equivalently x + 3y = 3z with x = 3d),
    - a color witness k : ℕ,
    - hypotheses χ(3·d) = k and χ(y) = k,

  yields χ(y+d) ≠ k. This is the minimal closed-form same-color exclusion
  for `bAdicEquation 3`, ready for mechanical clause-by-clause invocation
  in a generated MUS file.

  **Anchor normalization audit**:
  R396 SAT MUS used anchor positions:
    χ27 = χ81 = 0 (A), χ9 = 1 (B), χ18 = 2 (C).
  These are EXACTLY the Branch II setup (R318):
    h27_eq_81, h9_ne_27, h18_ne_9.
  Hence R396 establishes **Branch II at n=81 is UNSAT**, which is the
  case Bridge.lean has been pursuing since R313. The complementary
  Branch I (χ18 = χ9) and the χ27 ≠ χ81 case require separate handling
  (out of R396 scope).

  Generic theorem proof: thin wrapper over R313 era
  `bAdicEquation_general_rado_constraint`. -/

/-- **R397 generic same-color exclusion for b=3**:
  given d, y ≥ 1 with 3·d ≤ n and y + d ≤ n, and a color value k with
  χ(3·d) = k and χ(y) = k, conclude χ(y + d) ≠ k.

  All same-color exclusion clauses in the R396 SAT MUS can be discharged
  via a single invocation of this theorem with appropriate (d, y, k). -/
theorem bAdicEquation_3_same_color_excl
    {n : ℕ} (χ : ℕ → ℕ)
    (hNoMono : ¬ HasMonoSolution (bAdicEquation 3) n χ)
    {d y k : ℕ}
    (hd : 1 ≤ d) (hy : 1 ≤ y)
    (hbd : 3 * d ≤ n) (hyd : y + d ≤ n)
    (hxk : χ (3 * d) = k) (hyk : χ y = k) :
    χ (y + d) ≠ k := by
  intro hzk
  apply bAdicEquation_general_rado_constraint
    (b := 3) (n := n) (by omega) χ hNoMono
    (d := d) (y := y) hd hy hbd hyd
  exact ⟨hxk.trans hyk.symm, hyk.trans hzk.symm⟩

end RadoNumbers.General
