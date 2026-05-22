/-
  RadoNumbers/General/BAdicEquation.lean

  Specific instance: the b-adic Rado equation x + by - bz = 0.

  This is the central equation of the project. We define it in the general
  framework (`LinearEquation`) and prove basic properties.

  Bridge to project's HasMonoSolution / AvoidsMonoSolution is in
  `RadoNumbers/General/Bridge.lean` (separate, to keep General/ free of
  project-specific dependencies).
-/

import RadoNumbers.General.PartitionRegular
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace RadoNumbers.General

/--
  **The b-adic Rado equation** x + b·y - b·z = 0.

  For b ≥ 2, defines a 3-variable linear equation with coefficients (1, b, -b).
  Solutions (x, y, z) over ℕ satisfy x + b·y = b·z, i.e., z = (x + b·y)/b.
  Integer solutions require b | x.

  Examples:
  - b = 2: equation x + 2y = 2z (Schur-related).
  - b = 3: equation x + 3y = 3z (our central equation, R_3(3) = 27).
-/
def bAdicEquation (b : ℕ) : LinearEquation where
  coeffs := [(1 : ℤ), (b : ℤ), -(b : ℤ)]
  nontrivial := by simp

/--
  **Number of variables in bAdicEquation is 3.**
-/
theorem bAdicEquation_numVars (b : ℕ) : (bAdicEquation b).numVars = 3 := by
  unfold bAdicEquation LinearEquation.numVars
  rfl

/--
  **The specific equation for b = 3** (our central case).
-/
def radoEq_3 : LinearEquation := bAdicEquation 3

/--
  **Coefficient list** for radoEq_3 is [1, 3, -3].
-/
theorem radoEq_3_coeffs : radoEq_3.coeffs = [(1 : ℤ), 3, -3] := by
  unfold radoEq_3 bAdicEquation
  decide

/--
  **Explicit evaluation** of radoEq_3: eval x = x 0 + 3·x 1 - 3·x 2.

  Computed directly from the eval definition (foldl over zipIdx).
-/
theorem eval_radoEq_3 (x : ℕ → ℤ) :
    radoEq_3.eval x = x 0 + 3 * x 1 - 3 * x 2 := by
  unfold radoEq_3 bAdicEquation LinearEquation.eval
  simp [List.zipIdx]
  omega

/--
  **Explicit evaluation** of bAdicEquation b: eval x = x 0 + b·x 1 - b·x 2.

  Generalizes eval_radoEq_3 to arbitrary b.
-/
theorem eval_bAdicEquation (b : ℕ) (x : ℕ → ℤ) :
    (bAdicEquation b).eval x = x 0 + (b : ℤ) * x 1 - (b : ℤ) * x 2 := by
  unfold bAdicEquation LinearEquation.eval
  simp [List.zipIdx]
  ring

/--
  **Canonical positive solution** for bAdicEquation b (b ≥ 1):
  (x, y, z) = (b, 1, 2) satisfies x + b·y = b·z (i.e., b + b = 2b).

  Returns the witness function fun i => if i = 0 then b else if i = 1 then 1 else 2.
  Useful in any proof that needs to construct a mono solution via the smallest
  positive triple.
-/
theorem bAdicEquation_hasPositiveSolution (b : ℕ) (hb : 1 ≤ b) :
    (bAdicEquation b).IsPositiveSolution
      (fun i => if i = 0 then b else if i = 1 then 1 else 2) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
    rw [hnv] at hi
    match i, hi with
    | 0, _ => simp; omega
    | 1, _ => simp
    | 2, _ => simp
  · rw [eval_bAdicEquation]
    simp
    ring

/--
  **HasPosSolution** for bAdicEquation b (b ≥ 1): the b-adic equation always
  has at least one positive solution (via the canonical (b, 1, 2) triple).

  Existential form for downstream use; doesn't require knowing the witness.
-/
theorem bAdicEquation_exists_positive_solution (b : ℕ) (hb : 1 ≤ b) :
    ∃ x : ℕ → ℕ, (bAdicEquation b).IsPositiveSolution x :=
  ⟨_, bAdicEquation_hasPositiveSolution b hb⟩

/--
  **Schur equation** = bAdicEquation 1 (i.e., x + y - z = 0).

  Special case for which Schur's theorem applies: partition regular for
  all k ≥ 1. The first Schur triple is (x, y, z) = (1, 1, 2).
-/
def schurEquation : LinearEquation := bAdicEquation 1

/--
  **Schur equation has positive solution (1, 1, 2)** : x + y = z with
  x = 1, y = 1, z = 2 (the smallest Schur triple).
-/
theorem schurEquation_hasPositiveSolution :
    schurEquation.IsPositiveSolution
      (fun i => if i = 0 then 1 else if i = 1 then 1 else 2) := by
  unfold schurEquation
  exact bAdicEquation_hasPositiveSolution 1 (by omega)

/--
  **Number of variables in schurEquation is 3** (same as bAdicEquation).
-/
theorem schurEquation_numVars : schurEquation.numVars = 3 :=
  bAdicEquation_numVars 1

/--
  **Schur evaluation**: schurEquation evaluated at x is x 0 + x 1 - x 2.
-/
theorem eval_schurEquation (x : ℕ → ℤ) :
    schurEquation.eval x = x 0 + x 1 - x 2 := by
  unfold schurEquation
  have h := eval_bAdicEquation 1 x
  simp at h
  exact h

/-! ### b-adic valuation in General/ namespace (foundation for valuation coloring).

  Recursive definition: bAdicVal b n = largest k with b^k | n.

  For b = 1: trivially 0 (only n = 0 has b^k | n for all k, but we return 0).
  For b ≥ 2, n > 0: standard b-adic valuation.

  This is the foundation for the VALUATION COLORING lower bound:
    chi_v(n) := bAdicVal b n mod k.
  The valuation coloring is mono-free for bAdicEquation b on [1, b^k - 1],
  giving R_k(b) ≥ b^k (lower bound direction of the threshold conjecture).
-/

/--
  **b-adic valuation**: bAdicVal b n = largest k such that b^k divides n.
  Recursive: if b ≥ 2 and b | n, return 1 + bAdicVal b (n/b); else 0.
-/
def bAdicVal (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ 0 < n ∧ n % b = 0 then
    have : n / b < n := Nat.div_lt_self h.2.1 h.1
    1 + bAdicVal b (n / b)
  else 0
  termination_by n

/--
  **bAdicVal at 0**: bAdicVal b 0 = 0 (no positive multiplicities by convention).
-/
@[simp]
theorem bAdicVal_zero (b : ℕ) : bAdicVal b 0 = 0 := by
  unfold bAdicVal
  simp

/--
  **bAdicVal for b < 2**: trivially 0 (no valuation defined for b ∈ {0, 1}).
-/
@[simp]
theorem bAdicVal_lt_two (b n : ℕ) (hb : b < 2) : bAdicVal b n = 0 := by
  unfold bAdicVal
  simp
  intros
  omega

/--
  **bAdicVal of non-multiple**: if b ∤ n, then bAdicVal b n = 0.
-/
theorem bAdicVal_not_dvd (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) (hmod : n % b ≠ 0) :
    bAdicVal b n = 0 := by
  unfold bAdicVal
  simp
  intro _ _
  exact hmod

/--
  **bAdicVal recursive step**: for b ≥ 2, n > 0, b | n,
  bAdicVal b n = 1 + bAdicVal b (n / b).
-/
theorem bAdicVal_step (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) (hmod : n % b = 0) :
    bAdicVal b n = 1 + bAdicVal b (n / b) := by
  conv_lhs => unfold bAdicVal
  simp [hb, hn, hmod]

/--
  **bAdicVal of b·n**: bAdicVal b (b·n) = bAdicVal b n + 1 for b ≥ 2, n > 0.

  Direct consequence of bAdicVal_step with substitution n → b·n.
-/
theorem bAdicVal_b_mul (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) :
    bAdicVal b (b * n) = bAdicVal b n + 1 := by
  have hbn_pos : 0 < b * n := Nat.mul_pos (by omega) hn
  have hmod : (b * n) % b = 0 := Nat.mul_mod_right b n
  rw [bAdicVal_step b (b * n) hb hbn_pos hmod]
  have hdiv : (b * n) / b = n := by
    rw [Nat.mul_div_cancel_left]; omega
  rw [hdiv]; omega

/--
  **bAdicVal of b^k**: bAdicVal b (b^k) = k for b ≥ 2.

  Proof by induction on k using bAdicVal_b_mul.
-/
theorem bAdicVal_b_pow (b k : ℕ) (hb : 2 ≤ b) :
    bAdicVal b (b ^ k) = k := by
  induction k with
  | zero =>
    -- b^0 = 1. bAdicVal b 1 = 0.
    simp
    apply bAdicVal_not_dvd b 1 hb (by omega)
    simp; omega
  | succ k IH =>
    -- b^(k+1) = b · b^k.
    have hbk_pos : 0 < b ^ k := by positivity
    have : b ^ (k + 1) = b * b ^ k := by rw [pow_succ]; ring
    rw [this, bAdicVal_b_mul b _ hb hbk_pos, IH]

/--
  **bAdicVal at 1**: bAdicVal b 1 = 0 for b ≥ 2 (since 1 % b = 1 ≠ 0).
-/
@[simp]
theorem bAdicVal_one (b : ℕ) (hb : 2 ≤ b) : bAdicVal b 1 = 0 := by
  apply bAdicVal_not_dvd b 1 hb (by omega)
  simp; omega

/--
  **bAdicVal at b**: bAdicVal b b = 1 for b ≥ 2.
-/
@[simp]
theorem bAdicVal_b_value (b : ℕ) (hb : 2 ≤ b) : bAdicVal b b = 1 := by
  have := bAdicVal_b_pow b 1 hb
  simpa using this

/--
  **bAdicVal divisibility**: if bAdicVal b n ≥ j, then b^j | n (for b ≥ 2, n > 0).

  Proof by induction on j.
-/
theorem b_pow_dvd_of_bAdicVal_ge
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (hn : 0 < n) (j : ℕ)
    (hval : j ≤ bAdicVal b n) : b ^ j ∣ n := by
  induction j generalizing n with
  | zero => simp
  | succ j IH =>
    have hmod : n % b = 0 := by
      by_contra hmod
      have h0 : bAdicVal b n = 0 := bAdicVal_not_dvd b n hb hn hmod
      omega
    have hdvd_b : b ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hstep := bAdicVal_step b n hb hn hmod
    have hval_div : j ≤ bAdicVal b (n / b) := by omega
    have hnb_pos : 0 < n / b :=
      Nat.div_pos (Nat.le_of_dvd hn hdvd_b) (by omega)
    have IH' : b ^ j ∣ n / b := IH (n / b) hnb_pos hval_div
    -- b^(j+1) ∣ n: combine b ∣ n with b^j ∣ n/b.
    rw [pow_succ]
    obtain ⟨c, hc⟩ := IH'
    -- n / b = b^j * c, so n = b * (b^j * c) = b^j * b * c = b^j * (b * c).
    -- Actually goal is b ^ j * b ∣ n. n = b * (n/b) = b * b^j * c.
    have hn_eq : n = b * (b ^ j * c) := by
      rw [← hc]
      exact (Nat.div_mul_cancel hdvd_b).symm.trans (by ring)
    rw [hn_eq]
    -- Goal: b ^ j * b ∣ b * (b ^ j * c). Both have b · b^j · c.
    exact ⟨c, by ring⟩

/--
  **bAdicVal bounded by valuation level**: for n ∈ [1, b^k - 1], bAdicVal b n < k.

  Proof: by contradiction. If bAdicVal b n ≥ k, then b^k ∣ n, so n ≥ b^k > b^k - 1,
  contradicting n ≤ b^k - 1.
-/
theorem bAdicVal_lt_pow (b : ℕ) (hb : 2 ≤ b) (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ b ^ k - 1) :
    bAdicVal b n < k := by
  by_contra hval
  push_neg at hval
  -- hval : k ≤ bAdicVal b n. So b^k ∣ n.
  have hdvd : b ^ k ∣ n := b_pow_dvd_of_bAdicVal_ge b hb n hn k hval
  have hge : b ^ k ≤ n := Nat.le_of_dvd hn hdvd
  -- n ≤ b^k - 1 < b^k. Contradiction with b^k ≤ n.
  have hpos : 0 < b ^ k := by positivity
  omega

/-! ### Valuation coloring (kernel-pure lower bound foundation).

  The VALUATION COLORING chi_v(n) := bAdicVal b n mod k is the canonical
  mono-free k-coloring of [1, b^k - 1] for bAdicEquation b. It proves
  R_k(b) > b^k - 1, i.e., R_k(b) ≥ b^k — the lower bound direction of
  the threshold conjecture.
-/

/--
  **Valuation coloring**: chi_v(n) := (bAdicVal b n) mod k.
  Standard mod-k reduction of the b-adic valuation.
-/
def valuationColoring (b k n : ℕ) : ℕ := (bAdicVal b n) % k

/--
  **Valuation coloring is a k-coloring** of any range, for k ≥ 1.
  Direct from Nat.mod_lt.
-/
theorem valuationColoring_lt (b k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    valuationColoring b k n < k := by
  unfold valuationColoring
  exact Nat.mod_lt _ hk

/--
  **Valuation coloring is an IsKColoring** of [1, n] for any n.
  Direct from valuationColoring_lt.
-/
theorem isKColoring_valuationColoring (b k n : ℕ) (hk : 1 ≤ k) :
    IsKColoring n k (valuationColoring b k) := by
  intro i _ _
  exact valuationColoring_lt b k hk i

/--
  **Valuation coloring agrees with bAdicVal** on the range [1, b^k - 1].

  For n ∈ [1, b^k - 1], bAdicVal b n < k (from bAdicVal_lt_pow), so
  (bAdicVal b n) mod k = bAdicVal b n.
-/
theorem valuationColoring_eq_bAdicVal (b k n : ℕ) (hb : 2 ≤ b)
    (hn : 1 ≤ n) (hnk : n ≤ b ^ k - 1) :
    valuationColoring b k n = bAdicVal b n := by
  unfold valuationColoring
  exact Nat.mod_eq_of_lt (bAdicVal_lt_pow b hb k n hn hnk)

/-! ### Valuation coloring MONO-FREENESS (deep mathematical content).

  The valuation coloring χ_v is mono-free for bAdicEquation b on [1, b^k - 1].
  This is the KEY MATHEMATICAL CONTENT establishing the lower bound R_k(b) ≥ b^k.

  Proof outline: for a Rado triple (x, y, z) with x + b·y = b·z:
  - x = b·(z - y), so bAdicVal_b(x) = bAdicVal_b(z - y) + 1.
  - If chi_v mono, then bAdicVal_b(x) ≡ bAdicVal_b(y) ≡ bAdicVal_b(z) (mod k).
  - On [1, b^k - 1], all valuations are < k, so ≡ mod k means =.
  - bAdicVal_b(y) = bAdicVal_b(z) implies b^v ∣ both y and z (v = common val),
    hence b^v ∣ (z - y), so bAdicVal_b(z - y) ≥ v.
  - Then bAdicVal_b(x) = bAdicVal_b(z - y) + 1 ≥ v + 1 > v = bAdicVal_b(y).
  - But bAdicVal_b(x) = bAdicVal_b(y) by mono. Contradiction.
-/

/--
  **bAdicVal lower bound from divisibility**: if b^v ∣ n (with n > 0, b ≥ 2),
  then bAdicVal b n ≥ v.

  Converse of `b_pow_dvd_of_bAdicVal_ge`.
-/
theorem bAdicVal_ge_of_b_pow_dvd
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (hn : 0 < n) (v : ℕ)
    (hdvd : b ^ v ∣ n) : v ≤ bAdicVal b n := by
  induction v generalizing n with
  | zero => omega
  | succ v IH =>
    -- b^(v+1) ∣ n means b · b^v ∣ n. Specifically b ∣ n.
    have hb_dvd : b ∣ n := by
      have : b ∣ b ^ (v + 1) := dvd_pow_self b (by omega)
      exact this.trans hdvd
    have hmod : n % b = 0 := Nat.mod_eq_zero_of_dvd hb_dvd
    have hstep := bAdicVal_step b n hb hn hmod
    -- n / b has b^v ∣ (n / b) since n = b · (n/b) and b^(v+1) = b · b^v ∣ b·(n/b) = n.
    have hnb_pos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hb_dvd) (by omega)
    have hdvd_div : b ^ v ∣ n / b := by
      obtain ⟨c, hc⟩ := hdvd
      -- n = b^(v+1) * c = b * b^v * c. So n / b = b^v * c.
      have hn_eq : n = b * (b ^ v * c) := by rw [hc]; ring
      have : n / b = b ^ v * c := by
        rw [hn_eq, Nat.mul_div_cancel_left _ (by omega : 0 < b)]
      rw [this]
      exact ⟨c, rfl⟩
    have := IH (n / b) hnb_pos hdvd_div
    omega

/--
  **bAdicVal of difference**: if b^v ∣ y AND b^v ∣ z AND z ≥ y AND z - y > 0,
  then bAdicVal b (z - y) ≥ v (for b ≥ 2).

  Direct consequence: b^v divides z - y, then apply `bAdicVal_ge_of_b_pow_dvd`.
-/
theorem bAdicVal_sub_ge
    (b : ℕ) (hb : 2 ≤ b) (y z v : ℕ)
    (hyz : y ≤ z) (hzy_pos : 0 < z - y)
    (hy_dvd : b ^ v ∣ y) (hz_dvd : b ^ v ∣ z) :
    v ≤ bAdicVal b (z - y) := by
  -- z = y + (z - y), so z - y = z - y. b^v ∣ y, b^v ∣ z ⇒ b^v ∣ (z - y).
  have hzmy_dvd : b ^ v ∣ z - y := by
    obtain ⟨q_y, hy_eq⟩ := hy_dvd
    obtain ⟨q_z, hz_eq⟩ := hz_dvd
    refine ⟨q_z - q_y, ?_⟩
    -- z - y = b^v · q_z - b^v · q_y = b^v · (q_z - q_y).
    rw [hz_eq, hy_eq, ← Nat.mul_sub]
  exact bAdicVal_ge_of_b_pow_dvd b hb (z - y) hzy_pos v hzmy_dvd

/--
  **VALUATION COLORING IS MONO-FREE** for bAdicEquation b on [1, b^k - 1].

  This is the KEY MATHEMATICAL THEOREM giving the kernel-pure LOWER BOUND
  R_k(b) ≥ b^k. Direct algebraic valuation argument:

  For any positive Rado solution (x, y, z) ∈ [1, b^k - 1]^3 with chi_v mono:
  - bAdicVal_b(y) = bAdicVal_b(z) = v (forced: both < k and ≡ mod k).
  - x = b·(z - y), so bAdicVal_b(x) = bAdicVal_b(z - y) + 1.
  - bAdicVal_b(z - y) ≥ v (from common divisibility).
  - bAdicVal_b(x) ≥ v + 1, but also bAdicVal_b(x) = v. Contradiction.

  KERNEL-PURE proof, no project bridge.
-/
theorem valuationColoring_mono_free (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ¬ HasMonoSolution (bAdicEquation b) (b ^ k - 1) (valuationColoring b k) := by
  intro ⟨f, hbound, hpos, hcolor⟩
  obtain ⟨hfpos, heval⟩ := hpos
  -- f 0, f 1, f 2 ∈ [1, b^k - 1].
  have hnv : (bAdicEquation b).numVars = 3 := bAdicEquation_numVars b
  have hf0_pos : 0 < f 0 := hfpos 0 (by rw [hnv]; omega)
  have hf1_pos : 0 < f 1 := hfpos 1 (by rw [hnv]; omega)
  have hf2_pos : 0 < f 2 := hfpos 2 (by rw [hnv]; omega)
  have hf0_le : f 0 ≤ b ^ k - 1 := hbound 0 (by rw [hnv]; omega)
  have hf1_le : f 1 ≤ b ^ k - 1 := hbound 1 (by rw [hnv]; omega)
  have hf2_le : f 2 ≤ b ^ k - 1 := hbound 2 (by rw [hnv]; omega)
  -- eval: f 0 + b·f 1 = b·f 2 in ℤ.
  have hZeq : (f 0 : ℤ) + (b : ℤ) * (f 1 : ℤ) = (b : ℤ) * (f 2 : ℤ) := by
    have h := heval
    rw [eval_bAdicEquation] at h
    linarith
  -- Cast to ℕ.
  have hNeq : f 0 + b * f 1 = b * f 2 := by exact_mod_cast hZeq
  -- f 2 > f 1 (else f 0 ≤ 0).
  have hf21 : f 1 < f 2 := by
    by_contra hge
    push_neg at hge
    have hbmul : b * f 2 ≤ b * f 1 := Nat.mul_le_mul_left b hge
    omega
  -- f 0 = b · (f 2 - f 1).
  have hfdiff_pos : 0 < f 2 - f 1 := by omega
  have hf0_eq : f 0 = b * (f 2 - f 1) := by
    have hbprod : b * f 1 ≤ b * f 2 := Nat.mul_le_mul_left b (le_of_lt hf21)
    have : f 0 = b * f 2 - b * f 1 := by omega
    rw [this, ← Nat.mul_sub]
  -- chi_v mono: val(f 0) = val(f 1) = val(f 2) (mod k).
  -- All values < k from bAdicVal_lt_pow.
  have hval0_lt : bAdicVal b (f 0) < k := bAdicVal_lt_pow b hb k (f 0) hf0_pos hf0_le
  have hval1_lt : bAdicVal b (f 1) < k := bAdicVal_lt_pow b hb k (f 1) hf1_pos hf1_le
  have hval2_lt : bAdicVal b (f 2) < k := bAdicVal_lt_pow b hb k (f 2) hf2_pos hf2_le
  -- chi_v values equal in this range = bAdicVal values equal.
  have hchi01 : valuationColoring b k (f 0) = valuationColoring b k (f 1) :=
    hcolor 0 1 (by rw [hnv]; omega) (by rw [hnv]; omega)
  have hchi12 : valuationColoring b k (f 1) = valuationColoring b k (f 2) :=
    hcolor 1 2 (by rw [hnv]; omega) (by rw [hnv]; omega)
  -- On the valid range, valuationColoring = bAdicVal.
  have hv0 : valuationColoring b k (f 0) = bAdicVal b (f 0) :=
    valuationColoring_eq_bAdicVal b k (f 0) hb hf0_pos hf0_le
  have hv1 : valuationColoring b k (f 1) = bAdicVal b (f 1) :=
    valuationColoring_eq_bAdicVal b k (f 1) hb hf1_pos hf1_le
  have hv2 : valuationColoring b k (f 2) = bAdicVal b (f 2) :=
    valuationColoring_eq_bAdicVal b k (f 2) hb hf2_pos hf2_le
  have hval_01 : bAdicVal b (f 0) = bAdicVal b (f 1) := by rw [← hv0, ← hv1]; exact hchi01
  have hval_12 : bAdicVal b (f 1) = bAdicVal b (f 2) := by rw [← hv1, ← hv2]; exact hchi12
  -- Let v = bAdicVal b (f 1) = bAdicVal b (f 2). b^v ∣ f 1, b^v ∣ f 2.
  set v := bAdicVal b (f 1)
  have hdvd1 : b ^ v ∣ f 1 := b_pow_dvd_of_bAdicVal_ge b hb (f 1) hf1_pos v (le_refl v)
  have hdvd2 : b ^ v ∣ f 2 := by
    have hv12 : v = bAdicVal b (f 2) := hval_12
    rw [hv12]
    exact b_pow_dvd_of_bAdicVal_ge b hb (f 2) hf2_pos (bAdicVal b (f 2)) (le_refl _)
  -- bAdicVal b (f 2 - f 1) ≥ v.
  have hval_sub : v ≤ bAdicVal b (f 2 - f 1) :=
    bAdicVal_sub_ge b hb (f 1) (f 2) v (le_of_lt hf21) hfdiff_pos hdvd1 hdvd2
  -- bAdicVal b (f 0) = bAdicVal b (b · (f 2 - f 1)) = bAdicVal b (f 2 - f 1) + 1.
  have hval_f0 : bAdicVal b (f 0) = bAdicVal b (f 2 - f 1) + 1 := by
    rw [hf0_eq]
    exact bAdicVal_b_mul b (f 2 - f 1) hb hfdiff_pos
  -- bAdicVal b (f 0) ≥ v + 1.
  have hval_f0_ge : v + 1 ≤ bAdicVal b (f 0) := by
    rw [hval_f0]; omega
  -- But bAdicVal b (f 0) = bAdicVal b (f 1) = v (from mono).
  have hval_f0_eq_v : bAdicVal b (f 0) = v := hval_01
  -- Contradiction: v + 1 ≤ v.
  omega

/--
  **KERNEL-PURE LOWER BOUND R_k(b) ≥ b^k from scratch in General/**.

  ¬ IsKPartitionRegularAt (bAdicEquation b) k (b^k - 1)

  For b ≥ 2, k ≥ 1, the b-adic equation is NOT k-partition-regular at level
  b^k - 1. Equivalently, R_k(bAdicEquation b) ≥ b^k.

  Proof: the valuation coloring chi_v provides an explicit witness. It is a
  k-coloring (by isKColoring_valuationColoring) and mono-free (by
  valuationColoring_mono_free).

  THIS ELIMINATES THE PROJECT BRIDGE for the LOWER BOUND DIRECTION ENTIRELY.

  Previously the lower bound was bridged via
  not_isKPartitionRegularAt_of_radoNumberAtLeast + project's thm_lower
  (which itself depended on project's bAdicVal + analytic
  bAdicVal_avoidsMono). Now derived in pure General/ form.

  KERNEL-PURE end-to-end.
-/
theorem not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one_from_scratch
    (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ¬ IsKPartitionRegularAt (bAdicEquation b) k (b ^ k - 1) := by
  intro hPR
  -- Apply to the valuation coloring.
  have hχk : IsKColoring (b ^ k - 1) k (valuationColoring b k) :=
    isKColoring_valuationColoring b k (b ^ k - 1) hk
  have hMono : HasMonoSolution (bAdicEquation b) (b ^ k - 1) (valuationColoring b k) :=
    hPR _ hχk
  exact valuationColoring_mono_free b k hb hk hMono

end RadoNumbers.General
