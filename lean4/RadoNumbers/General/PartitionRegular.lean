/-
  RadoNumbers/General/PartitionRegular.lean

  GENERAL Rado partition regularity infrastructure.

  Long-term Mathlib-style framework for arbitrary linear equations over ℤ,
  not specific to x + by = bz. This file provides basic definitions; full
  Rado theorem proof is multi-year work (user-approved).

  This is the structural backbone for proving R_3(3) ≤ 27 (and general
  R_k(b) = b^k threshold) UNCONDITIONALLY without case enumeration.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace RadoNumbers.General

/--
  **Linear equation over ℤ**: list of integer coefficients (a_1, ..., a_n).
  Represents equation a_1 · x_1 + a_2 · x_2 + ... + a_n · x_n = 0.

  Example: Schur's equation x + y - z = 0 has coefficients [1, 1, -1].
  Example: Our equation x + 3y - 3z = 0 has coefficients [1, 3, -3].
-/
structure LinearEquation where
  coeffs : List ℤ
  nontrivial : coeffs ≠ []

namespace LinearEquation

/--
  **Number of variables** in the equation.
-/
def numVars (eq : LinearEquation) : ℕ := eq.coeffs.length

/--
  **Evaluation**: given an assignment x : ℕ → ℤ of values,
  compute the LHS of the equation by summing a_i · x_i over indices.
-/
def eval (eq : LinearEquation) (x : ℕ → ℤ) : ℤ :=
  (eq.coeffs.zipIdx.foldl (fun acc (c, i) => acc + c * x i) (0 : ℤ))

/--
  **Solution predicate**: an assignment is a solution iff `eval = 0`.
-/
def IsSolution (eq : LinearEquation) (x : ℕ → ℤ) : Prop := eq.eval x = 0

/--
  **Positive solution**: all variable values are positive integers (≥ 1)
  AND values satisfy the equation.
-/
def IsPositiveSolution (eq : LinearEquation) (x : ℕ → ℕ) : Prop :=
  (∀ i, i < eq.numVars → 0 < x i) ∧
  eq.eval (fun i => (x i : ℤ)) = 0

/-! ### Eval linearity (foundational structural lemma).

  The LinearEquation eval is LINEAR in the assignment:
    eval (c · x) = c · eval x

  This expresses the HOMOGENEITY of linear equations Σ aᵢ xᵢ = 0 and is
  the foundation for scaling-based arguments (multiples sub-coloring,
  cascade machinery, etc.) at full Mathlib-style generality (any
  LinearEquation, not just bAdicEquation b).
-/

/--
  **Helper**: foldl with scaled accumulator equals scaled foldl.

  For any list L of (coeff, index) pairs and any c : ℤ, using the
  destructuring-match lambda form (matching the actual `eval` definition).
  Proof by induction on L, generalizing acc.
-/
private theorem foldl_eval_const_mul (x : ℕ → ℤ) (c : ℤ) :
    ∀ (L : List (ℤ × ℕ)) (acc : ℤ),
      L.foldl (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * (c * x i)) (c * acc) =
      c * L.foldl (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                    match x_1 with | (q, i) => a + q * x i) acc := by
  intro L
  induction L with
  | nil => intro acc; simp [List.foldl]
  | cons p tail IH =>
    intro acc
    obtain ⟨q, i⟩ := p
    simp only [List.foldl]
    have hstep : c * acc + q * (c * x i) = c * (acc + q * x i) := by ring
    rw [hstep]
    exact IH (acc + q * x i)

/--
  **eval is linear (scalar multiplication)**: for any LinearEquation `eq`,
  any scalar `c : ℤ`, and any assignment `x : ℕ → ℤ`:
    eq.eval (fun i => c * x i) = c * eq.eval x

  Foundational lemma for the homogeneity of linear equations.

  CONSEQUENCE: if x is a solution (eval x = 0), then c·x is also a solution
  (eval (c·x) = c·0 = 0). This is the algebraic backbone of all
  scaling-based arguments — multiples sub-coloring, cascade machinery,
  etc. — at full Mathlib-style generality (any LinearEquation, not just
  bAdicEquation b).
-/
theorem eval_const_mul (eq : LinearEquation) (c : ℤ) (x : ℕ → ℤ) :
    eq.eval (fun i => c * x i) = c * eq.eval x := by
  show eq.coeffs.zipIdx.foldl
        (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
          match x_1 with | (q, i) => a + q * ((fun i => c * x i) i)) 0 =
       c * eq.coeffs.zipIdx.foldl
        (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
          match x_1 with | (q, i) => a + q * x i) 0
  -- Beta-reduce the inner application (fun i => c * x i) i = c * x i.
  have hrhs : (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * ((fun i => c * x i) i))
            = (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * (c * x i)) := by
    funext a x_1; rcases x_1 with ⟨q, i⟩; rfl
  rw [hrhs]
  have h0 : (0 : ℤ) = c * 0 := by ring
  conv_lhs => rw [h0]
  exact foldl_eval_const_mul x c eq.coeffs.zipIdx 0

/--
  **Solutions scale**: scaling a solution by c yields another solution.
  Direct corollary of `eval_const_mul`.
-/
theorem isSolution_const_mul (eq : LinearEquation) (c : ℤ) (x : ℕ → ℤ)
    (h : eq.IsSolution x) : eq.IsSolution (fun i => c * x i) := by
  show eq.eval (fun i => c * x i) = 0
  rw [eval_const_mul]
  have : eq.eval x = 0 := h
  rw [this]
  ring

/--
  **Positive solution scales** (ℕ version): scaling a positive solution by
  c ≥ 1 yields another positive solution. Combines `eval_const_mul` (in ℤ)
  with positivity preservation under multiplication.
-/
theorem isPositiveSolution_const_mul (eq : LinearEquation) {c : ℕ} (hc : 1 ≤ c)
    (x : ℕ → ℕ) (h : eq.IsPositiveSolution x) :
    eq.IsPositiveSolution (fun i => c * x i) := by
  obtain ⟨hpos, heval⟩ := h
  refine ⟨?_, ?_⟩
  · intro i hi
    exact Nat.mul_pos hc (hpos i hi)
  · -- eval ((c · x) : ℕ → ℤ) = c · eval (x : ℕ → ℤ) = c · 0 = 0.
    have h1 : (fun i => ((c * x i : ℕ) : ℤ)) = (fun i => (c : ℤ) * ((x i : ℕ) : ℤ)) := by
      funext i; push_cast; ring
    rw [h1, eval_const_mul, heval]
    ring

/-! ### Eval additivity (the OTHER linearity property).

  Combined with `eval_const_mul`, gives full ℤ-linearity of eval.
  Useful for combining solutions: if x and y are solutions, so is x + y.
-/

/--
  **Helper**: foldl additivity for two assignments.

  foldl (fun a (q, i) => a + q * (x i + y i)) (acc_x + acc_y) L
    = foldl (fun a (q, i) => a + q * x i) acc_x L + foldl (fun a (q, i) => a + q * y i) acc_y L
-/
private theorem foldl_eval_add (x y : ℕ → ℤ) :
    ∀ (L : List (ℤ × ℕ)) (acc_x acc_y : ℤ),
      L.foldl (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * (x i + y i)) (acc_x + acc_y) =
      L.foldl (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * x i) acc_x +
      L.foldl (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * y i) acc_y := by
  intro L
  induction L with
  | nil => intro acc_x acc_y; simp [List.foldl]
  | cons p tail IH =>
    intro acc_x acc_y
    obtain ⟨q, i⟩ := p
    simp only [List.foldl]
    have hstep : (acc_x + acc_y) + q * (x i + y i)
               = (acc_x + q * x i) + (acc_y + q * y i) := by ring
    rw [hstep]
    exact IH (acc_x + q * x i) (acc_y + q * y i)

/--
  **eval is additive**: for any LinearEquation `eq` and any two assignments
  `x, y : ℕ → ℤ`:
    eq.eval (fun i => x i + y i) = eq.eval x + eq.eval y
-/
theorem eval_add (eq : LinearEquation) (x y : ℕ → ℤ) :
    eq.eval (fun i => x i + y i) = eq.eval x + eq.eval y := by
  show eq.coeffs.zipIdx.foldl
        (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
          match x_1 with | (q, i) => a + q * ((fun i => x i + y i) i)) 0 =
       eq.coeffs.zipIdx.foldl
        (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
          match x_1 with | (q, i) => a + q * x i) 0 +
       eq.coeffs.zipIdx.foldl
        (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
          match x_1 with | (q, i) => a + q * y i) 0
  -- Beta-reduce.
  have hrhs : (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * ((fun i => x i + y i) i))
            = (fun (a : ℤ) (x_1 : ℤ × ℕ) =>
                match x_1 with | (q, i) => a + q * (x i + y i)) := by
    funext a x_1; rcases x_1 with ⟨q, i⟩; rfl
  rw [hrhs]
  have h0 : (0 : ℤ) = 0 + 0 := by ring
  conv_lhs => rw [h0]
  exact foldl_eval_add x y eq.coeffs.zipIdx 0 0

/--
  **Solutions form a group under addition**: if x and y are solutions
  (in ℤ), so is x + y.
-/
theorem isSolution_add (eq : LinearEquation) (x y : ℕ → ℤ)
    (hx : eq.IsSolution x) (hy : eq.IsSolution y) :
    eq.IsSolution (fun i => x i + y i) := by
  show eq.eval (fun i => x i + y i) = 0
  rw [eval_add]
  show eq.eval x + eq.eval y = 0
  have hxz : eq.eval x = 0 := hx
  have hyz : eq.eval y = 0 := hy
  rw [hxz, hyz]
  ring

end LinearEquation

/--
  **k-coloring of [1, n]**: function χ : ℕ → ℕ with χ(i) < k for i ∈ [1, n].
-/
def IsKColoring (n k : ℕ) (χ : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → χ i < k

/--
  **Mono solution**: a positive solution of `eq` where all variable values
  have the same color under χ.
-/
def HasMonoSolution (eq : LinearEquation) (n : ℕ) (χ : ℕ → ℕ) : Prop :=
  ∃ x : ℕ → ℕ,
    (∀ i, i < eq.numVars → x i ≤ n) ∧
    eq.IsPositiveSolution x ∧
    (∀ i j, i < eq.numVars → j < eq.numVars → χ (x i) = χ (x j))

/--
  **k-Partition regular at bound N**: every k-coloring of [1, N] has a
  mono solution. This is a quantitative bound; partition regularity is
  the existential version (some such N exists).
-/
def IsKPartitionRegularAt (eq : LinearEquation) (k N : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsKColoring N k χ → HasMonoSolution eq N χ

/--
  **k-Partition regular**: there exists some N such that every k-coloring
  of [1, N] has a mono solution.
-/
def IsKPartitionRegular (eq : LinearEquation) (k : ℕ) : Prop :=
  ∃ N, IsKPartitionRegularAt eq k N

/--
  **N is the (k-)Rado number of equation `eq`**: equation is k-partition-regular
  at N AND not k-partition-regular at any smaller M.

  Equivalently, R_k(eq) = N exactly.
-/
def IsRadoNumber (eq : LinearEquation) (k N : ℕ) : Prop :=
  IsKPartitionRegularAt eq k N ∧ ∀ M, M < N → ¬ IsKPartitionRegularAt eq k M

/--
  **Uniqueness of Rado number**: at most one N satisfies `IsRadoNumber eq k`.

  Proof: if both N1, N2 are Rado numbers, suppose N1 < N2. Then by second
  clause of IsRadoNumber for N2 applied to N1, ¬ IsKPartitionRegularAt eq k N1.
  But first clause of IsRadoNumber for N1 says IsKPartitionRegularAt eq k N1.
  Contradiction. By symmetry, N1 = N2.
-/
theorem isRadoNumber_unique (eq : LinearEquation) (k N1 N2 : ℕ)
    (h1 : IsRadoNumber eq k N1) (h2 : IsRadoNumber eq k N2) : N1 = N2 := by
  obtain ⟨hPR1, hMin1⟩ := h1
  obtain ⟨hPR2, hMin2⟩ := h2
  by_contra hne
  rcases Nat.lt_or_ge N1 N2 with h | h
  · exact hMin2 N1 h hPR1
  · have h' : N2 < N1 := Nat.lt_of_le_of_ne h (Ne.symm hne)
    exact hMin1 N2 h' hPR2

end RadoNumbers.General
