/-
  RadoNumbers/Basic.lean

  Definitions for the formalization of Li 2026 "On Rado Numbers for
  $x + by = bz$: The $b^k$ Pattern and a Threshold Conjecture".

  Paper objects formalized here:

  * Definition `def:b-adic-valuation` — the b-adic valuation `v_b(n)`
  * Definition `def:rado-number` — the k-color Rado number `R_k(b)` for
    the equation `x + by = bz`, as the pair of bounds
    `RadoLowerThan` (lower-bound predicate) and `RadoUpperThan`
    (upper-bound predicate)
  * Remark `rmk:distance` — distance-rephrasing of a monochromatic
    solution (an unfolded form of `IsRadoTriple`)

  Paper symbol → Lean identifier:

      paper  →  Lean
      ─────────────
      v_b    →  bAdicVal
      χ      →  chi  (or χ kept as Greek; Lean parser accepts)
      C_c    →  ColorClass
      R_k(b) →  RadoNumberAtLeast / RadoNumberAtMost
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Definition `def:b-adic-valuation` — the b-adic valuation. -/

/--
  `bAdicVal b n` is the largest `m ≥ 0` such that `b^m ∣ n`.

  For `b ≥ 2` and `n ≥ 1`, this is the standard b-adic valuation.
  For `n = 0` or `b ≤ 1`, the value is `0` by convention (the paper
  sets `v_b(0) = ∞` but no proof in this formalisation evaluates `v_b`
  at zero, so finiteness is preserved without semantic change).

  Recursive definition: if `b ∣ n`, then `v_b(n) = 1 + v_b(n / b)`;
  otherwise `v_b(n) = 0`.  Termination follows from `n / b < n`
  whenever `b ≥ 2` and `n > 0`.
-/
def bAdicVal (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ 0 < n ∧ n % b = 0 then
    have : n / b < n := Nat.div_lt_self h.2.1 h.1
    1 + bAdicVal b (n / b)
  else 0
  termination_by n

/-! ### Rado triples and colorings. -/

/--
  `IsRadoTriple b x y z` says the triple `(x, y, z)` of positive
  integers satisfies the Rado equation `x + b·y = b·z`.

  Under the substitution `d := z - y`, this reduces to `x = b·d`
  with `d ≥ 1`, i.e., the paper's distance form (Remark
  `rmk:distance`).  We use the additive form here for direct
  alignment with the paper's `x + by = bz` and to keep solver
  computations symbolic.
-/
def IsRadoTriple (b x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x + b * y = b * z

/--
  A `k`-coloring of `{1, …, n}` is a function `χ : ℕ → ℕ` whose values
  on the domain `{1, …, n}` lie in `{0, …, k-1}`.  Values outside the
  domain are unconstrained.
-/
def IsValidColoring (n k : ℕ) (χ : ℕ → ℕ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ n → χ m < k

/--
  A monochromatic solution to `x + b·y = b·z` in `{1, …, n}` under
  coloring `χ`: positive integers `x, y, z ≤ n` forming a Rado triple
  with `χ x = χ y = χ z`.
-/
def HasMonoSolution (b n : ℕ) (χ : ℕ → ℕ) : Prop :=
  ∃ x y z, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ IsRadoTriple b x y z ∧
    χ x = χ y ∧ χ y = χ z

/--
  Coloring `χ` *avoids* a monochromatic solution to `x + b·y = b·z`
  on `{1, …, n}`.  Negation of `HasMonoSolution`.
-/
def AvoidsMonoSolution (b n : ℕ) (χ : ℕ → ℕ) : Prop :=
  ¬ HasMonoSolution b n χ

/-! ### Rado number bounds. -/

/--
  *Lower-bound predicate.*  `RadoNumberAtLeast b k N` says the Rado
  number `R_k(b)` is at least `N`: there exists a valid `k`-coloring
  of `{1, …, N - 1}` avoiding all monochromatic solutions to
  `x + b·y = b·z`.

  Paper: `R_k(b) ≥ N` (Theorem `thm:lower` with `N = b^k`).
-/
def RadoNumberAtLeast (b k N : ℕ) : Prop :=
  ∃ χ : ℕ → ℕ, IsValidColoring (N - 1) k χ ∧
    AvoidsMonoSolution b (N - 1) χ

/--
  *Upper-bound predicate.*  `RadoNumberAtMost b k N` says the Rado
  number `R_k(b)` is at most `N`: every valid `k`-coloring of
  `{1, …, N}` contains a monochromatic solution to `x + b·y = b·z`.

  Paper: `R_k(b) ≤ N` (the upper-bound half of `thm:k2`,
  `thm:k3b3`, `thm:k4b3`, `thm:sat`).
-/
def RadoNumberAtMost (b k N : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring N k χ → HasMonoSolution b N χ

/--
  *Exact-value predicate.*  `IsRadoNumber b k N` says `R_k(b) = N`:
  both lower bound `R_k(b) ≥ N` and upper bound `R_k(b) ≤ N` hold.

  Paper: `R_2(b) = b^2`, `R_3(3) = 27`, `R_4(3) = 81`, etc.
-/
def IsRadoNumber (b k N : ℕ) : Prop :=
  RadoNumberAtLeast b k N ∧ RadoNumberAtMost b k N

/-! ### Color classes and distance avoidance.

  Remark `rmk:distance` of the paper rephrases monochromatic
  solutions in distance form: if `χ(b·d) = c`, then the color class
  `C_c = χ^{-1}(c)` must avoid pairs at distance `d`.  We carry this
  rephrasing as a paper-level definition.
-/

/-- Color class `C_c` of color `c` restricted to `{1, …, n}`. -/
def ColorClass (n : ℕ) (χ : ℕ → ℕ) (c : ℕ) : Set ℕ :=
  { x | 1 ≤ x ∧ x ≤ n ∧ χ x = c }

/-- Color class `C` avoids pairs at distance `d`: no two elements
    of `C` differ by exactly `d`. -/
def AvoidsDistance (C : Set ℕ) (d : ℕ) : Prop :=
  ∀ x y, x ∈ C → y ∈ C → x + d ≠ y ∧ y + d ≠ x

end RadoNumbers
