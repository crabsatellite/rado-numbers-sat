/-
  RadoNumbers/General/ColumnsCondition.lean

  Rado's Columns Condition for a single linear equation
  a_1 x_1 + ... + a_n x_n = 0.

  For a 1×n matrix (single equation), the (full) Columns Condition reduces
  to: there exists a non-empty subset S ⊆ {0, ..., n-1} with ∑_{i ∈ S} a_i = 0.

  This is because in 1D, "ℚ-span" of any non-zero scalar is ℚ; the
  recursive part of Columns Condition (each subsequent group's sum is in
  ℚ-span of prior groups) is automatically satisfied once a non-zero
  earlier group exists.

  Rado's theorem (1933): A linear equation is k-partition-regular for all
  k ≥ 1 IFF it satisfies the Columns Condition.

  For our b-adic equation x + b·y - b·z = 0 (coeffs [1, b, -b]):
  subset {1, -b} indices 1, 2 sums to b - b = 0 (when interpreted as a + (-a)).
  Wait, subset {3, -3} (indices 1, 2) sums to 3 + (-3) = 0. ✓
  So bAdicEquation satisfies Columns Condition for all b ≥ 1.
-/

import RadoNumbers.General.BAdicEquation
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace RadoNumbers.General

/--
  **Zero-sum subset** for a linear equation: a non-empty subset of index
  positions whose coefficients sum to 0.

  This is the FIRST GROUP of Rado's Columns Condition (for the single
  equation case). In 1D, the rest of Columns Condition is automatic.
-/
def HasZeroSumSubset (eq : LinearEquation) : Prop :=
  ∃ S : Finset ℕ,
    S.Nonempty ∧
    (∀ i ∈ S, i < eq.numVars) ∧
    (S.sum fun i => eq.coeffs.getD i 0) = 0

/--
  **Columns Condition (single equation version)**: for a single linear
  equation, the Columns Condition is equivalent to existence of a
  non-empty zero-sum subset of coefficients.

  This definition captures the 1×n matrix specialization of Rado's
  general Columns Condition.
-/
def ColumnsCondition (eq : LinearEquation) : Prop := HasZeroSumSubset eq

/--
  **bAdicEquation satisfies Columns Condition**: the subset {1, 2}
  (indices for coefficients b and -b) sums to b + (-b) = 0.
-/
theorem bAdicEquation_columnsCondition (b : ℕ) :
    ColumnsCondition (bAdicEquation b) := by
  refine ⟨{1, 2}, ⟨1, by decide⟩, ?_, ?_⟩
  · -- ∀ i ∈ {1, 2}, i < numVars = 3.
    intro i hi
    have hnv : (bAdicEquation b).numVars = 3 := by
      unfold bAdicEquation LinearEquation.numVars
      rfl
    rw [hnv]
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · omega
    · rcases Finset.mem_singleton.mp hi' with rfl
      omega
  · -- Sum of coeffs at indices 1 and 2 = b + (-b) = 0.
    rw [show ({1, 2} : Finset ℕ) = insert 1 {2} from rfl,
        Finset.sum_insert (by decide), Finset.sum_singleton]
    -- Goal: (bAdicEquation b).coeffs.getD 1 0 + (bAdicEquation b).coeffs.getD 2 0 = 0.
    show ([(1 : ℤ), (b : ℤ), -(b : ℤ)].getD 1 0) + ([(1 : ℤ), (b : ℤ), -(b : ℤ)].getD 2 0) = 0
    simp [List.getD]

/--
  **radoEq_3 satisfies Columns Condition**: specific case of b = 3.
-/
theorem radoEq_3_columnsCondition : ColumnsCondition radoEq_3 := by
  unfold radoEq_3
  exact bAdicEquation_columnsCondition 3

end RadoNumbers.General
