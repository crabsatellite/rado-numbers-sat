/-
  RadoNumbers/K3B3.lean

  Lemma `lem:k3b3pair` and Theorem `thm:k3b3` ($R_3(3) = 27$).
  Companion to Li 2026 "On Rado Numbers for $x + by = bz$".

  The upper bound is hybrid analytic-SAT: the paper's Lemma
  `lem:k3b3pair` (forcing $\chi(3) = \chi(6)$ in any valid
  3-coloring of $\{1, …, 18\}$) is analytic for Steps 1–2 and
  uses SAT for Step 3. The full upper bound $R_3(3) \le 27$ is
  established by SAT (Table `table:sat`, row $b = 3, k = 3$,
  CaDiCaL 1.5.3 in $< 0.01$s).

  Encoding (Round 18 refactor):

  * `lem_compress3_b3` — Cat 2 SAT-verified atom: the compression
    hypothesis for $b = 3, k = 3$ (multiples sub-coloring omits a
    color). STRICTLY SMALLER than the former monolithic
    `thm_k3b3_upper_sat`.
  * `thm_k3b3_upper_sat` — now a DERIVED theorem: `cascade_step` at $b = 3, k = 3$ with $R_2(3) \le 9$ (`thm_k2`,
    kernel-pure) and `lem_compress3_b3`.
  * `thm_k3b3` — derived theorem combining `thm_lower` (lower
    bound) with `thm_k3b3_upper_sat` (cascade-derived upper bound).
  * Former `lem_k3b3pair_sat` monolithic axiom REMOVED Round 18
    (Pattern 7 phantom); analytic Steps 1–2 live as theorems in
    `K3General.lean`.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.K2
import RadoNumbers.DPLStructure
import RadoNumbers.K3General
-- : import the General bridge for the kernel-pure `thm_k3b3_kernel_pure`.
-- The Bridge.lean → K3B3.lean cycle was broken in (Bridge no longer imports K3B3).
import RadoNumbers.General.Bridge
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Note on paper Lemma `lem:k3b3pair`.

  Paper's named Lemma `lem:k3b3pair` ($\chi(3) = \chi(6)$ in any
  valid 3-coloring of $\{1, \ldots, 18\}$) was originally encoded
  here as a monolithic Cat 2 SAT-verified axiom `lem_k3b3pair_sat`.
  Rounds 2–3 Lean-derived its analytic Steps 1–2
  (`lem_k3b3pair_step1`, `lem_k3b3pair_step2` in `K3General.lean`).
  Since no Lean theorem consumes the monolithic axiom (Pattern 7
  phantom downstream user), it was REMOVED Round 18.
  The analytic Step-1/2 theorems remain; Step 3 (element 18
  uncolorability) is documented as the remaining gap for a full
  in-Lean derivation of `lem:k3b3pair`. -/

/-! ### Derived theorem `thm:k3b3`.

  ** refactor:** `thm:k3b3` is now KERNEL-PURE.
  It points directly to `RadoNumbers.General.thm_k3b3_kernel_pure`
  (Bridge.lean §40.5), which derives $R_3(3) = 27$ from -
  Branch I-V + Branch I-W closure, using ONLY Lean kernel axioms.

  This eliminates the `lem_compress3_general` SAT axiom from
  `thm_k3b3`'s dependency cone (for the $b = 3$ case).

  Old path (still available as `thm_k3b3_via_compression_axiom` below):
  cascade_step + thm_k2 + `lem_compress3_general` (Cat 2 SAT axiom).
  The general-b path `thm_k3_general` (b ∈ {3..10}) still uses the
  axiom because the cascade infrastructure works for the parameterized
  range — the kernel-pure derivation is currently only b=3 specific.
-/

/--
  **Theorem `thm:k3b3`.** $R_3(3) = 27$. **KERNEL-PURE** since.

  Direct alias to `RadoNumbers.General.thm_k3b3_kernel_pure`, which
  uses Branch I-V (-) + Branch I-W (-) + vacuous
  compression () to derive the result from Lean kernel axioms only.
-/
theorem thm_k3b3 : IsRadoNumber 3 3 27 :=
  RadoNumbers.General.thm_k3b3_kernel_pure

/-- **Theorem `thm:k3b3` upper bound** (kept for naming
    compatibility): $R_3(3) \le 27$, the upper-bound half of
    `thm_k3b3`. **KERNEL-PURE** since. -/
theorem thm_k3b3_upper_sat : RadoNumberAtMost 3 3 27 := thm_k3b3.2

/-- **Legacy proof** of `thm:k3b3` via the axiom-dependent
    `thm_k3_general`. Kept for historical comparison and for
    cross-checking the parameterized $b \in \{3..10\}$ proof path
    against the kernel-pure b=3 derivation. **DEPENDS ON
    `lem_compress3_general` axiom.** -/
theorem thm_k3b3_via_compression_axiom : IsRadoNumber 3 3 27 := by
  have h := thm_k3_general 3 (by norm_num) (by norm_num)
  have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
  rwa [h27] at h

end RadoNumbers
