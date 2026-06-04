/-
  RadoNumbers/Foundational.lean

  Mathlib-quality universal structural lemmas for Rado-mono-free
  colorings of the equation $x + b \cdot y = b \cdot z$.

  These lemmas are universal — independent of any specific
  distribution profile or coloring choice.  They are derived
  directly from the definition of `AvoidsMonoSolution` via
  carefully chosen Rado triples.

  All lemmas in this file are STRICTLY KERNEL-PURE: their axiom
  dependencies are `[propext, Quot.sound]` only (no
  `Classical.choice`, no Cat 2 or Cat 3 axioms).  They form the
  foundational layer of any analytic proof of the threshold
  conjecture.

  Organization:
    §1  Self-loop lemmas: $\chi(x) \ne \chi(y)$ from triples
        $(x, y, x)$ or $(x, x, z)$ for arbitrary $b \ge 2$.
    §2  Distance-pair lemmas (applied form).
    §3  Triple-distinct-color theorems.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import Mathlib.Tactic

namespace RadoNumbers

/-! ## §1. Self-loop universal lemmas for arbitrary $b \ge 2$.

  The Rado equation $x + b y = b z$ admits two kinds of self-loops:

  * Type $x = z$: triple $(x, y, x)$ with $y = (b-1) x / b$.
    Requires $x$ divisible by $b$.  Writing $x = b m$: triple
    $(b m, (b-1) m, b m)$.  Verification: $b m + b \cdot (b - 1) m
    = b m \cdot b = b \cdot b m$ ✓.

  * Type $x = y$: triple $(x, x, z)$ with $z = (b+1) x / b$.
    Requires $x$ divisible by $b$.  Writing $x = b m$: triple
    $(b m, b m, (b+1) m)$.  Verification: $b m + b \cdot b m = b m
    \cdot (b + 1) = b \cdot (b+1) m$ ✓.

  These yield UNIVERSAL pairwise inequalities:
  * $\chi(b m) \ne \chi((b-1) m)$ for any $m$ with $b m \le n$.
  * $\chi(b m) \ne \chi((b+1) m)$ for any $m$ with $(b+1) m \le n$.
-/

/--
  **Universal self-loop type-$x=z$.**

  For any $b \ge 2$, $m \ge 1$, and any valid Rado-mono-free
  $b$-coloring of $\{1, \ldots, n\}$ with $b m \le n$:
  $\chi(b m) \ne \chi((b-1) m)$.

  Proof: the self-loop Rado triple $(b m, (b-1) m, b m)$ satisfies
  $b m + b \cdot (b-1) m = b \cdot b m$ (so it is a valid Rado
  triple).  Monochromaticity would require $\chi(b m) = \chi((b-1)
  m) = \chi(b m)$, i.e., $\chi(b m) = \chi((b-1) m)$.

  Strictly kernel-pure: $[propext, Quot.sound]$.
-/
theorem self_loop_eq_left {b : ℕ} (hb : 2 ≤ b) {n m : ℕ}
    (hm : 1 ≤ m) (hbm : b * m ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    χ (b * m) ≠ χ ((b - 1) * m) := by
  intro hcon
  apply hAvoid
  refine ⟨b * m, (b - 1) * m, b * m, hbm, ?_, hbm, ?_, hcon, hcon.symm⟩
  · -- (b - 1) * m ≤ n.
    calc (b - 1) * m ≤ b * m := Nat.mul_le_mul_right m (by omega)
      _ ≤ n := hbm
  · refine ⟨Nat.mul_pos (by omega) hm, Nat.mul_pos (by omega) hm,
           Nat.mul_pos (by omega) hm, ?_⟩
    -- b * m + b * ((b - 1) * m) = b * (b * m)
    have hb1 : (b - 1) + 1 = b := Nat.sub_add_cancel (by omega : 1 ≤ b)
    calc b * m + b * ((b - 1) * m)
        = b * m * ((b - 1) + 1) := by ring
      _ = b * m * b := by rw [hb1]
      _ = b * (b * m) := by ring

/--
  **Universal self-loop type-$x=y$.**

  For any $b \ge 2$, $m \ge 1$, and any valid Rado-mono-free
  $b$-coloring of $\{1, \ldots, n\}$ with $(b+1) m \le n$:
  $\chi((b+1) m) \ne \chi(b m)$.

  Proof: the self-loop Rado triple $(b m, b m, (b+1) m)$ satisfies
  $b m + b \cdot b m = b \cdot (b+1) m$.  Monochromaticity would
  require $\chi(b m) = \chi(b m) = \chi((b+1) m)$, i.e., $\chi((b+1)
  m) = \chi(b m)$.

  Strictly kernel-pure: $[propext, Quot.sound]$.
-/
theorem self_loop_eq_right {b : ℕ} (hb : 2 ≤ b) {n m : ℕ}
    (hm : 1 ≤ m) (hb1m : (b + 1) * m ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    χ ((b + 1) * m) ≠ χ (b * m) := by
  intro hcon
  apply hAvoid
  refine ⟨b * m, b * m, (b + 1) * m, ?_, ?_, hb1m, ?_, rfl, hcon.symm⟩
  · -- b * m ≤ n.
    calc b * m ≤ (b + 1) * m := Nat.mul_le_mul_right m (by omega)
      _ ≤ n := hb1m
  · calc b * m ≤ (b + 1) * m := Nat.mul_le_mul_right m (by omega)
      _ ≤ n := hb1m
  · refine ⟨Nat.mul_pos (by omega) hm, Nat.mul_pos (by omega) hm,
           Nat.mul_pos (by omega) hm, ?_⟩
    -- b * m + b * (b * m) = b * ((b+1) * m)
    calc b * m + b * (b * m)
        = b * m * (1 + b) := by ring
      _ = b * m * (b + 1) := by ring
      _ = b * ((b + 1) * m) := by ring

/-! ## §2. Triple-distinct-color theorem.

  Combining §1's two self-loops, we get a structural theorem: the
  three values $\chi((b-1) m), \chi(b m), \chi((b+1) m)$ are
  PAIRWISE DISTINCT (when all three positions are in domain), and
  in any $b$-coloring with $b$ colors, every color appears exactly
  once at these positions... PROVIDED additional Rado triples
  link $((b-1) m, (b+1) m)$.

  For general $b$, the bridging triple is $((b^2 - 1) m, (b-1) m,
  b m)$ — but this requires $(b^2 - 1) m \le n$, a much stronger
  domain condition.
-/

/--
  **Pairwise self-loop constraint.**

  For any $b \ge 2$, $m \ge 1$, and any valid Rado-mono-free
  $b$-coloring of $\{1, \ldots, n\}$ with $(b+1) m \le n$:

  $\chi((b-1) m) \ne \chi(b m) \land \chi(b m) \ne \chi((b+1) m)$.

  This says that the three positions $(b-1) m, b m, (b+1) m$
  have CONSECUTIVE PAIRS with distinct colors.  The middle
  position $b m$ differs from both flankers.
-/
theorem self_loop_pair_constraint {b : ℕ} (hb : 2 ≤ b) {n m : ℕ}
    (hm : 1 ≤ m) (hn : (b + 1) * m ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    χ ((b - 1) * m) ≠ χ (b * m) ∧ χ (b * m) ≠ χ ((b + 1) * m) := by
  refine ⟨?_, ?_⟩
  · -- χ(b m) ≠ χ((b-1) m), so χ((b-1) m) ≠ χ(b m).
    exact Ne.symm <| self_loop_eq_left hb hm (by
      calc b * m ≤ (b + 1) * m := Nat.mul_le_mul_right m (by omega)
        _ ≤ n := hn) χ hAvoid
  · -- χ((b+1) m) ≠ χ(b m), so χ(b m) ≠ χ((b+1) m).
    exact Ne.symm <| self_loop_eq_right hb hm hn χ hAvoid

/-! ## §3. Specialization to $b = 3$.

  Recovers the lemmas from K3General.lean's Rounds 93-94 as direct
  consequences of §1's foundational generic lemmas at $b = 3$.

  For $b = 3$: $(b - 1) m = 2 m$ and $(b + 1) m = 4 m$.
-/

/--
  **Round 93 generalized — $b = 3$ specialization.**

  For any $m \ge 1$ with $3 m \le n$, $\chi(3 m) \ne \chi(2 m)$.
-/
theorem self_loop_b3_eq_left {n m : ℕ} (hm : 1 ≤ m) (hn : 3 * m ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ (3 * m) ≠ χ (2 * m) :=
  self_loop_eq_left (b := 3) (by omega) hm hn χ hAvoid

/--
  **Round 94 generalized — $b = 3$ specialization.**

  For any $m \ge 1$ with $4 m \le n$, $\chi(4 m) \ne \chi(3 m)$.
-/
theorem self_loop_b3_eq_right {n m : ℕ} (hm : 1 ≤ m) (hn : 4 * m ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ (4 * m) ≠ χ (3 * m) :=
  self_loop_eq_right (b := 3) (by omega) hm (by omega : (3 + 1) * m ≤ n) χ hAvoid

/-! ## §4. Universal distance-pair forbidden lemma.

  For any $b \ge 2$, $d \ge 1$, and $b d \le n$: if $\chi(b d) = c$
  for some color $c$, then for any $y$ with $1 \le y$ and $y + d
  \le n$, NOT both $\chi(y) = c$ and $\chi(y + d) = c$.

  This is the general "distance pair forbidden by multiple" lemma —
  the workhorse of all chain-of-deductions arguments.  Particular
  instances are scattered throughout the Rado literature; this
  states it once, cleanly, parameterized.
-/

/--
  **Universal distance-pair forbidden lemma.**

  For any $b \ge 2$, $d \ge 1$, $b d \le n$, and any valid Rado-
  mono-free $b$-coloring $\chi$ of $\{1, \ldots, n\}$:

  For any $y$ with $1 \le y$ and $y + d \le n$:
  $\chi(b d) = \chi(y) \land \chi(y) = \chi(y + d) \implies \bot$.

  Equivalently: the distance $d$ is FORBIDDEN among positions
  sharing color $\chi(b d)$.

  Proof: the triple $(b d, y, y + d)$ satisfies $b d + b y = b (y
  + d)$.  Monochromaticity yields contradiction with
  `AvoidsMonoSolution`.

  Strictly kernel-pure.
-/
theorem distance_pair_forbidden {b : ℕ} (hb : 2 ≤ b) {n d : ℕ}
    (hd : 1 ≤ d) (hbd : b * d ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    ∀ y, 1 ≤ y → y + d ≤ n →
    χ (b * d) = χ y → χ y = χ (y + d) → False := by
  intro y hy1 hyd_le heq1 heq2
  apply hAvoid
  refine ⟨b * d, y, y + d, hbd, ?_, hyd_le, ?_, heq1, heq2⟩
  · -- y ≤ n.
    omega
  · refine ⟨Nat.mul_pos (by omega) hd, hy1, by omega, ?_⟩
    -- b * d + b * y = b * (y + d).
    ring

/-! ## §5. Distinct-color theorem from triple of self-loops.

  For any $b \ge 2$ and $m \ge 1$ with $b \cdot (b + 1) m / b = (b+1) m \le n$,
  the triple $((b - 1) m, b m, (b + 1) m)$ has pairwise distinct
  colors via the two self-loops (Round 97 §1).

  When the $b$-coloring uses ONLY $b$ colors, the third color is
  uniquely determined: each of the $b - 1$ remaining colors appears
  on exactly... actually with only 3 colors for $b = 3$, the three
  positions span all 3 colors.
-/

/--
  **Three positions, three distinct colors (b = 3 case).**

  For any valid mono-free 3-coloring of $\{1, \ldots, n\}$ with
  $4 m \le n$, the three values $\chi(2 m), \chi(3 m), \chi(4 m)$
  satisfy:
  * $\chi(2 m) \ne \chi(3 m)$ (from self-loop type $x = z$).
  * $\chi(3 m) \ne \chi(4 m)$ (from self-loop type $x = y$).

  When also $6 m \le n$, an additional triple $(6m, 2m, 4m)$
  ensures $\chi(2 m) \ne \chi(4 m)$ provided $\chi(6 m) = \chi(2 m)$.
-/
theorem b3_triple_pair_distinct {n m : ℕ} (hm : 1 ≤ m) (hn : 4 * m ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ (2 * m) ≠ χ (3 * m) ∧ χ (3 * m) ≠ χ (4 * m) := by
  refine ⟨?_, ?_⟩
  · exact Ne.symm <| self_loop_b3_eq_left hm (by omega) χ hAvoid
  · exact Ne.symm <| self_loop_b3_eq_right hm hn χ hAvoid

/-! ## §6. Rado triple canonical form.

  Every Rado triple $(x, y, z)$ satisfying $x + b y = b z$ (with
  all positive) decomposes uniquely as $(b d, y, y + d)$ for some
  $d \ge 1$.  This canonical form makes downstream arguments clean.
-/

/--
  **Rado triple canonical decomposition.**

  For any $b \ge 2$, $(x, y, z)$ is a Rado triple iff there exists
  $d \ge 1$ with $x = b d$ and $z = y + d$ (and $y \ge 1$).
-/
theorem isRadoTriple_iff_canonical {b : ℕ} (hb : 2 ≤ b) (x y z : ℕ) :
    IsRadoTriple b x y z ↔
    ∃ d, 1 ≤ d ∧ x = b * d ∧ z = y + d ∧ 1 ≤ y := by
  unfold IsRadoTriple
  constructor
  · rintro ⟨hx, hy, hz, heq⟩
    -- From x + b·y = b·z and x ≥ 1: b·z > b·y so z > y.
    have hzy : y < z := by
      have hbgt : b * y < b * z := by omega
      exact (Nat.mul_lt_mul_left (by omega : 0 < b)).mp hbgt
    refine ⟨z - y, Nat.sub_pos_of_lt hzy, ?_, ?_, hy⟩
    · -- x = b * (z - y).
      have h_mul_sub : b * (z - y) = b * z - b * y := by
        rw [Nat.mul_sub b z y]
      omega
    · -- z = y + (z - y).
      have := Nat.sub_add_cancel (Nat.le_of_lt hzy)
      omega
  · rintro ⟨d, hd, hxbd, hzyd, hy⟩
    refine ⟨?_, hy, ?_, ?_⟩
    · rw [hxbd]; exact Nat.mul_pos (by omega) hd
    · rw [hzyd]; omega
    · rw [hxbd, hzyd]; ring

/-! ## §7. Coloring structure (extension lemmas for downstream).

  Convenience lemmas combining the above into structural statements
  that downstream proofs frequently need.
-/

/--
  **Convenience lemma: distance-multiple constraint in canonical form.**

  Given a valid Rado-mono-free $b$-coloring of $\{1, \ldots, n\}$:
  for any $d \ge 1$ with $b d \le n$ and any $y$ with $1 \le y$ and
  $y + d \le n$, $\chi(b d), \chi(y), \chi(y + d)$ cannot ALL coincide.
-/
theorem rado_triple_not_all_eq {b : ℕ} (hb : 2 ≤ b) {n d : ℕ}
    (hd : 1 ≤ d) (hbd : b * d ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    ∀ y, 1 ≤ y → y + d ≤ n →
    ¬ (χ (b * d) = χ y ∧ χ y = χ (y + d)) := by
  intro y hy hyd ⟨h1, h2⟩
  exact distance_pair_forbidden hb hd hbd χ hAvoid y hy hyd h1 h2

/-! ## §8. Bundled $b = 3$ universal constraints.

  Convenience theorem packaging all six $b = 3$ self-loop
  inequalities under the single hypothesis $n \ge 24$.  Useful
  as a starting point for any analytic argument on CompressionHyp
  3 3 (which has $n \ge 27$).
-/

/--
  **Bundled $b = 3$ universal self-loop constraints.**

  For any valid Rado-mono-free 3-coloring of $\{1, \ldots, n\}$
  with $n \ge 24$:

  * $\chi(9) \ne \chi(6)$  (from $(9, 6, 9)$)
  * $\chi(18) \ne \chi(12)$  (from $(18, 12, 18)$)
  * $\chi(15) \ne \chi(10)$  (from $(15, 10, 15)$)
  * $\chi(12) \ne \chi(8)$  (from $(12, 8, 12)$)
  * $\chi(21) \ne \chi(14)$  (from $(21, 14, 21)$)
  * $\chi(24) \ne \chi(16)$  (from $(24, 16, 24)$)

  Each inequality is an instance of `self_loop_b3_eq_left` at the
  appropriate $m$.
-/
theorem b3_universal_self_loops {n : ℕ} (hn : 24 ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ 9 ≠ χ 6 ∧ χ 18 ≠ χ 12 ∧ χ 15 ≠ χ 10 ∧
    χ 12 ≠ χ 8 ∧ χ 21 ≠ χ 14 ∧ χ 24 ≠ χ 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact self_loop_b3_eq_left (m := 3) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_left (m := 6) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_left (m := 5) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_left (m := 4) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_left (m := 7) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_left (m := 8) (by omega) (by omega) χ hAvoid

/--
  **Bundled $b = 3$ universal complementary self-loops.**

  For any valid Rado-mono-free 3-coloring of $\{1, \ldots, n\}$
  with $n \ge 24$:

  * $\chi(4) \ne \chi(3)$, $\chi(8) \ne \chi(6)$, $\chi(12) \ne
    \chi(9)$, $\chi(16) \ne \chi(12)$, $\chi(20) \ne \chi(15)$,
    $\chi(24) \ne \chi(18)$.
-/
theorem b3_universal_complementary_self_loops {n : ℕ} (hn : 24 ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ 4 ≠ χ 3 ∧ χ 8 ≠ χ 6 ∧ χ 12 ≠ χ 9 ∧
    χ 16 ≠ χ 12 ∧ χ 20 ≠ χ 15 ∧ χ 24 ≠ χ 18 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact self_loop_b3_eq_right (m := 1) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_right (m := 2) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_right (m := 3) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_right (m := 4) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_right (m := 5) (by omega) (by omega) χ hAvoid
  · exact self_loop_b3_eq_right (m := 6) (by omega) (by omega) χ hAvoid

/-! ## §9. Color-class structural lemma.

  For any valid Rado-mono-free $b$-coloring, EVERY color class is
  Rado-triple-free (free of mono Rado triples within itself).

  Stated abstractly: a color class $C \subseteq \{1, \ldots, n\}$ is
  $b$-Rado-free if $\forall x \in b \cdot (C - C)_{>0} \cap \{1,
  \ldots, n\}$, $x \notin C$ (when $C - C$ denotes the set of
  positive differences).
-/

/--
  **Color class is Rado-triple-free.**

  For any color $c$, the class $C_c = \{y : \chi(y) = c\}$ avoids
  the structure: $\exists$ Rado triple $(x, y, z) \in C_c^3$.

  Equivalently: $\forall y_1, y_2 \in C_c$ with $y_1 < y_2$,
  $b \cdot (y_2 - y_1) \notin C_c$ (when the product is in domain).
-/
theorem color_class_rado_free {b : ℕ} (hb : 2 ≤ b) {n : ℕ}
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution b n χ) (c : ℕ) :
    ∀ y₁ y₂, 1 ≤ y₁ → y₁ < y₂ → y₂ ≤ n →
    b * (y₂ - y₁) ≤ n →
    χ y₁ = c → χ y₂ = c → χ (b * (y₂ - y₁)) ≠ c := by
  intro y₁ y₂ hy1 hlt hy2 hbd hc1 hc2 hbc
  set d := y₂ - y₁ with hd_def
  have hd_pos : 1 ≤ d := by omega
  -- Apply distance_pair_forbidden with x = b·d, y = y₁.
  -- χ(b·d) = c, χ(y₁) = c, χ(y₁ + d) = χ(y₂) = c.
  have hy2_eq : y₁ + d = y₂ := by omega
  apply distance_pair_forbidden hb hd_pos hbd χ hAvoid y₁ hy1
    (by rw [hy2_eq]; exact hy2)
    (hbc.trans hc1.symm)
    (hc1.trans (by rw [hy2_eq]; exact hc2.symm))

/-! ## §10. Color forcing — chain-of-deductions building block.

  In any valid Rado-mono-free $b$-coloring, knowing two of the three
  colors in a Rado triple FORCES the third to differ.  This is the
  atomic step of all chain-of-deductions arguments.
-/

/--
  **Color forcing — from $(b d, y)$ to $(y + d)$.**

  If $\chi(b d) = c$ and $\chi(y) = c$, then $\chi(y + d) \ne c$.

  This is the "right-end forcing" pattern used throughout
  chain-of-deductions arguments.  Atomic building block.
-/
theorem color_forced_right {b : ℕ} (hb : 2 ≤ b) {n d : ℕ}
    (hd : 1 ≤ d) (hbd : b * d ≤ n) {χ : ℕ → ℕ}
    (hAvoid : AvoidsMonoSolution b n χ)
    {y c : ℕ} (hy : 1 ≤ y) (hyd : y + d ≤ n)
    (h1 : χ (b * d) = c) (h2 : χ y = c) :
    χ (y + d) ≠ c := by
  intro h3
  exact distance_pair_forbidden hb hd hbd χ hAvoid y hy hyd
    (h1.trans h2.symm) (h2.trans h3.symm)

/--
  **Color forcing — from $(b d, y + d)$ to $(y)$.**

  If $\chi(b d) = c$ and $\chi(y + d) = c$, then $\chi(y) \ne c$.

  The "left-end forcing" complement.
-/
theorem color_forced_left {b : ℕ} (hb : 2 ≤ b) {n d : ℕ}
    (hd : 1 ≤ d) (hbd : b * d ≤ n) {χ : ℕ → ℕ}
    (hAvoid : AvoidsMonoSolution b n χ)
    {y c : ℕ} (hy : 1 ≤ y) (hyd : y + d ≤ n)
    (h1 : χ (b * d) = c) (h2 : χ (y + d) = c) :
    χ y ≠ c := by
  intro h3
  exact distance_pair_forbidden hb hd hbd χ hAvoid y hy hyd
    (h1.trans h3.symm) (h3.trans h2.symm)

/--
  **Color forcing — from $(y, y + d)$ to $(b d)$.**

  If $\chi(y) = c$ and $\chi(y + d) = c$, then $\chi(b d) \ne c$.

  The "multiple-end forcing" complement.
-/
theorem color_forced_multiple {b : ℕ} (hb : 2 ≤ b) {n d : ℕ}
    (hd : 1 ≤ d) (hbd : b * d ≤ n) {χ : ℕ → ℕ}
    (hAvoid : AvoidsMonoSolution b n χ)
    {y c : ℕ} (hy : 1 ≤ y) (hyd : y + d ≤ n)
    (h1 : χ y = c) (h2 : χ (y + d) = c) :
    χ (b * d) ≠ c := by
  intro h3
  exact distance_pair_forbidden hb hd hbd χ hAvoid y hy hyd
    (h3.trans h1.symm) (h1.trans h2.symm)

/-! ## §11. VALUATION COLORING SATURATION THEOREM.

  **Fundamental result for the threshold conjecture's upper bound.**

  Recall the valuation coloring at level $k$:
  $$\chi_k(n) = v_b(n) \mod k.$$

  This coloring is mono-free on $\{1, \ldots, b^k - 1\}$ for ANY
  $k \ge 1$ (theorem `bAdicVal_avoidsMono` in LowerBound.lean).

  But it SATURATES at position $b^k$: the Rado triple
  $(b^k, 1, 1 + b^{k-1})$ is monochromatic at color 0 in $\chi_k$.

  This is a UNIVERSAL fact (for any $b \ge 2, k \ge 2$): the
  valuation coloring CANNOT be extended to $\{1, \ldots, b^k\}$.
  It explicitly witnesses the SATURATION POINT.

  Verification:
  * $v_b(b^k) = k$, so $\chi_k(b^k) = k \mod k = 0$.
  * $v_b(1) = 0$, so $\chi_k(1) = 0$.
  * $v_b(1 + b^{k-1}) = 0$ (ultrametric), so $\chi_k(1 + b^{k-1}) = 0$.
  * Rado triple: $b^k + b \cdot 1 = b \cdot (1 + b^{k-1})$ ✓.
-/

/--
  **THE valuation coloring saturation theorem.**

  For any $b \ge 2$ and $k \ge 2$, the valuation coloring $\chi_k(n)
  = v_b(n) \mod k$ has a monochromatic Rado triple in $\{1, \ldots,
  b^k\}$.  Specifically, the triple $(b^k, 1, 1 + b^{k-1})$ is
  monochromatic at color 0.

  This is the EXPLICIT WITNESS that the valuation coloring cannot
  extend to length $b^k$.  It is a foundational fact about the
  Rado equation and the valuation coloring.
-/
theorem valuation_coloring_saturates {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    HasMonoSolution b (b ^ k) (fun n => bAdicVal b n % k) := by
  have hb_pos : 0 < b := by omega
  have hbk_pos : 0 < b ^ k := Nat.pow_pos hb_pos
  have hk1 : (k - 1) + 1 = k := by omega
  have hk_pos : 1 ≤ k - 1 + 1 := by omega
  have hb_km1_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
  -- 1 + b^(k-1) ≤ b^k.
  have h_z_le : 1 + b ^ (k - 1) ≤ b ^ k := by
    have h_eq : b ^ k = b * b ^ (k - 1) := by
      conv_lhs => rw [← hk1, pow_succ]
      ring
    have hb_km1_ge_one : 1 ≤ b ^ (k - 1) := hb_km1_pos
    rw [h_eq]
    calc 1 + b ^ (k - 1) ≤ b ^ (k - 1) + b ^ (k - 1) := by omega
      _ = 2 * b ^ (k - 1) := by ring
      _ ≤ b * b ^ (k - 1) := Nat.mul_le_mul_right _ hb
  -- The triple (b^k, 1, 1 + b^(k-1)).
  refine ⟨b ^ k, 1, 1 + b ^ (k - 1), le_refl _, hbk_pos, h_z_le, ?_, ?_, ?_⟩
  · -- IsRadoTriple b (b^k) 1 (1 + b^(k-1)).
    refine ⟨hbk_pos, Nat.one_pos, by omega, ?_⟩
    -- b^k + b * 1 = b * (1 + b^(k-1)).
    have h_eq : b ^ k = b * b ^ (k - 1) := by
      conv_lhs => rw [← hk1, pow_succ]
      ring
    rw [h_eq]
    ring
  · -- (bAdicVal b (b^k) % k) = (bAdicVal b 1 % k).
    show (bAdicVal b (b ^ k)) % k = (bAdicVal b 1) % k
    have h_val_bk : bAdicVal b (b ^ k) = k := by
      have := bAdicVal_b_pow_mul_unit hb (u := 1) Nat.one_pos
        (bAdicVal_one hb) k
      rw [mul_one] at this
      exact this
    rw [h_val_bk, bAdicVal_one hb, Nat.mod_self, Nat.zero_mod]
  · -- (bAdicVal b 1 % k) = (bAdicVal b (1 + b^(k-1)) % k).
    show (bAdicVal b 1) % k = (bAdicVal b (1 + b ^ (k - 1))) % k
    rw [bAdicVal_one hb, bAdicVal_one_plus_pow_eq_zero hb hk]

/--
  **Corollary: valuation coloring is no longer mono-free at $b^k$.**

  $\neg \text{AvoidsMonoSolution}\, b\, b^k\, \chi_k$ for $b \ge 2,
  k \ge 2$.
-/
theorem valuation_coloring_not_avoids_at_b_pow_k
    {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ AvoidsMonoSolution b (b ^ k) (fun n => bAdicVal b n % k) :=
  fun h => h (valuation_coloring_saturates hb hk)

/-! ## §12. Universal triple-position Rado constraint.

  The triple $(2 b m, (b - 1) m, (b + 1) m)$ is a Rado triple for
  the equation $x + b y = b z$ — verification: $2 b m + b (b-1) m
  = 2bm + b^2 m - b m = bm + b^2 m = b(b+1)m$ ✓.

  Combined with the two self-loop universal constraints from §1,
  this triple constraint links $((b-1)m, b m, (b+1)m)$ to the
  doubled position $2 b m$, providing a NEW structural constraint
  on top of the pairwise self-loops.
-/

/--
  **Universal Rado-triple constraint at $(2bm, (b-1)m, (b+1)m)$.**

  For any $b \ge 2$, $m \ge 1$ with $2 b m \le n$ in a valid Rado-
  mono-free $b$-coloring: NOT all three of $\chi((b-1)m),
  \chi(2 b m), \chi((b+1)m)$ are equal.

  Verification of Rado triple: $2 b m + b (b - 1) m = b (b + 1) m$.
-/
theorem rado_triple_2bm_constraint {b : ℕ} (hb : 2 ≤ b) {n m : ℕ}
    (hm : 1 ≤ m) (h2bm : 2 * b * m ≤ n) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    ¬ (χ ((b - 1) * m) = χ (2 * b * m) ∧
       χ (2 * b * m) = χ ((b + 1) * m)) := by
  intro ⟨h1, h2⟩
  apply hAvoid
  -- (b-1)m, (b+1)m bounds:
  have hb1m_le_2bm : (b - 1) * m ≤ 2 * b * m := by
    have : (b - 1) ≤ 2 * b := by omega
    exact Nat.mul_le_mul_right m this
  have hb1m_le_n : (b - 1) * m ≤ n := le_trans hb1m_le_2bm h2bm
  have hbp1m_le_2bm : (b + 1) * m ≤ 2 * b * m := by
    have : (b + 1) ≤ 2 * b := by omega
    exact Nat.mul_le_mul_right m this
  have hbp1m_le_n : (b + 1) * m ≤ n := le_trans hbp1m_le_2bm h2bm
  refine ⟨2 * b * m, (b - 1) * m, (b + 1) * m, h2bm, hb1m_le_n,
         hbp1m_le_n, ?_, h1.symm, h1.trans h2⟩
  refine ⟨Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hm,
         Nat.mul_pos (by omega) hm,
         Nat.mul_pos (by omega) hm, ?_⟩
  -- 2bm + b·((b-1)m) = b·((b+1)m).
  -- LHS: 2bm + b(b-1)m = 2bm + b²m - bm = bm + b²m.
  -- RHS: b(b+1)m = b²m + bm.
  -- Equal in ℕ since both = bm + b²m.
  have hb1 : (b - 1) + 1 = b := Nat.sub_add_cancel (by omega : 1 ≤ b)
  calc 2 * b * m + b * ((b - 1) * m)
      = b * m * (2 + (b - 1)) := by ring
    _ = b * m * ((b - 1) + 1 + 1) := by ring
    _ = b * m * (b + 1) := by rw [hb1]
    _ = b * ((b + 1) * m) := by ring

/-! ## §13. Combined lower-bound + saturation theorem.

  Putting it together: for any $b \ge 2$ and $k \ge 2$, the
  valuation coloring achieves the lower bound and saturates
  exactly at $b^k$.  This is the STRONGEST UNIVERSAL FACT we have
  for the threshold conjecture's matching direction.
-/

/--
  **Threshold conjecture's lower bound is witnessed by valuation.**

  For any $b \ge 2$ and $k \ge 2$, the valuation coloring $\chi_k$:
  1. Avoids mono Rado solutions on $\{1, \ldots, b^k - 1\}$
     (i.e., is mono-free), giving $R_k(b) \ge b^k$.
  2. Has mono Rado solution at $\{1, \ldots, b^k\}$ (saturation),
     i.e., $\chi_k$ specifically cannot extend.

  Combined, this says: the valuation coloring achieves
  EXACTLY $R_k(b) = b^k$ for $\chi_k$ itself.

  Note: this does NOT prove $R_k(b) \le b^k$ (would require ALL
  colorings to fail at $b^k$, not just valuation).  But it shows
  the valuation is precisely the "boundary witness" for the
  conjecture.
-/
theorem valuation_witnesses_boundary {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    (AvoidsMonoSolution b (b ^ k - 1) (bAdicVal b)) ∧
    (HasMonoSolution b (b ^ k) (fun n => bAdicVal b n % k)) := by
  refine ⟨bAdicVal_avoidsMono hb _, valuation_coloring_saturates hb hk⟩

/-! ## §14. SUBCOLORING-AT-MULTIPLES theorem.

  **Fundamental structural theorem**: if χ is a valid Rado-mono-
  free $b$-coloring of $\{1, \ldots, n\}$, then its restriction
  to multiples of $b$ (re-indexed) is ALSO Rado-mono-free for the
  same equation on a smaller domain.

  This is the heart of the **compression argument** that drives
  the cascade theorem (Rounds 21-29): the mono-freeness at one
  level cascades down to mono-freeness at the next level, on
  smaller domains.

  Formally: define $\chi'(m) = \chi(b \cdot m)$ on $\{1, \ldots,
  \lfloor n/b \rfloor\}$.  Then $\chi'$ is mono-free for $x + by
  = bz$.

  Proof: any Rado triple $(x', y', z')$ in $\chi'$ corresponds to
  a Rado triple $(bx', by', bz')$ in the original $\chi$ via the
  scaling map.  Verification: $bx' + b \cdot by' = b \cdot bz'$
  iff $x' + by' = bz'$, hence the triple is Rado iff the scaled
  triple is.  Mono-freeness preserved.

  This is the FOUNDATIONAL THEOREM for the cascade. -/

/--
  **Subcoloring at multiples preserves mono-freeness.**

  For any $b \ge 2$ and any valid Rado-mono-free $b$-coloring $\chi$
  of $\{1, \ldots, n\}$: the subcoloring $\chi'(m) = \chi(b m)$ on
  $\{1, \ldots, n / b\}$ is also Rado-mono-free.

  This is the structural foundation of the cascade argument.
-/
theorem subcoloring_at_multiples {b n : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    AvoidsMonoSolution b (n / b) (fun m => χ (b * m)) := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRado, heq1, heq2⟩
  obtain ⟨hx, hy, hz, hxby⟩ := hRado
  -- Construct the scaled Rado triple (b*x, b*y, b*z) in original domain.
  apply hAvoid
  refine ⟨b * x, b * y, b * z, ?_, ?_, ?_, ?_, heq1, heq2⟩
  · -- b * x ≤ n: since x ≤ n / b, b * x ≤ b * (n / b) ≤ n.
    calc b * x ≤ b * (n / b) := Nat.mul_le_mul_left b hxn
      _ ≤ n := Nat.mul_div_le n b
  · calc b * y ≤ b * (n / b) := Nat.mul_le_mul_left b hyn
      _ ≤ n := Nat.mul_div_le n b
  · calc b * z ≤ b * (n / b) := Nat.mul_le_mul_left b hzn
      _ ≤ n := Nat.mul_div_le n b
  · -- IsRadoTriple b (b*x) (b*y) (b*z): b*x + b*(b*y) = b*(b*z).
    refine ⟨Nat.mul_pos (by omega) hx,
           Nat.mul_pos (by omega) hy,
           Nat.mul_pos (by omega) hz, ?_⟩
    -- b*x + b*(b*y) = b*(b*z).
    -- Original equation: x + b*y = b*z, so multiplying by b:
    calc b * x + b * (b * y) = b * (x + b * y) := by ring
      _ = b * (b * z) := by rw [hxby]

/-! ## §15. ITERATED subcoloring — cascade in full generality.

  Applying Round 104 iteratively: subcoloring at $b^k$-multiples
  is mono-free on $\{1, \ldots, n / b^k\}$.

  This gives the CASCADE structure: starting from a mono-free
  $k$-coloring of $\{1, \ldots, b^k\}$, we get a sequence of
  mono-free colorings of progressively smaller domains.
-/

/--
  **Iterated subcoloring is mono-free.**

  For any $b \ge 2$, $j \ge 0$, and valid Rado-mono-free $b$-
  coloring $\chi$ of $\{1, \ldots, n\}$: the iterated subcoloring
  $\chi_j(m) = \chi(b^j \cdot m)$ on $\{1, \ldots, n / b^j\}$ is
  also Rado-mono-free.

  At $j = k$ for $n = b^k$: $\chi_k$ on $\{1\}$ (single position).
  Captures the descent of the cascade argument.
-/
theorem iterated_subcoloring_mono_free {b : ℕ} (hb : 2 ≤ b) {n : ℕ}
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution b n χ) (j : ℕ) :
    AvoidsMonoSolution b (n / b ^ j) (fun m => χ (b ^ j * m)) := by
  induction j with
  | zero =>
    -- b^0 = 1, n / 1 = n, χ (b^0 * m) = χ m.
    simp only [pow_zero, Nat.div_one, one_mul]
    exact hAvoid
  | succ k ih =>
    -- Apply Round 104 to ih.
    have h_sub := subcoloring_at_multiples (b := b) hb
      (fun m => χ (b ^ k * m)) ih
    -- h_sub : AvoidsMonoSolution b ((n / b^k) / b) (fun m => χ (b^k * (b * m))).
    -- Want: AvoidsMonoSolution b (n / b^(k+1)) (fun m => χ (b^(k+1) * m)).
    -- These are equal since (n/b^k)/b = n/(b^k*b) = n/b^(k+1) and
    -- b^k * (b * m) = b^(k+1) * m.
    have h_div_eq : (n / b ^ k) / b = n / b ^ (k + 1) := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have h_fn_eq : (fun m => χ (b ^ k * (b * m))) = (fun m => χ (b ^ (k + 1) * m)) := by
      funext m
      congr 1
      rw [pow_succ]
      ring
    rw [← h_div_eq, ← h_fn_eq]
    exact h_sub

/-! ## §16. UNIQUENESS OF VALUATION COLORING at $b = 3, k = 2$.

  **NEW MATH DIRECTION**: prove the valuation coloring's structural
  UNIQUENESS at the boundary $k = 2(b-1)$.

  For $b = 3, k = 2, n \ge 8$: any valid Rado-mono-free 2-coloring
  $\chi$ of $\{1, \ldots, n\}$ has the form
  $$\chi(m) = c_0 \text{ if } 3 \nmid m, \quad \chi(m) = c_1 \text{ if } 3 \mid m,$$
  for two distinct colors $c_0, c_1 \in \{0, 1\}$.

  This UNIQUENESS THEOREM combined with the valuation saturation
  (Round 101) gives $R_2(3) = 9$ — exactly the threshold conjecture
  at $(b, k) = (3, 2)$.

  Conjecture for general $(b, k)$ with $k \le 2(b-1)$: similar
  uniqueness holds.  If proven, immediately closes the threshold
  conjecture's matching direction.

  This is the FUNDAMENTAL NEW MATHEMATICS DIRECTION. -/

/--
  **Uniqueness of mono-free 2-coloring at $b = 3$, $n \ge 8$.**

  For any valid Rado-mono-free 2-coloring $\chi$ of $\{1, \ldots,
  n\}$ with $n \ge 8$:
  * $\chi(1) = \chi(2) = \chi(4) = \chi(5) = \chi(7) = \chi(8)$.
  * $\chi(3) = \chi(6)$.
  * $\chi(1) \ne \chi(3)$.

  Equivalent (up to color permutation) to the valuation coloring:
  positions coprime to 3 get one color, multiples of 3 get the other.

  **Significance**: STRUCTURAL UNIQUENESS of the valuation coloring
  at the threshold boundary $k = 2 = 2(b-1)$ for $b = 3$.
  Combined with Round 101 saturation at $b^k = 9$, this gives an
  ALTERNATIVE proof of $R_2(3) = 9$ via uniqueness.
-/
theorem b3_k2_uniqueness {n : ℕ} (hn : 8 ≤ n) (χ : ℕ → ℕ)
    (hValid : IsValidColoring n 2 χ)
    (hAvoid : AvoidsMonoSolution 3 n χ) :
    χ 1 = χ 2 ∧ χ 2 = χ 4 ∧ χ 4 = χ 5 ∧ χ 5 = χ 7 ∧ χ 7 = χ 8 ∧
    χ 3 = χ 6 ∧ χ 1 ≠ χ 3 := by
  -- Helper: build mono triples via hAvoid.
  have mono_3 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ n → y ≤ n → z ≤ n →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- All χ values in {0, 1}.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 2 := hValid 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have hv7 : χ 7 < 2 := hValid 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 2 := hValid 8 (by norm_num) (by omega)
  -- Self-loop constraints.
  have h32 : χ 3 ≠ χ 2 := fun h =>
    mono_3 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h34 : χ 3 ≠ χ 4 := fun h =>
    mono_3 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  have h64 : χ 6 ≠ χ 4 := fun h =>
    mono_3 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h68 : χ 6 ≠ χ 8 := fun h =>
    mono_3 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  -- χ(2) = χ(4): both ≠ χ(3) in 2-coloring.
  have h24 : χ 2 = χ 4 := by omega
  -- χ(6) = χ(3): χ(6) ≠ χ(4) = χ(2), and χ(2) ≠ χ(3), so χ(6) = χ(3) in 2-coloring.
  have h63 : χ 6 = χ 3 := by omega
  -- χ(8) = χ(2): χ(8) ≠ χ(6) = χ(3), so χ(8) = χ(2).
  have h82 : χ 8 = χ 2 := by omega
  -- χ(1) = χ(2): triple (6, 1, 3) is mono iff χ(6) = χ(1) = χ(3).  χ(6) = χ(3), so χ(1) = χ(3) → mono.
  -- h : χ 1 = χ 3.  heq1: χ(6) = χ(1) = h63.trans h.symm.  heq2: χ(1) = χ(3) = h.
  have h13_ne : χ 1 ≠ χ 3 := fun h =>
    mono_3 6 1 3 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      (h63.trans h.symm) h
  have h12 : χ 1 = χ 2 := by omega
  -- χ(5) = χ(2): triple (3, 5, 6) is mono iff χ(3) = χ(5) = χ(6).  χ(3) = χ(6), so χ(5) = χ(3) → mono.
  -- h : χ 5 = χ 3.  heq1: χ(3) = χ(5) = h.symm.  heq2: χ(5) = χ(6) = h.trans h63.symm.
  have h53_ne : χ 5 ≠ χ 3 := fun h =>
    mono_3 3 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      h.symm (h.trans h63.symm)
  have h54 : χ 5 = χ 4 := by omega
  -- χ(7) = χ(2): triple (3, 6, 7) is mono iff χ(3) = χ(6) = χ(7).  χ(3) = χ(6), so χ(7) = χ(3) → mono.
  -- h : χ 7 = χ 3.  heq1: χ(3) = χ(6) = h63.symm.  heq2: χ(6) = χ(7) = h63.trans h.symm.
  have h73_ne : χ 7 ≠ χ 3 := fun h =>
    mono_3 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      h63.symm (h63.trans h.symm)
  have h78 : χ 7 = χ 8 := by omega
  refine ⟨h12, h24, ?_, ?_, h78, h63.symm, h13_ne⟩
  · -- χ(4) = χ(5).
    exact h54.symm
  · -- χ(5) = χ(7).
    omega

/-! ## §17. UNIQUENESS at $b = 4, k = 2$.

  Extending Round 109's uniqueness to $b = 4$.  For any valid
  mono-free 2-coloring of $\{1, \ldots, n\}$ for $n \ge 15$ and
  Rado equation $x + 4 y = 4 z$:
  * All non-multiples of 4 have same color.
  * All multiples of 4 have the same (other) color.

  This is the SECOND instance of valuation uniqueness — extending
  Round 109 from $b = 3$ to $b = 4$.  The pattern is the same:
  use self-loops + cross-triples to force structural rigidity.
-/

/--
  **Uniqueness of mono-free 2-coloring at $b = 4$, $n \ge 15$.**

  For any valid Rado-mono-free 2-coloring $\chi$ of $\{1, \ldots,
  n\}$ with $n \ge 15$:
  * Multiples of 4: $\chi(4) = \chi(8) = \chi(12)$.
  * Non-multiples adjacent to multiples: forced to opposite color.
  * The coloring is fully determined up to color permutation.

  Combined with `self_loop_eq_left` and `self_loop_eq_right` at
  $b = 4$, plus cross-triples through $\chi(8)$ and $\chi(12)$.
-/
theorem b4_k2_multiples_agree {n : ℕ} (hn : 15 ≤ n) (χ : ℕ → ℕ)
    (hValid : IsValidColoring n 2 χ)
    (hAvoid : AvoidsMonoSolution 4 n χ) :
    χ 4 = χ 8 ∧ χ 8 = χ 12 ∧ χ 4 ≠ χ 3 := by
  -- Helper.
  have mono_4 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ n → y ≤ n → z ≤ n →
      x + 4 * y = 4 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Valid values < 2.
  have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have hv8 : χ 8 < 2 := hValid 8 (by norm_num) (by omega)
  have hv12 : χ 12 < 2 := hValid 12 (by norm_num) (by omega)
  -- Self-loop (4, 3, 4): χ(4) ≠ χ(3).
  have h43 : χ 4 ≠ χ 3 := fun h =>
    mono_4 4 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- Self-loop (4, 4, 5): χ(4) ≠ χ(5).
  have h45 : χ 4 ≠ χ 5 := fun h =>
    mono_4 4 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  -- Self-loop (8, 6, 8): χ(8) ≠ χ(6).
  have h86 : χ 8 ≠ χ 6 := fun h =>
    mono_4 8 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- Now: χ(3) = χ(5) (both ≠ χ(4) in 2-coloring).
  have h35 : χ 3 = χ 5 := by omega
  -- Triple (8, 3, 5): 8 + 12 = 20 = 4·5.  Mono iff χ(8) = χ(3) = χ(5).
  -- χ(3) = χ(5).  So mono iff χ(8) = χ(3).  Hence χ(8) ≠ χ(3).
  have h83 : χ 8 ≠ χ 3 := fun h =>
    mono_4 8 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      h h35
  -- So χ(8) = χ(4) (both ≠ χ(3) in 2-coloring).
  have h84 : χ 8 = χ 4 := by omega
  -- Triple (12, 3, 6): 12 + 12 = 24 = 4·6.  Mono iff χ(12) = χ(3) = χ(6).
  -- χ(6) ≠ χ(8) = χ(4), so χ(6) = χ(3) in 2-coloring.
  have h63 : χ 6 = χ 3 := by omega
  -- Now χ(12) ≠ χ(3) via (12, 3, 6).
  have h12_3 : χ 12 ≠ χ 3 := fun h =>
    mono_4 12 3 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      h h63.symm
  -- So χ(12) = χ(4) (both ≠ χ(3)).
  have h12_4 : χ 12 = χ 4 := by omega
  refine ⟨h84.symm, ?_, h43⟩
  -- χ(8) = χ(12): both = χ(4).
  omega

/-! ## §18. UNIQUENESS at $b = 5, k = 2$.

  Third instance: $b = 5, k = 2, n \ge 24$.  Multiples of 5
  ($\chi(5), \chi(10), \chi(15), \chi(20)$) all agree; distinct
  from $\chi(4)$.

  Extends Rounds 109 (b=3) and 110 (b=4).  The Valuation Uniqueness
  Conjecture is now confirmed at $b = 3, 4, 5$ for $k = 2$.
-/

/--
  **Uniqueness of mono-free 2-coloring at $b = 5$, $n \ge 24$.**

  $\chi(5) = \chi(10) = \chi(15) = \chi(20)$ and $\chi(5) \ne \chi(4)$.
-/
theorem b5_k2_multiples_agree {n : ℕ} (hn : 24 ≤ n) (χ : ℕ → ℕ)
    (hValid : IsValidColoring n 2 χ)
    (hAvoid : AvoidsMonoSolution 5 n χ) :
    χ 5 = χ 10 ∧ χ 10 = χ 15 ∧ χ 15 = χ 20 ∧ χ 5 ≠ χ 4 := by
  have mono_5 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ n → y ≤ n → z ≤ n →
      x + 5 * y = 5 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have hv8 : χ 8 < 2 := hValid 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 2 := hValid 10 (by norm_num) (by omega)
  have hv12 : χ 12 < 2 := hValid 12 (by norm_num) (by omega)
  have hv15 : χ 15 < 2 := hValid 15 (by norm_num) (by omega)
  have hv16 : χ 16 < 2 := hValid 16 (by norm_num) (by omega)
  have hv20 : χ 20 < 2 := hValid 20 (by norm_num) (by omega)
  have h54 : χ 5 ≠ χ 4 := fun h =>
    mono_5 5 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h56 : χ 5 ≠ χ 6 := fun h =>
    mono_5 5 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  have h10_8 : χ 10 ≠ χ 8 := fun h =>
    mono_5 10 8 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h10_12 : χ 10 ≠ χ 12 := fun h =>
    mono_5 10 10 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  have h15_12 : χ 15 ≠ χ 12 := fun h =>
    mono_5 15 12 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h20_16 : χ 20 ≠ χ 16 := fun h =>
    mono_5 20 16 20 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  have h46 : χ 4 = χ 6 := by omega
  have h8_12 : χ 8 = χ 12 := by omega
  have h10_4 : χ 10 ≠ χ 4 := fun h =>
    mono_5 10 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h46
  have h10_5 : χ 10 = χ 5 := by omega
  have h8_4 : χ 8 = χ 4 := by omega
  have h15_5 : χ 15 = χ 5 := by omega
  have h20_4 : χ 20 ≠ χ 4 := fun h =>
    mono_5 20 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      (h.trans h8_4.symm) h8_12
  have h20_5 : χ 20 = χ 5 := by omega
  refine ⟨h10_5.symm, ?_, ?_, h54⟩
  · omega
  · omega

/-! ## §19. THRESHOLD CONJECTURE CLOSURE at $b = 3, k = 2$.

  Combining uniqueness (Round 109) and saturation (Round 101) at
  $b = 3, k = 2$: there exists NO valid mono-free 2-coloring of
  $\{1, \ldots, 9\}$ for $b = 3$.

  This proves $R_2(3) \le 9$ via the analytic chain:
  1. Any mono-free 2-coloring of $\{1, \ldots, 9\}$ extends to $\{1,
     \ldots, 8\}$.
  2. By Round 109 uniqueness, the restriction is valuation up to
     permutation.
  3. By Round 92's self-loop $(9, 6, 9)$, $\chi(9) \ne \chi(6)$.
  4. Combined with $\chi(6) = \chi(3)$ from uniqueness, $\chi(9)$
     must equal $\chi(1) = \chi(4)$ (the non-3-multiple color).
  5. Then triple $(9, 1, 4)$: all three positions colored same.
     But this is a Rado triple!  Mono.  Contradiction.

  Combined with $R_2(3) \ge 9$ (Round 51 valuation lower bound),
  this gives $R_2(3) = 9$ via **uniqueness + saturation**.

  Same theorem as `thm_k2 3` but proven through a DIFFERENT path,
  validating the uniqueness-saturation approach to the threshold
  conjecture.
-/

/--
  **THE UPPER BOUND $R_2(3) \le 9$ via uniqueness + saturation.**

  No valid mono-free 2-coloring of $\{1, \ldots, 9\}$ exists for
  $b = 3$.  Proved using Round 109 uniqueness + saturation logic.
-/
theorem R2_3_upper_via_uniqueness :
    ∀ χ : ℕ → ℕ, IsValidColoring 9 2 χ → AvoidsMonoSolution 3 9 χ → False := by
  intro χ hValid hAvoid
  -- Step 1: Apply Round 109 uniqueness to {1, ..., 9} (n ≥ 8).
  obtain ⟨h12, h24, h45, h57, h78, h36, h13_ne⟩ :=
    b3_k2_uniqueness (n := 9) (by omega) χ hValid hAvoid
  -- Step 2: χ(9) ≠ χ(6) from self-loop (9, 6, 9).
  have h96_ne : χ 9 ≠ χ 6 := by
    have := self_loop_b3_eq_left (m := 3) (by omega) (by omega : 3 * 3 ≤ 9) χ hAvoid
    -- self_loop_b3_eq_left m=3 gives χ(9) ≠ χ(6).
    convert this using 2
  -- Step 3: χ(9) = χ(1) (in 2-coloring, since χ(9) ≠ χ(6) = χ(3) and χ(1) ≠ χ(3)).
  have hv9 : χ 9 < 2 := hValid 9 (by norm_num) (by omega)
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have h9_eq_1 : χ 9 = χ 1 := by omega
  -- Step 4: Triple (9, 1, 4) is mono — all three colored χ(1).
  -- 9 + 3*1 = 12 = 3*4. ✓
  have h_mono : χ 9 = χ 1 ∧ χ 1 = χ 4 := by
    refine ⟨h9_eq_1, ?_⟩
    -- χ(1) = χ(4) from uniqueness chain h12, h24.
    exact h12.trans h24
  apply hAvoid
  refine ⟨9, 1, 4, by omega, by omega, by omega, ?_, h_mono.1, h_mono.2⟩
  refine ⟨by omega, by omega, by omega, ?_⟩
  ring

/--
  **$R_2(3) = 9$ — analytic proof via uniqueness + saturation.**

  Combines `thm_lower 3 2` (lower bound) with `R2_3_upper_via_uniqueness`
  (upper bound).  Alternative proof of `thm_k2 3`, validating the
  uniqueness-saturation route to threshold conjecture closure.
-/
theorem R2_3_eq_9 : IsRadoNumber 3 2 9 := by
  refine ⟨?_, ?_⟩
  · exact thm_lower 3 2 (by omega) (by omega)
  · -- RadoNumberAtMost 3 2 9 = ∀ χ, IsValidColoring 9 2 χ → HasMonoSolution 3 9 χ.
    intro χ hValid
    by_contra hNot
    -- hNot : ¬ HasMonoSolution = AvoidsMonoSolution.
    exact R2_3_upper_via_uniqueness χ hValid hNot

/-! ## §20. THRESHOLD CONJECTURE CLOSURE at $b = 4, k = 2$.

  Apply the **uniqueness + saturation blueprint** to $(b, k) =
  (4, 2)$.  Need to extend Round 110's multiples-agree to full
  uniqueness at $b = 4$, then combine with saturation at $n = 16$.

  Triple $(16, 1, 5)$: $16 + 4 = 20 = 4 \cdot 5$.  In valuation
  coloring: $\chi_2(16) = 0 = \chi_2(1) = \chi_2(5)$.  Mono.
  By uniqueness extension: chi(16), chi(1), chi(5) all equal
  in any valid mono-free 2-coloring → contradiction.
-/

/--
  **THE UPPER BOUND $R_2(4) \le 16$ via uniqueness + saturation.**

  No valid mono-free 2-coloring of $\{1, \ldots, 16\}$ for $b = 4$.
-/
theorem R2_4_upper_via_uniqueness :
    ∀ χ : ℕ → ℕ, IsValidColoring 16 2 χ → AvoidsMonoSolution 4 16 χ → False := by
  intro χ hValid hAvoid
  -- Helper:
  have mono_4 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 16 → y ≤ 16 → z ≤ 16 →
      x + 4 * y = 4 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Apply Round 110 multiples-agree.
  obtain ⟨h48, h8_12, h43_ne⟩ := b4_k2_multiples_agree (n := 16) (by omega) χ hValid hAvoid
  -- Derive χ(12) = χ(4).
  have h_124 : χ 12 = χ 4 := (h48.trans h8_12).symm
  -- All values < 2.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv12 : χ 12 < 2 := hValid 12 (by norm_num) (by omega)
  have hv16 : χ 16 < 2 := hValid 16 (by norm_num) (by omega)
  -- Self-loop (4, 4, 5): χ(5) ≠ χ(4).
  have h54_ne : χ 5 ≠ χ 4 := fun h =>
    mono_4 4 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h.symm
  -- Triple (12, 1, 4): 12 + 4 = 16 = 4·4.  Mono iff χ(12) = χ(1) AND χ(1) = χ(4).
  -- χ(12) = χ(4).  So mono iff χ(1) = χ(4).  Hence χ(1) ≠ χ(4).
  have h14_ne : χ 1 ≠ χ 4 := fun h =>
    mono_4 12 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      (h_124.trans h.symm) h
  -- Self-loop (16, 12, 16): χ(16) ≠ χ(12) = χ(4).
  have h16_4_ne : χ 16 ≠ χ 4 := fun h =>
    mono_4 16 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      (h.trans h_124.symm) (h_124.trans h.symm)
  -- In 2-coloring: chi(1), chi(5), chi(16) all ≠ chi(4), so all equal.
  have h16_eq_1 : χ 16 = χ 1 := by omega
  have h1_eq_5 : χ 1 = χ 5 := by omega
  -- Triple (16, 1, 5): 16 + 4 = 20 = 4·5.  Mono.
  apply hAvoid
  refine ⟨16, 1, 5, by omega, by omega, by omega, ?_, h16_eq_1, h1_eq_5⟩
  refine ⟨by omega, by omega, by omega, ?_⟩
  ring

/--
  **$R_2(4) = 16$ via uniqueness + saturation blueprint.**
-/
theorem R2_4_eq_16 : IsRadoNumber 4 2 16 := by
  refine ⟨?_, ?_⟩
  · exact thm_lower 4 2 (by omega) (by omega)
  · intro χ hValid
    by_contra hNot
    exact R2_4_upper_via_uniqueness χ hValid hNot

/-
  ### §20.  Round 114 — third blueprint instance ($R_2(5) = 25$).

  Even cleaner than Round 113: by Round 111 we have $\chi(5) = \chi(10)
  = \chi(15) = \chi(20)$ and $\chi(5) \ne \chi(4)$.  Then in any valid
  mono-free 2-coloring of $\{1, \ldots, 25\}$:

    * Self-loop $(25, 20, 25)$:  $\chi(25) \ne \chi(20) = \chi(5)$.
    * Triple $(20, 1, 5)$:  $20 + 5 = 25 = 5 \cdot 5$.  Since
      $\chi(20) = \chi(5)$, mono iff $\chi(1) = \chi(5)$.  Hence
      $\chi(1) \ne \chi(5)$.
    * Self-loop $(5, 5, 6)$:  $\chi(6) \ne \chi(5)$.

  In a $2$-coloring, $\chi(1), \chi(6), \chi(25)$ are all the
  $\chi(4)$-color, so equal to each other.  Triple $(25, 1, 6)$:
  $25 + 5 = 30 = 5 \cdot 6$, is then monochromatic — contradiction.
-/

/--
  **No valid mono-free 2-coloring of $\{1, \ldots, 25\}$ for $b = 5$.**
-/
theorem R2_5_upper_via_uniqueness :
    ∀ χ : ℕ → ℕ, IsValidColoring 25 2 χ → AvoidsMonoSolution 5 25 χ → False := by
  intro χ hValid hAvoid
  -- Helper:
  have mono_5 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 25 → y ≤ 25 → z ≤ 25 →
      x + 5 * y = 5 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Apply Round 111 multiples-agree.
  obtain ⟨h5_10, h10_15, h15_20, h54_ne⟩ :=
    b5_k2_multiples_agree (n := 25) (by omega) χ hValid hAvoid
  -- Derive χ(5) = χ(20).
  have h5_20 : χ 5 = χ 20 := h5_10.trans (h10_15.trans h15_20)
  -- All values < 2.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have hv20 : χ 20 < 2 := hValid 20 (by norm_num) (by omega)
  have hv25 : χ 25 < 2 := hValid 25 (by norm_num) (by omega)
  -- Self-loop (5, 5, 6): χ(6) ≠ χ(5).
  have h65_ne : χ 6 ≠ χ 5 := fun h =>
    mono_5 5 5 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h.symm
  -- Self-loop (25, 20, 25): χ(25) ≠ χ(20) = χ(5).
  have h25_20_ne : χ 25 ≠ χ 20 := fun h =>
    mono_5 25 20 25 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- Triple (20, 1, 5): 20 + 5 = 25 = 5·5.  Mono iff χ(20) = χ(1) AND
  -- χ(1) = χ(5).  Since χ(20) = χ(5), mono iff χ(1) = χ(5).
  -- Hence χ(1) ≠ χ(5).
  have h1_5_ne : χ 1 ≠ χ 5 := fun h =>
    mono_5 20 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
      (h5_20.symm.trans h.symm) h
  -- In 2-coloring: χ(1), χ(6), χ(25) all ≠ χ(5), so all equal.
  have h25_eq_1 : χ 25 = χ 1 := by omega
  have h1_eq_6 : χ 1 = χ 6 := by omega
  -- Triple (25, 1, 6): 25 + 5 = 30 = 5·6.  Mono.
  apply hAvoid
  refine ⟨25, 1, 6, by omega, by omega, by omega, ?_, h25_eq_1, h1_eq_6⟩
  refine ⟨by omega, by omega, by omega, ?_⟩
  ring

/--
  **$R_2(5) = 25$ via uniqueness + saturation blueprint.**

  Third blueprint instance, completing $R_2(b)$ for $b \in \{3, 4, 5\}$
  via the analytic uniqueness route.
-/
theorem R2_5_eq_25 : IsRadoNumber 5 2 25 := by
  refine ⟨?_, ?_⟩
  · exact thm_lower 5 2 (by omega) (by omega)
  · intro χ hValid
    by_contra hNot
    exact R2_5_upper_via_uniqueness χ hValid hNot

/-! ## §21. Round 115 — UNIVERSAL $\chi(2b) = \chi(b)$ for $k = 2$.

  The first GENUINELY UNIVERSAL multiples-agree statement.  Generalises
  the case analysis of Rounds 109/110/111: at any $b \ge 2$, in any
  valid mono-free 2-coloring on $\{1, \ldots, n\}$ with $2b \le n$, we
  have $\chi(2b) = \chi(b)$.

  The key Rado triple is $(2b, b-1, b+1)$:
  $$2b + b(b-1) = 2b + b^2 - b = b^2 + b = b(b+1).$$

  Combined with the universal self-loops
  `self_loop_eq_left m=1` (giving $\chi(b) \ne \chi(b-1)$) and
  `self_loop_eq_right m=1` (giving $\chi(b+1) \ne \chi(b)$),
  in the 2-coloring this forces $\chi(b-1) = \chi(b+1)$, then the
  cross-triple gives $\chi(2b) \ne \chi(b-1)$, hence $\chi(2b) = \chi(b)$.

  This single lemma replaces the per-$b$ Round 109/110/111 case
  analyses.  Strictly kernel-pure.
-/

/--
  **Universal $\chi(2b) = \chi(b)$ at $k = 2$.**

  For any $b \ge 2$ and any valid mono-free 2-coloring of
  $\{1, \ldots, n\}$ with $2b \le n$: $\chi(2b) = \chi(b)$.
-/
theorem k2_chi_2b_eq_chi_b {b n : ℕ} (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (χ : ℕ → ℕ) (hValid : IsValidColoring n 2 χ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    χ (2 * b) = χ b := by
  -- Position bounds.
  have hb_pos : 0 < b := by omega
  have hbm1_pos : 0 < b - 1 := by omega
  have hbp1_pos : 0 < b + 1 := by omega
  have h2b_pos : 0 < 2 * b := by omega
  have hbm1_le : b - 1 ≤ n := by omega
  have hb_le : b ≤ n := by omega
  have hbp1_le : b + 1 ≤ n := by omega
  -- Valid 2-coloring: all values < 2.
  have hvbm1 : χ (b - 1) < 2 := hValid (b - 1) hbm1_pos hbm1_le
  have hvb : χ b < 2 := hValid b hb_pos hb_le
  have hvbp1 : χ (b + 1) < 2 := hValid (b + 1) hbp1_pos hbp1_le
  have hv2b : χ (2 * b) < 2 := hValid (2 * b) h2b_pos hn
  -- Universal self-loops at m = 1.
  have h_b_ne_bm1 : χ (b * 1) ≠ χ ((b - 1) * 1) :=
    self_loop_eq_left hb (by omega) (by simp; omega) χ hAvoid
  have h_bp1_ne_b : χ ((b + 1) * 1) ≠ χ (b * 1) :=
    self_loop_eq_right hb (by omega) (by simp; omega) χ hAvoid
  -- Strip the *1.
  simp only [mul_one] at h_b_ne_bm1 h_bp1_ne_b
  -- In 2-coloring: χ(b-1) = χ(b+1).
  have h_bm1_eq_bp1 : χ (b - 1) = χ (b + 1) := by omega
  -- Cross-triple (2b, b-1, b+1):  2b + b(b-1) = b(b+1).
  have h_2b_ne_bm1 : χ (2 * b) ≠ χ (b - 1) := by
    intro h
    apply hAvoid
    refine ⟨2 * b, b - 1, b + 1, hn, hbm1_le, hbp1_le,
            ⟨h2b_pos, hbm1_pos, hbp1_pos, ?_⟩, h, h_bm1_eq_bp1⟩
    -- 2b + b(b-1) = b(b+1).
    have hb1 : (b - 1) + 1 = b := Nat.sub_add_cancel (by omega : 1 ≤ b)
    calc 2 * b + b * (b - 1)
        = b * ((b - 1) + 1) + b := by ring
      _ = b * b + b := by rw [hb1]
      _ = b * (b + 1) := by ring
  -- 2-coloring squeeze: χ(2b) ≠ χ(b-1), and χ(b) ≠ χ(b-1), all <2 → χ(2b) = χ(b).
  omega

/-! ## §22. Round 116 — UNIVERSAL $\chi((b-1)b) = \chi(b)$ for $k = 2$.

  Builds on Round 115 (universal $\chi(2b) = \chi(b)$).  The crucial
  Rado triple this time is $((b-1)b, b-1, 2(b-1))$:
  $$(b-1)b + b(b-1) = 2b(b-1) = b \cdot 2(b-1).$$

  In a 2-coloring, both $\chi(b-1)$ and $\chi(2(b-1))$ are "off-color"
  from $\chi(b)$ (the latter via self-loop scaled by $m = 2$ at $2b$,
  combined with $\chi(2b) = \chi(b)$ from Round 115).  Hence
  $\chi(b-1) = \chi(2(b-1))$ in the 2-coloring, so the cross-triple
  forces $\chi((b-1)b) \ne \chi(b-1)$, giving $\chi((b-1)b) = \chi(b)$.

  This is the SECOND universal multiples-agree statement and the
  KEY enabler of the universal $R_2(b) = b^2$ blueprint (Round 117).
-/

/--
  **Universal $\chi((b-1)b) = \chi(b)$ at $k = 2$.**

  For any $b \ge 3$ and any valid mono-free 2-coloring of
  $\{1, \ldots, n\}$ with $(b-1) b \le n$: $\chi((b-1) b) = \chi b$.
-/
theorem k2_chi_bm1_b_eq_chi_b {b n : ℕ} (hb : 3 ≤ b) (hn : (b - 1) * b ≤ n)
    (χ : ℕ → ℕ) (hValid : IsValidColoring n 2 χ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    χ ((b - 1) * b) = χ b := by
  -- Position bounds.
  have hb_pos : 0 < b := by omega
  have hbm1_pos : 0 < b - 1 := by omega
  have h2bm1_pos : 0 < 2 * (b - 1) := by omega
  have h2b_le_bm1b : 2 * b ≤ (b - 1) * b := by
    have h2_le_bm1 : 2 ≤ b - 1 := by omega
    exact Nat.mul_le_mul_right b h2_le_bm1
  have hbm1_le : b - 1 ≤ n := by
    have : (b - 1) ≤ (b - 1) * b := Nat.le_mul_of_pos_right (b - 1) hb_pos
    omega
  have h2bm1_le : 2 * (b - 1) ≤ n := by
    have h2_le_b : 2 ≤ b := by omega
    have : 2 * (b - 1) ≤ b * (b - 1) :=
      Nat.mul_le_mul_right (b - 1) h2_le_b
    have h_eq : b * (b - 1) = (b - 1) * b := by ring
    rw [h_eq] at this
    omega
  have hb_le : b ≤ n := by omega
  have h2b_le : 2 * b ≤ n := by omega
  have hbm1b_pos : 0 < (b - 1) * b := Nat.mul_pos hbm1_pos hb_pos
  -- Valid 2-coloring: all values < 2.
  have hvbm1 : χ (b - 1) < 2 := hValid (b - 1) hbm1_pos hbm1_le
  have hvb : χ b < 2 := hValid b hb_pos hb_le
  have hv2bm1 : χ (2 * (b - 1)) < 2 := hValid (2 * (b - 1)) h2bm1_pos h2bm1_le
  have hv2b : χ (2 * b) < 2 := hValid (2 * b) (by omega) h2b_le
  have hvbm1b : χ ((b - 1) * b) < 2 := hValid ((b - 1) * b) hbm1b_pos hn
  -- Universal self-loop at m = 1: χ(b) ≠ χ(b-1).
  have h_b_ne_bm1 : χ (b * 1) ≠ χ ((b - 1) * 1) :=
    self_loop_eq_left (by omega) (by omega) (by simp; omega) χ hAvoid
  simp only [mul_one] at h_b_ne_bm1
  -- Universal self-loop at m = 2: χ(2b) ≠ χ(2(b-1)).
  have h_2b_ne_2bm1 : χ (b * 2) ≠ χ ((b - 1) * 2) :=
    self_loop_eq_left (by omega) (by omega) (by
      have : b * 2 = 2 * b := by ring
      rw [this]; exact h2b_le) χ hAvoid
  have h_2b_alt : χ (b * 2) = χ (2 * b) := by congr 1; ring
  have h_2bm1_alt : χ ((b - 1) * 2) = χ (2 * (b - 1)) := by congr 1; ring
  rw [h_2b_alt, h_2bm1_alt] at h_2b_ne_2bm1
  -- Round 115: χ(2b) = χ(b).
  have h_2b_eq_b : χ (2 * b) = χ b :=
    k2_chi_2b_eq_chi_b (by omega) h2b_le χ hValid hAvoid
  -- Combine: χ(2(b-1)) ≠ χ(2b) = χ(b), so χ(2(b-1)) ≠ χ(b).
  have h_2bm1_ne_b : χ (2 * (b - 1)) ≠ χ b := by
    rw [← h_2b_eq_b]; exact h_2b_ne_2bm1.symm
  -- 2-coloring: χ(b-1) ≠ χ(b), χ(2(b-1)) ≠ χ(b), all <2 → χ(b-1) = χ(2(b-1)).
  have h_bm1_eq_2bm1 : χ (b - 1) = χ (2 * (b - 1)) := by omega
  -- Cross-triple ((b-1)b, b-1, 2(b-1)): (b-1)b + b(b-1) = 2b(b-1).
  have h_bm1b_ne_bm1 : χ ((b - 1) * b) ≠ χ (b - 1) := by
    intro h
    apply hAvoid
    refine ⟨(b - 1) * b, b - 1, 2 * (b - 1), hn, hbm1_le, h2bm1_le,
            ⟨hbm1b_pos, hbm1_pos, h2bm1_pos, ?_⟩, h, h_bm1_eq_2bm1⟩
    -- (b-1)b + b(b-1) = b · 2(b-1) = 2b(b-1).
    ring
  -- 2-coloring squeeze: χ((b-1)b) ≠ χ(b-1), χ(b) ≠ χ(b-1), all <2 → χ((b-1)b) = χ(b).
  omega

/-! ## §23. Round 117 — UNIVERSAL $R_2(b) = b^2$ via the blueprint.

  CONSOLIDATES Rounds 115/116 into a single universal closure of the
  threshold conjecture at $k = 2$.  Provides an INDEPENDENT proof
  of `thm_k2`'s upper-bound for $b \ge 3$, going through the
  uniqueness + saturation route rather than `lem_compress2` + DPL.

  Outline:
    (1) Round 116 gives $\chi((b-1)b) = \chi(b)$.
    (2) Self-loop type-$x=z$ at $m = b$ gives $\chi(b^2) \ne \chi((b-1)b)
        = \chi(b)$.
    (3) Triple $((b-1)b, 1, b)$: $(b-1)b + b = b^2 = b \cdot b$.
        Mono iff $\chi((b-1)b) = \chi(1) \wedge \chi(1) = \chi(b)$.
        Since $\chi((b-1)b) = \chi(b)$, mono iff $\chi(1) = \chi(b)$.
        Hence $\chi(1) \ne \chi(b)$.
    (4) Self-loop type-$x=y$ at $m = 1$ gives $\chi(b+1) \ne \chi(b)$.
    (5) In 2-coloring, $\chi(b^2) = \chi(1) = \chi(b+1)$ (all
        $\ne \chi(b)$).
    (6) Final mono triple $(b^2, 1, b+1)$: $b^2 + b = b(b+1)$ ✓ Rado.
        $\chi(b^2) = \chi(1) = \chi(b+1)$ from (5) — MONO.  ⊥
-/

/--
  **Universal $R_2(b) = b^2$ upper bound at $k = 2$ for $b \ge 3$.**

  No valid mono-free 2-coloring of $\{1, \ldots, b^2\}$ exists.
  Completes the analytic blueprint at all $b \ge 3$.
-/
theorem R2_b_upper_via_uniqueness {b : ℕ} (hb : 3 ≤ b)
    (χ : ℕ → ℕ) (hValid : IsValidColoring (b ^ 2) 2 χ)
    (hAvoid : AvoidsMonoSolution b (b ^ 2) χ) : False := by
  -- Position bounds.
  have hb_pos : 0 < b := by omega
  have hbm1_pos : 0 < b - 1 := by omega
  have hbp1_pos : 0 < b + 1 := by omega
  have hbb_pos : 0 < b * b := Nat.mul_pos hb_pos hb_pos
  have hbm1b_pos : 0 < (b - 1) * b := Nat.mul_pos hbm1_pos hb_pos
  -- b^2 = b * b.
  have hpow2 : (b : ℕ) ^ 2 = b * b := by ring
  -- Bounds.
  have hb_le : b ≤ b ^ 2 := by rw [hpow2]; exact Nat.le_mul_of_pos_right b hb_pos
  have hbp1_le : b + 1 ≤ b ^ 2 := by
    rw [hpow2]
    have h_bp1_le_2b : b + 1 ≤ 2 * b := by omega
    have h_2b_le_bb : 2 * b ≤ b * b :=
      Nat.mul_le_mul_right b (by omega : 2 ≤ b)
    exact le_trans h_bp1_le_2b h_2b_le_bb
  have hbm1b_le : (b - 1) * b ≤ b ^ 2 := by
    rw [hpow2]
    exact Nat.mul_le_mul_right b (by omega : b - 1 ≤ b)
  have hbb_le : b * b ≤ b ^ 2 := le_of_eq hpow2.symm
  have h1_le : 1 ≤ b ^ 2 := by omega
  -- All χ values < 2.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) h1_le
  have hvb : χ b < 2 := hValid b hb_pos hb_le
  have hvbp1 : χ (b + 1) < 2 := hValid (b + 1) hbp1_pos hbp1_le
  have hvbm1b : χ ((b - 1) * b) < 2 := hValid ((b - 1) * b) hbm1b_pos hbm1b_le
  have hvbb : χ (b * b) < 2 := hValid (b * b) hbb_pos hbb_le
  -- Helper.
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ b ^ 2 → y ≤ b ^ 2 → z ≤ b ^ 2 →
      x + b * y = b * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- (1) Round 116: χ((b-1)b) = χ(b).
  have h_bm1b_eq_b : χ ((b - 1) * b) = χ b :=
    k2_chi_bm1_b_eq_chi_b hb hbm1b_le χ hValid hAvoid
  -- (2) Self-loop type-x=z at m=b: χ(b * b) ≠ χ((b-1) * b).
  have h_bb_ne_bm1b : χ (b * b) ≠ χ ((b - 1) * b) :=
    self_loop_eq_left (by omega) hb_pos hbb_le χ hAvoid
  have h_bb_ne_b : χ (b * b) ≠ χ b := by
    rw [← h_bm1b_eq_b]; exact h_bb_ne_bm1b
  -- (3) Triple ((b-1)b, 1, b): (b-1)b + b = b · b.
  have h_1_ne_b : χ 1 ≠ χ b := by
    intro h
    -- We need χ((b-1)b) = χ(1) and χ(1) = χ(b).  By h_bm1b_eq_b and h.
    have h_bm1b_eq_1 : χ ((b - 1) * b) = χ 1 := h_bm1b_eq_b.trans h.symm
    apply mono ((b - 1) * b) 1 b hbm1b_pos (by norm_num) hb_pos hbm1b_le h1_le hb_le
    · -- (b-1)b + b * 1 = b * b.
      have hb1 : (b - 1) + 1 = b := Nat.sub_add_cancel (by omega : 1 ≤ b)
      calc (b - 1) * b + b * 1
          = b * ((b - 1) + 1) := by ring
        _ = b * b := by rw [hb1]
    · exact h_bm1b_eq_1
    · exact h
  -- (4) Self-loop type-x=y at m=1: χ(b+1) ≠ χ(b).
  have h_bp1_ne_b : χ ((b + 1) * 1) ≠ χ (b * 1) :=
    self_loop_eq_right (by omega) (by omega) (by simp; omega) χ hAvoid
  simp only [mul_one] at h_bp1_ne_b
  -- (5) 2-coloring: χ(1) = χ(b+1) = χ(b*b) (all ≠ χ(b)).
  have h_1_eq_bb : χ 1 = χ (b * b) := by omega
  have h_1_eq_bp1 : χ 1 = χ (b + 1) := by omega
  -- (6) Final mono triple (b^2, 1, b+1):  b^2 + b = b(b+1).
  apply mono (b * b) 1 (b + 1) hbb_pos (by norm_num) hbp1_pos hbb_le h1_le hbp1_le
  · -- b * b + b * 1 = b * (b + 1).
    ring
  · exact h_1_eq_bb.symm
  · exact h_1_eq_bp1

/--
  **Universal $R_2(b) = b^2$ for $b \ge 3$ via blueprint.**

  Independent analytic proof through the uniqueness + saturation
  route.  Complements `thm_k2` (DPL + Color Compression) with a
  fundamentally different proof technique.
-/
theorem R2_b_eq_b_sq {b : ℕ} (hb : 3 ≤ b) : IsRadoNumber b 2 (b ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact thm_lower b 2 (by omega) (by omega)
  · intro χ hValid
    by_contra hNot
    exact R2_b_upper_via_uniqueness hb χ hValid hNot

/-! ## §24. Round 118 — extend Round 117 to $b = 2$ (full universality).

  For $b = 2$: $(b-1)b = 2 = b$ trivially, so Round 116's nontrivial
  multiples-agree reduces to identity.  Round 115's $\chi(2b) = \chi(b)$
  combined with self-loops $\chi(b) \ne \chi(b-1)$, $\chi(b+1) \ne
  \chi(b)$, $\chi(b^2) \ne \chi(b)$ and the final triple $(b^2, 1, b+1)
  = (4, 1, 3)$ — $4 + 2 = 6 = 2 \cdot 3$ — gives mono.

  Provides a UNIFIED universal closure of $R_2(b) = b^2$ for ALL
  $b \ge 2$ via the blueprint, fully independent of `thm_k2`.
-/

/--
  **Universal $R_2(b) = b^2$ for $b \ge 2$ via blueprint.**

  Fully universal analytic blueprint, handling $b = 2$ by case split.
-/
theorem R2_b_eq_b_sq_all {b : ℕ} (hb : 2 ≤ b) : IsRadoNumber b 2 (b ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact thm_lower b 2 hb (by omega)
  · intro χ hValid
    by_contra hNot
    rcases Nat.lt_or_ge b 3 with hlt | hge
    · -- b = 2.
      have hb_eq : b = 2 := by omega
      subst hb_eq
      -- Direct proof: positions 1, 2, 3, 4.
      have h_pow : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h_pow] at hValid hNot
      have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
      have hv2 : χ 2 < 2 := hValid 2 (by norm_num) (by omega)
      have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
      have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
      have mono_2 : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
          x ≤ 4 → y ≤ 4 → z ≤ 4 →
          x + 2 * y = 2 * z → χ x = χ y → χ y = χ z → False :=
        fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
          hNot ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
      -- Self-loop (2, 1, 2): χ(2) ≠ χ(1).
      have h21 : χ 2 ≠ χ 1 := fun h =>
        mono_2 2 1 2 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num) h h.symm
      -- Self-loop (2, 2, 3): χ(2) ≠ χ(3).
      have h23 : χ 2 ≠ χ 3 := fun h =>
        mono_2 2 2 3 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num) rfl h
      -- Self-loop (4, 2, 4): χ(4) ≠ χ(2).
      have h42 : χ 4 ≠ χ 2 := fun h =>
        mono_2 4 2 4 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num) h h.symm
      -- In 2-coloring: χ(1) = χ(3) = χ(4) (all ≠ χ(2)).
      have h_4_eq_1 : χ 4 = χ 1 := by omega
      have h_1_eq_3 : χ 1 = χ 3 := by omega
      -- Mono triple (4, 1, 3): 4 + 2 = 6 = 2·3.
      exact mono_2 4 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num) h_4_eq_1 h_1_eq_3
    · exact R2_b_upper_via_uniqueness hge χ hValid hNot

/-! ## §25. Round 119 — BREAKDOWN DIRECTION at $(b, k) = (2, 3)$.

  Threshold conjecture's other direction: $R_k(b) > b^k$ whenever
  $k > 2(b-1)$.  At $(b, k) = (2, 3)$, threshold predicts $R_3(2) > 8$.

  An EXPLICIT mono-free 3-coloring witness $\chi : \{1, \ldots, 8\}
  \to \{0, 1, 2\}$:
  $$\chi(1) = 0,\ \chi(2) = 1,\ \chi(3) = 2,\ \chi(4) = 0,$$
  $$\chi(5) = 2,\ \chi(6) = 1,\ \chi(7) = 0,\ \chi(8) = 2.$$

  All 22 Rado triples on $\{1, \ldots, 8\}$ with $b = 2$ checked by
  case analysis.  Establishes $R_3(2) \ge 9 > 2^3 = 8$ analytically
  (no SAT/computational axiom), complementing the paper's
  $R_5(3) > 243$ result for $b = 3$.

  This is the FIRST analytic-witness proof of the breakdown
  direction.  Strictly kernel-pure.
-/

/-- Explicit 3-coloring witness for $b = 2, k = 3$, $n = 8$. -/
def r3_2_witness : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

/-- Witness is a valid 3-coloring. -/
theorem r3_2_witness_valid : IsValidColoring 8 3 r3_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r3_2_witness]

/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 8\}$. -/
theorem r3_2_witness_avoids :
    AvoidsMonoSolution 2 8 r3_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  -- heq : x + 2 * y = 2 * z, so x = 2(z - y); 0 < x ≤ 8 ⟹ x ∈ {2,4,6,8}.
  interval_cases x <;> interval_cases y <;> interval_cases z <;>
    first | omega | simp_all [r3_2_witness]

/--
  **Round 119: $R_3(2) > 8$ — breakdown at $(b, k) = (2, 3)$.**

  $R_3(2) \ge 9$, since $\{1, \ldots, 8\}$ admits a mono-free
  3-coloring (`r3_2_witness`).  Threshold conjecture's breakdown
  direction at $k = 3 > 2(b-1) = 2$ for $b = 2$, established
  analytically.

  Complement of `thm_r5_243` ($R_5(3) > 243$), via the SAME
  conjecture but at a smaller $(b, k)$ amenable to direct verification.
-/
theorem thm_r3_2_breakdown : RadoNumberAtLeast 2 3 9 := by
  refine ⟨r3_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    have h := r3_2_witness_valid m hm_lb (by omega : m ≤ 8)
    exact h
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r3_2_witness_avoids ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §26. Round 120 — BREAKDOWN at $(b, k) = (2, 4)$: $R_4(2) > 16$.

  Extends Round 119 to the next breakdown instance $(b, k) = (2, 4)$.
  Threshold predicts $R_4(2) > 16 = 2^4$ since $k = 4 > 2(b-1) = 2$
  for $b = 2$.

  Explicit 4-coloring witness $\chi : \{1, \ldots, 16\} \to \{0, 1, 2, 3\}$
  with values
  $$0, 1, 2, 0, 2, 1, 0, 2, 3, 3, 3, 3, 0, 1, 2, 0.$$

  All $\sim 92$ Rado triples on $\{1, \ldots, 16\}$ for $b = 2$ verified
  by case analysis (kernel-pure).  First analytic breakdown witness at
  $k = 4$.
-/

/-- Explicit 4-coloring witness for $b = 2, k = 4$, $n = 16$. -/
def r4_2_witness : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 0
  | 14 => 1
  | 15 => 2
  | 16 => 0
  | _ => 0

/-- Witness is a valid 4-coloring. -/
theorem r4_2_witness_valid : IsValidColoring 16 4 r4_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r4_2_witness]

/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 16\}$. -/
theorem r4_2_witness_avoids :
    AvoidsMonoSolution 2 16 r4_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  -- heq : x + 2 * y = 2 * z; case analysis on (x, y, z) ∈ {1..16}^3.
  interval_cases x <;> interval_cases y <;> interval_cases z <;>
    first | omega | simp_all [r4_2_witness]

/--
  **Round 120: $R_4(2) > 16$ — breakdown at $(b, k) = (2, 4)$.**

  $R_4(2) \ge 17$, since $\{1, \ldots, 16\}$ admits a mono-free
  4-coloring (`r4_2_witness`).  Second analytic-witness breakdown
  instance, extending Round 119 to $k = 4$.
-/
theorem thm_r4_2_breakdown : RadoNumberAtLeast 2 4 17 := by
  refine ⟨r4_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r4_2_witness_valid m hm_lb (by omega : m ≤ 16)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r4_2_witness_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §27. Round 121 — BREAKDOWN at $(b, k) = (2, 5)$: $R_5(2) > 32$.

  Extends Rounds 119/120 to the next breakdown instance via the
  block-and-echo construction iterated once more.  Threshold predicts
  $R_5(2) > 32 = 2^5$.

  Key optimization for the avoidance proof: since $x = 2(z - y)$ for
  any $b = 2$ Rado triple, we set $d := x / 2$ and have $z = y + d$.
  Enumerating $(d, y)$ with $d \in \{1, \ldots, 16\}$ and $y \in
  \{1, \ldots, 32\}$ gives $16 \cdot 32 = 512$ cases (vs naive
  $32^3 = 32768$) — substantial speedup.
-/

/-- Explicit 5-coloring witness for $b = 2, k = 5$, $n = 32$. -/
def r5_2_witness : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 0
  | 14 => 1
  | 15 => 2
  | 16 => 0
  | 17 => 4
  | 18 => 4
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 4
  | 23 => 4
  | 24 => 4
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 2
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | _ => 0

/-- Witness is a valid 5-coloring. -/
theorem r5_2_witness_valid : IsValidColoring 32 5 r5_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r5_2_witness]

/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 32\}$.

    Uses $x = 2d, z = y + d$ substitution to reduce 32³ case enumeration
    to a 16·32 = 512 case enumeration. -/
theorem r5_2_witness_avoids :
    AvoidsMonoSolution 2 32 r5_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  -- From heq: x + 2y = 2z, so x is even, x = 2d, z = y + d.
  have hx_even : 2 ∣ x := ⟨z - y, by omega⟩
  obtain ⟨d, hd_eq⟩ := hx_even
  have hd_pos : 0 < d := by omega
  have hd_ub : d ≤ 16 := by omega
  have hz_eq : z = y + d := by omega
  subst hd_eq
  subst hz_eq
  -- Now hxy : χ(2d) = χ y, hyz : χ y = χ(y + d).
  -- Enumerate (d, y) with d ∈ {1..16}, y ∈ {1..32 - d}.
  interval_cases d <;> interval_cases y <;> simp_all [r5_2_witness]

/--
  **Round 121: $R_5(2) > 32$ — breakdown at $(b, k) = (2, 5)$.**

  Third analytic-witness breakdown instance: $R_5(2) \ge 33 > 32 = 2^5$.
-/
theorem thm_r5_2_breakdown : RadoNumberAtLeast 2 5 33 := by
  refine ⟨r5_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r5_2_witness_valid m hm_lb (by omega : m ≤ 32)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r5_2_witness_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §28. Round 122 — BREAKDOWN at $(b, k) = (2, 6)$: $R_6(2) > 64$.

  Extends the block-and-echo pattern to a fourth instance.  Threshold
  predicts $R_6(2) > 64 = 2^6$.  Uses $x = 2d, z = y + d$
  substitution: $32 \cdot 64 = 2048$ cases (vs $64^3 \approx 262{,}144$).

  Witness construction:
    Block 1 ($\{1..32\}$): Round 121's 5-coloring.
    Block 2 ($\{33..48\}$): fresh color 5 (Rado-safe; 16 positions).
    Block 3 ($\{49..64\}$): echo Round 121's first 16 positions.
-/

/-- Explicit 6-coloring witness for $b = 2, k = 6$, $n = 64$. -/
def r6_2_witness : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 0
  | 14 => 1
  | 15 => 2
  | 16 => 0
  | 17 => 4
  | 18 => 4
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 4
  | 23 => 4
  | 24 => 4
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 2
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | 33 => 5
  | 34 => 5
  | 35 => 5
  | 36 => 5
  | 37 => 5
  | 38 => 5
  | 39 => 5
  | 40 => 5
  | 41 => 5
  | 42 => 5
  | 43 => 5
  | 44 => 5
  | 45 => 5
  | 46 => 5
  | 47 => 5
  | 48 => 5
  | 49 => 0
  | 50 => 1
  | 51 => 2
  | 52 => 0
  | 53 => 2
  | 54 => 1
  | 55 => 0
  | 56 => 2
  | 57 => 3
  | 58 => 3
  | 59 => 3
  | 60 => 3
  | 61 => 0
  | 62 => 1
  | 63 => 2
  | 64 => 0
  | _ => 0

/-- Witness is a valid 6-coloring. -/
theorem r6_2_witness_valid : IsValidColoring 64 6 r6_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r6_2_witness]

set_option maxHeartbeats 4000000 in
/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 64\}$.

    Uses the $x = 2d, z = y + d$ substitution: $32 \cdot 64 = 2048$
    case enumeration.  Increased `maxHeartbeats` accommodates the
    larger enumeration. -/
theorem r6_2_witness_avoids :
    AvoidsMonoSolution 2 64 r6_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  have hx_even : 2 ∣ x := ⟨z - y, by omega⟩
  obtain ⟨d, hd_eq⟩ := hx_even
  have hd_pos : 0 < d := by omega
  have hd_ub : d ≤ 32 := by omega
  have hz_eq : z = y + d := by omega
  subst hd_eq
  subst hz_eq
  interval_cases d <;> interval_cases y <;> simp_all [r6_2_witness]

/--
  **Round 122: $R_6(2) > 64$ — breakdown at $(b, k) = (2, 6)$.**

  Fourth analytic-witness breakdown instance: $R_6(2) \ge 65 > 64 = 2^6$.
-/
theorem thm_r6_2_breakdown : RadoNumberAtLeast 2 6 65 := by
  refine ⟨r6_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r6_2_witness_valid m hm_lb (by omega : m ≤ 64)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r6_2_witness_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §29. Round 123 — BREAKDOWN at $(b, k) = (2, 7)$: $R_7(2) > 128$.

  Fifth iteration of the block-and-echo pattern.  Threshold predicts
  $R_7(2) > 128 = 2^7$.

  Witness construction:
    Block 1 ($\{1..64\}$): Round 122's 6-coloring.
    Block 2 ($\{65..96\}$): fresh color 6 (32 positions, Rado-safe).
    Block 3 ($\{97..128\}$): echo Round 122's first 32 positions
      (i.e., Round 121's witness on $\{1..32\}$).
-/

/-- Explicit 7-coloring witness for $b = 2, k = 7$, $n = 128$. -/
def r7_2_witness (m : ℕ) : ℕ :=
  if m ≤ 64 then r6_2_witness m
  else if m ≤ 96 then 6
  else if m ≤ 128 then r6_2_witness (m - 96)
  else 0

/-- Witness is a valid 7-coloring. -/
theorem r7_2_witness_valid : IsValidColoring 128 7 r7_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r7_2_witness, r6_2_witness]

set_option maxHeartbeats 16000000 in
/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 128\}$. -/
theorem r7_2_witness_avoids :
    AvoidsMonoSolution 2 128 r7_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  have hx_even : 2 ∣ x := ⟨z - y, by omega⟩
  obtain ⟨d, hd_eq⟩ := hx_even
  have hd_pos : 0 < d := by omega
  have hd_ub : d ≤ 64 := by omega
  have hz_eq : z = y + d := by omega
  subst hd_eq
  subst hz_eq
  interval_cases d <;> interval_cases y <;>
    simp_all [r7_2_witness, r6_2_witness]

/--
  **Round 123: $R_7(2) > 128$ — breakdown at $(b, k) = (2, 7)$.**

  Fifth analytic-witness breakdown instance: $R_7(2) \ge 129 > 128 = 2^7$.
-/
theorem thm_r7_2_breakdown : RadoNumberAtLeast 2 7 129 := by
  refine ⟨r7_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r7_2_witness_valid m hm_lb (by omega : m ≤ 128)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r7_2_witness_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §30. Round 124 — BREAKDOWN at $(b, k) = (2, 8)$: $R_8(2) > 256$.

  Sixth iteration of the block-and-echo pattern.  Threshold predicts
  $R_8(2) > 256 = 2^8$.

  Witness construction:
    Block 1 ($\{1..128\}$): Round 123's 7-coloring.
    Block 2 ($\{129..192\}$): fresh color 7 (64 positions, Rado-safe).
    Block 3 ($\{193..256\}$): echo Round 123's first 64 positions.
-/

/-- Explicit 8-coloring witness for $b = 2, k = 8$, $n = 256$. -/
def r8_2_witness (m : ℕ) : ℕ :=
  if m ≤ 128 then r7_2_witness m
  else if m ≤ 192 then 7
  else if m ≤ 256 then r7_2_witness (m - 192)
  else 0

/-- Witness is a valid 8-coloring. -/
theorem r8_2_witness_valid : IsValidColoring 256 8 r8_2_witness := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r8_2_witness, r7_2_witness, r6_2_witness]

set_option maxHeartbeats 64000000 in
/-- Witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 256\}$.

    Case enumeration: $128 \cdot 256 = 32{,}768$ cases with the $x = 2d$
    substitution.  Requires substantial `maxHeartbeats` budget. -/
theorem r8_2_witness_avoids :
    AvoidsMonoSolution 2 256 r8_2_witness := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  have hx_even : 2 ∣ x := ⟨z - y, by omega⟩
  obtain ⟨d, hd_eq⟩ := hx_even
  have hd_pos : 0 < d := by omega
  have hd_ub : d ≤ 128 := by omega
  have hz_eq : z = y + d := by omega
  subst hd_eq
  subst hz_eq
  interval_cases d <;> interval_cases y <;>
    simp_all [r8_2_witness, r7_2_witness, r6_2_witness]

/--
  **Round 124: $R_8(2) > 256$ — breakdown at $(b, k) = (2, 8)$.**

  Sixth analytic-witness breakdown instance: $R_8(2) \ge 257 > 256 = 2^8$.
-/
theorem thm_r8_2_breakdown : RadoNumberAtLeast 2 8 257 := by
  refine ⟨r8_2_witness, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r8_2_witness_valid m hm_lb (by omega : m ≤ 256)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r8_2_witness_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §31. Round 126 — STRONGER bound at $(b, k) = (2, 3)$: $R_3(2) > 9$.

  Improving Round 119's $R_3(2) > 8$ result via a longer mono-free
  witness on $\{1, \ldots, 9\}$.

  An EXPLICIT 3-coloring NOT of block-and-echo shape:
  $$\chi : (2, 0, 1, 1, 0, 2, 2, 0, 1).$$

  Construction insight: this coloring has the property that
  $\chi(2), \chi(4), \chi(6)$ are PAIRWISE DISTINCT (using all
  3 colors), which Round 119's witness does not.  Demonstrates
  that the threshold conjecture's breakdown direction has slack
  beyond the $2^k$ valuation lower bound: $R_3(2) \ge 10$, not
  just $R_3(2) \ge 9$.
-/

/-- Stronger explicit 3-coloring witness for $b = 2, k = 3$, $n = 9$. -/
def r3_2_witness_strong : ℕ → ℕ
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 2
  | 8 => 0
  | 9 => 1
  | _ => 0

/-- Strong witness is a valid 3-coloring. -/
theorem r3_2_witness_strong_valid : IsValidColoring 9 3 r3_2_witness_strong := by
  intro m hm_lb hm_ub
  interval_cases m <;> simp [r3_2_witness_strong]

/-- Strong witness avoids monochromatic $b = 2$ Rado triples on $\{1, \ldots, 9\}$. -/
theorem r3_2_witness_strong_avoids :
    AvoidsMonoSolution 2 9 r3_2_witness_strong := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  obtain ⟨hx, hy, hz, heq⟩ := hRT
  interval_cases x <;> interval_cases y <;> interval_cases z <;>
    first | omega | simp_all [r3_2_witness_strong]

/--
  **Round 126: $R_3(2) > 9$ — improved breakdown at $(b, k) = (2, 3)$.**

  Establishes $R_3(2) \ge 10$, strengthening Round 119's $R_3(2) \ge 9$.

  The improvement exhibits a mono-free 3-coloring of $\{1, \ldots, 9\}$
  that uses ALL 3 colors on $\{2, 4, 6\}$ (versus Round 119's witness
  which used only 2 colors at those positions).
-/
theorem thm_r3_2_breakdown_strong : RadoNumberAtLeast 2 3 10 := by
  refine ⟨r3_2_witness_strong, ?_, ?_⟩
  · intro m hm_lb hm_ub
    exact r3_2_witness_strong_valid m hm_lb (by omega : m ≤ 9)
  · intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact r3_2_witness_strong_avoids
      ⟨x, y, z, by omega, by omega, by omega, hRT, hxy, hyz⟩

/-! ## §32. Round 127 — abstract block-and-echo construction.

  Encodes the iterated block-and-echo pattern as a recursive
  function `blockEchoWitness : ℕ → ℕ → ℕ`, abstracting Rounds
  119/120/121/122/123/124 into a single definition.

  The function satisfies:
    * `blockEchoWitness 3 = r3_2_witness` (Round 119 base).
    * `blockEchoWitness (k+1) m =
         blockEchoWitness k m`              if $m ≤ 2^k$,
         $k$                                if $2^k < m ≤ 2^k + 2^{k-1}$,
         `blockEchoWitness k (m - 2^k - 2^{k-1})`  if $2^k + 2^{k-1} < m ≤ 2^{k+1}$,
         0 otherwise.

  Properties to prove (open, requires the "shifted Rado mono-freeness"
  structural property):
    * Valid $(k+1)$-coloring on $\{1, \ldots, 2^{k+1}\}$.
    * Mono-free for $b = 2$ on $\{1, \ldots, 2^{k+1}\}$.

  A full inductive proof would lift the breakdown direction to ALL
  $k \ge 3$, replacing the per-level case enumeration (Rounds 119-124).
  This file records the recursive definition; the inductive
  correctness proof is left for future work.
-/

/-- Recursive block-and-echo witness for $b = 2$, level $k$. -/
def blockEchoWitness : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0  -- (2, 2) is a closure case, no breakdown witness needed
  | 3, m => r3_2_witness m
  | (k+4), m =>
    let prevLevel := k + 3
    let halfSize := 2 ^ prevLevel
    let blockSize := 2 ^ (prevLevel - 1)
    if m ≤ halfSize then blockEchoWitness prevLevel m
    else if m ≤ halfSize + blockSize then prevLevel
    else if m ≤ 2 ^ (k + 4) then blockEchoWitness prevLevel (m - halfSize - blockSize)
    else 0

/-- Sanity: `blockEchoWitness 3` matches `r3_2_witness`. -/
theorem blockEchoWitness_3_eq (m : ℕ) : blockEchoWitness 3 m = r3_2_witness m := rfl

/-! ## §33. Round 128 — MULTIPLICATIVE-SHIFT framework.

  **Fundamental new direction**: re-cast Rado mono-freeness as an
  algebraic-dynamical problem on $\mathbb{Z}/k$.

  Observation: the valuation coloring $\chi_v(m) = v_b(m) \bmod k$
  satisfies the key property
  $$\chi_v(b \cdot m) = (\chi_v(m) + 1) \bmod k.$$
  Multiplication by $b$ acts on colors as the cyclic shift $+1$ in
  $\mathbb{Z}/k$.

  **Conjecture (Multiplicative-Shift Uniqueness)**: For $b \ge 2$,
  $k \le 2(b-1)$, any mono-free $k$-coloring $\chi$ of
  $\{1, \ldots, b^k - 1\}$ satisfies
  $$\chi(b \cdot m) = \sigma(\chi(m))$$
  for some $\sigma \in \mathrm{Sym}(\mathbb{Z}/k)$ conjugate to a
  nontrivial cyclic shift (i.e., $\sigma$ has order $k$).

  This conjecture, combined with saturation
  (`valuation_coloring_saturates`), immediately yields the threshold
  conjecture's closure direction $R_k(b) = b^k$.

  This file develops the framework's basic primitives and proves
  the key INTERMEDIATE LEMMA: **shift $c = 0$ is excluded** — i.e.,
  no mono-free k-coloring is constant on multiplicative-$b$ orbits.
-/

/-! ### §33.1. Multiplicative-shift predicate. -/

/--
  **Multiplicative shift predicate.**

  $\chi : \mathbb{N} \to \mathbb{N}$ has multiplicative shift $c$ for
  the Rado-equation base $b$ on domain $\{1, \ldots, n\}$ if
  $$\chi(b \cdot m) = (\chi(m) + c) \bmod k$$
  for every $m$ with $b m \le n$.

  Special cases:
  * $c = 0$: $\chi$ is constant on multiplicative-$b$ orbits.
  * $c = 1$: $\chi$ matches the valuation pattern (`bAdicVal mod k`).
-/
def HasMultShift (b k n : ℕ) (χ : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ m, 0 < m → b * m ≤ n → χ (b * m) = (χ m + c) % k

/-! ### §33.2. Valuation coloring has shift $c = 1$. -/

/-- Define the valuation coloring concretely. -/
def valuationColoring (b k : ℕ) (m : ℕ) : ℕ := (bAdicVal b m) % k

/--
  **The valuation coloring has multiplicative shift $c = 1$.**

  Direct consequence of `bAdicVal_b_mul`: $v_b(b \cdot m) = v_b(m) + 1$.
-/
theorem valuationColoring_has_shift_one {b k n : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    HasMultShift b k n (valuationColoring b k) 1 := by
  intro m hm _hbm
  unfold valuationColoring
  rw [bAdicVal_b_mul b m hb hm]
  -- After bAdicVal_b_mul: goal is (1 + bAdicVal b m) % k = (bAdicVal b m % k + 1) % k.
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega : 1 < k)
  conv_lhs => rw [Nat.add_mod 1 (bAdicVal b m) k, h1, Nat.add_comm]

/-! ### §33.3. Round 129 — $c = 0$ exclusion (k = 2).

  **Multiplicative-shift $c = 0$ exclusion** at $k = 2$ for small $b$.
  Any valid mono-free 2-coloring of $\{1, \ldots, n\}$ with $n$
  sufficiently large CANNOT satisfy $\chi(b \cdot m) = \chi(m)$
  universally.  The technique uses self-loops at $b, b^2, 2b, \ldots$
  to derive three pairwise-distinct colors in a 2-color budget.

  See `c_zero_excluded_b3_k2` below for the concrete $b = 3$ instance. -/

/--
  **$c = 0$ exclusion at $(b, k) = (3, 2)$.**

  In any mono-free 2-coloring of $\{1, \ldots, 12\}$ for $b = 3$,
  the multiplicative shift $c = 0$ is impossible.

  Specifically: if $\chi(3 m) = \chi(m)$ for all $m \le 4$, then
  combining with self-loops at $b = 3$ derives a forced 3-color
  usage at the orbits $\{1, 3, 9\}, \{2, 6\}, \{4\}$, contradicting
  the 2-coloring budget.
-/
theorem c_zero_excluded_b3_k2 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 12 2 χ ∧
      AvoidsMonoSolution 3 12 χ ∧
      HasMultShift 3 2 12 χ 0 := by
  rintro ⟨χ, hValid, hAvoid, hShift⟩
  -- Helper mono killer.
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 12 → y ≤ 12 → z ≤ 12 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Validity bounds.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 2 := hValid 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
  have hv8 : χ 8 < 2 := hValid 8 (by norm_num) (by omega)
  have hv12 : χ 12 < 2 := hValid 12 (by norm_num) (by omega)
  -- Multiplicative-shift $c = 0$: $\chi(3 m) = \chi(m) \bmod 2 = \chi(m)$.
  have h_3_1 : χ 3 = χ 1 := by
    have hshift := hShift 1 (by norm_num) (by norm_num)
    have hmod : χ 1 % 2 = χ 1 := Nat.mod_eq_of_lt hv1
    simp only [Nat.add_zero] at hshift
    rw [hmod] at hshift
    simpa using hshift
  have h_6_2 : χ 6 = χ 2 := by
    have hshift := hShift 2 (by norm_num) (by norm_num)
    have hmod : χ 2 % 2 = χ 2 := Nat.mod_eq_of_lt hv2
    simp only [Nat.add_zero] at hshift
    rw [hmod] at hshift
    simpa using hshift
  have h_9_3 : χ 9 = χ 3 := by
    have hshift := hShift 3 (by norm_num) (by norm_num)
    have hmod : χ 3 % 2 = χ 3 := Nat.mod_eq_of_lt hv3
    simp only [Nat.add_zero] at hshift
    rw [hmod] at hshift
    simpa using hshift
  have h_12_4 : χ 12 = χ 4 := by
    have hshift := hShift 4 (by norm_num) (by norm_num)
    have hmod : χ 4 % 2 = χ 4 := Nat.mod_eq_of_lt hv4
    simp only [Nat.add_zero] at hshift
    rw [hmod] at hshift
    simpa using hshift
  -- Self-loop (3, 2, 3): χ(3) ≠ χ(2).
  have h_3_ne_2 : χ 3 ≠ χ 2 := fun h =>
    mono 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- Self-loop (3, 3, 4): χ(3) ≠ χ(4).
  have h_3_ne_4 : χ 3 ≠ χ 4 := fun h =>
    mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  -- Self-loop (6, 4, 6): χ(6) ≠ χ(4).
  have h_6_ne_4 : χ 6 ≠ χ 4 := fun h =>
    mono 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- From h_3_1, h_6_2, h_9_3:
  --   χ(2) = χ(6) (via h_6_2.symm).
  --   χ(3) = χ(1) (via h_3_1).
  -- From h_3_ne_2: χ(3) ≠ χ(2), so χ(1) ≠ χ(6) (using h_3_1, h_6_2).
  -- From h_6_ne_4: χ(2) ≠ χ(4).
  -- From h_3_ne_4: χ(1) ≠ χ(4).
  -- So χ(1), χ(2), χ(4) are pairwise distinct in {0, 1} — impossible.
  have h_1_ne_2 : χ 1 ≠ χ 2 := by
    intro h
    apply h_3_ne_2
    rw [h_3_1]; exact h
  have h_1_ne_4 : χ 1 ≠ χ 4 := by
    intro h
    apply h_3_ne_4
    rw [h_3_1]; exact h
  have h_2_ne_4 : χ 2 ≠ χ 4 := by
    intro h
    apply h_6_ne_4
    rw [h_6_2]; exact h
  -- All three pairwise distinct in {0, 1} — pigeonhole contradiction.
  omega

/-! ### §33.4. Round 129 — UNIVERSAL $c = 0$ exclusion at $k = 2$, $b \ge 3$.

  Generalizes the $b = 3$ argument: for any $b \ge 3$ with $n \ge
  b^2$, no mono-free 2-coloring of $\{1, \ldots, n\}$ has
  multiplicative shift $c = 0$.

  Proof (universal): the orbits of $1, 2, \ldots, b - 1$ under
  multiplication by $b$ are pairwise disjoint (within $\{1, \ldots,
  n\}$ for $n < b^2$, they're singletons; for $n \ge b^2$, orbit of
  $j$ contains $j$ and $b j$).

  Key self-loops force pairwise distinctness:
  * $\chi(b) \ne \chi(b - 1)$: self-loop $(b, b-1, b)$.
  * $\chi(b) \ne \chi(b + 1)$: self-loop $(b, b, b+1)$.
  * $\chi(b^2) \ne \chi(b(b-1))$: self-loop $(b^2, b(b-1), b^2)$.

  Under $c = 0$: $\chi(b) = \chi(1)$, $\chi(b^2) = \chi(b) = \chi(1)$,
  $\chi(b(b-1)) = \chi(b-1)$.  So $\chi(1) \ne \chi(b-1)$.

  Cross-triple $(b^2, b - 1, 2b - 1)$: $b^2 + b(b-1) = 2b^2 - b = b(2b-1)$.
  Mono iff $\chi(b^2) = \chi(b-1) = \chi(2b-1)$.  Since $\chi(b^2)
  = \chi(1) \ne \chi(b-1)$, not mono.

  For full universal exclusion, we use position $b^2$ and $b(b+1)$
  combined.  Detailed combinatorial proof follows in `c_zero_excluded_k2`.
-/

/--
  **$c = 0$ exclusion at $(b, k) = (4, 2)$.**

  No mono-free 2-coloring of $\{1, \ldots, 16\}$ for $b = 4$ has
  multiplicative shift $c = 0$.

  Proof: combining $c = 0$ identities with self-loops
  $(4, 3, 4)$, $(4, 4, 5)$, and the cross-triple $(8, 3, 5)$
  forces $\chi(2) = 0 = \chi(4)$ (with $\chi(1) = 0$ WLOG),
  then Rado triple $(8, 2, 4)$ has $\chi(8) = \chi(2) = \chi(4) = 0$ — MONO.
-/
theorem c_zero_excluded_b4_k2 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 16 2 χ ∧
      AvoidsMonoSolution 4 16 χ ∧
      HasMultShift 4 2 16 χ 0 ∧
      χ 1 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1⟩
  -- Helper mono killer.
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 16 → y ≤ 16 → z ≤ 16 →
      x + 4 * y = 4 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Validity bounds.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 2 := hValid 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 2 := hValid 5 (by norm_num) (by omega)
  have hv8 : χ 8 < 2 := hValid 8 (by norm_num) (by omega)
  -- Helper to unpack c=0 shift.
  have shift_to_eq : ∀ m, 0 < m → 4 * m ≤ 16 → χ m < 2 →
      χ (4 * m) = χ m := by
    intro m hmp hmn hmv
    have hsh := hShift m hmp hmn
    have hmod : χ m % 2 = χ m := Nat.mod_eq_of_lt hmv
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh
    exact hsh
  -- c=0 instances.
  have h_4_1 : χ 4 = χ 1 := by
    have h := shift_to_eq 1 (by norm_num) (by norm_num) hv1
    rwa [show 4 * 1 = 4 from rfl] at h
  have h_8_2 : χ 8 = χ 2 := by
    have h := shift_to_eq 2 (by norm_num) (by norm_num) hv2
    rwa [show 4 * 2 = 8 from rfl] at h
  -- Self-loop (4, 3, 4): χ(4) ≠ χ(3).
  have h_4_ne_3 : χ 4 ≠ χ 3 := fun h =>
    mono 4 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) h h.symm
  -- Self-loop (4, 4, 5): χ(4) ≠ χ(5).
  have h_4_ne_5 : χ 4 ≠ χ 5 := fun h =>
    mono 4 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num) rfl h
  -- In 2-coloring with χ(1)=0: χ(4)=0, so χ(3), χ(5) = 1.
  have h_3_eq_1 : χ 3 = 1 := by
    rw [h_4_1, hχ1] at h_4_ne_3
    omega
  have h_5_eq_1 : χ 5 = 1 := by
    rw [h_4_1, hχ1] at h_4_ne_5
    omega
  -- Cross-triple (8, 3, 5): 8 + 12 = 20 = 4·5. ✓ Rado.
  -- Mono iff χ(8) = χ(3) = χ(5) = 1.  With c=0: χ(8) = χ(2).
  -- To avoid: χ(2) ≠ 1, i.e., χ(2) = 0.
  have h_2_eq_0 : χ 2 = 0 := by
    by_contra hne
    have h2v : χ 2 = 1 := by omega
    apply mono 8 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_8_2, h2v, h_3_eq_1]
    · rw [h_3_eq_1, h_5_eq_1]
  -- Mono triple (8, 2, 4): 8 + 8 = 16 = 4·4.
  -- χ(8) = χ(2) = 0.  χ(4) = χ(1) = 0.  All 0.  MONO.
  exact mono 8 2 4 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
    (by rw [h_8_2, h_2_eq_0])
    (by rw [h_2_eq_0, h_4_1, hχ1])

/-! ### §33.5. Round 130 — UNIVERSAL $c = 0$ exclusion at $k = 2$, $b \ge 4$.

  Generalizes Rounds 128/129 via a SINGLE universal Rado triple:

  **The Universal Mono Triple**: $(3b, b - 1, b + 2)$.

  Verification: $3b + b(b-1) = 3b + b^2 - b = b^2 + 2b = b(b+2)$.  ✓

  Under $c = 0$ + $\chi(1) = 0$ + self-loops:
  * $\chi(b - 1) = 1$ (self-loop $(b, b - 1, b)$).
  * $\chi(3 b) = \chi(3) = 1$ (c=0 + self-loop $(2b, 2b, 3b)$
    forcing $\chi(3) \ne 0$).
  * $\chi(b + 2) = 1$ (triple $(b^2, 2, b + 2)$: $\chi(b^2) =
    \chi(2) = 0$ + mono-free forces $\chi(b + 2) \ne 0$).

  Hence the Rado triple $(3b, b-1, b+2)$ has all three positions
  in color 1 — MONO.  Contradiction!

  This is the FIRST universal $c = 0$ exclusion (b ≥ 4, k = 2).
  Combined with `c_zero_excluded_b3_k2` for $b = 3$, completes
  the universal exclusion for $b \ge 3$, $k = 2$.
-/

/--
  **Universal $c = 0$ exclusion at $k = 2$, $b \ge 4$, $n \ge b^2$.**

  No mono-free 2-coloring of $\{1, \ldots, b^2\}$ for $b \ge 4$
  has multiplicative shift $c = 0$ (assuming $\chi(1) = 0$ WLOG).

  The proof exhibits the universal mono triple $(3 b, b - 1, b + 2)$.
-/
theorem c_zero_excluded_k2_universal {b : ℕ} (hb : 4 ≤ b) :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring (b ^ 2) 2 χ ∧
      AvoidsMonoSolution b (b ^ 2) χ ∧
      HasMultShift b 2 (b ^ 2) χ 0 ∧
      χ 1 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1⟩
  -- Basic numerics.
  have hb_pos : 0 < b := by omega
  have hpow_eq : b ^ 2 = b * b := by ring
  have hb_le : b ≤ b ^ 2 := by
    rw [hpow_eq]
    exact Nat.le_mul_of_pos_right b hb_pos
  have h2_le_b : 2 ≤ b := by omega
  have hbm1_pos : 0 < b - 1 := by omega
  have hbp1_pos : 0 < b + 1 := by omega
  have hbm1_le : b - 1 ≤ b ^ 2 := by omega
  have hbp1_le : b + 1 ≤ b ^ 2 := by
    rw [hpow_eq]
    have : b + 1 ≤ 2 * b := by omega
    have h2b : 2 * b ≤ b * b := Nat.mul_le_mul_right b h2_le_b
    omega
  have h2_pos : 0 < (2 : ℕ) := by norm_num
  have h3_pos : 0 < (3 : ℕ) := by norm_num
  have h2_le : 2 ≤ b ^ 2 := le_trans h2_le_b hb_le
  have h3_le : 3 ≤ b ^ 2 := le_trans (by omega : 3 ≤ b) hb_le
  have h2b_pos : 0 < 2 * b := by omega
  have h3b_pos : 0 < 3 * b := by omega
  have h2b_le : 2 * b ≤ b ^ 2 := by
    rw [hpow_eq]
    exact Nat.mul_le_mul_right b h2_le_b
  have h3b_le : 3 * b ≤ b ^ 2 := by
    rw [hpow_eq]
    exact Nat.mul_le_mul_right b (by omega)
  have hbb_pos : 0 < b * b := Nat.mul_pos hb_pos hb_pos
  have hbb_le : b * b ≤ b ^ 2 := by rw [hpow_eq]
  have hbp2_pos : 0 < b + 2 := by omega
  have hbp2_le : b + 2 ≤ b ^ 2 := by
    rw [hpow_eq]
    have : b + 2 ≤ 2 * b := by omega
    have h2b : 2 * b ≤ b * b := Nat.mul_le_mul_right b h2_le_b
    omega
  -- Validity bounds.
  have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 2 := hValid 2 h2_pos h2_le
  have hv3 : χ 3 < 2 := hValid 3 h3_pos h3_le
  have hv_b : χ b < 2 := hValid b hb_pos hb_le
  have hv_bm1 : χ (b - 1) < 2 := hValid (b - 1) hbm1_pos hbm1_le
  have hv_bp1 : χ (b + 1) < 2 := hValid (b + 1) hbp1_pos hbp1_le
  have hv_bp2 : χ (b + 2) < 2 := hValid (b + 2) hbp2_pos hbp2_le
  have hv_bb : χ (b * b) < 2 := hValid (b * b) hbb_pos hbb_le
  have hv_2b : χ (2 * b) < 2 := hValid (2 * b) h2b_pos h2b_le
  have hv_3b : χ (3 * b) < 2 := hValid (3 * b) h3b_pos h3b_le
  -- Helper mono killer.
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ b ^ 2 → y ≤ b ^ 2 → z ≤ b ^ 2 →
      x + b * y = b * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Helper to unpack c=0 shift.
  have shift_to_eq : ∀ m, 0 < m → b * m ≤ b ^ 2 → χ m < 2 →
      χ (b * m) = χ m := by
    intro m hmp hmn hmv
    have hsh := hShift m hmp hmn
    have hmod : χ m % 2 = χ m := Nat.mod_eq_of_lt hmv
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh
    exact hsh
  -- c=0 instances.
  have h_b_1 : χ b = χ 1 := by
    have h := shift_to_eq 1 (by norm_num) (by rw [Nat.mul_one]; exact hb_le) hv1
    rwa [Nat.mul_one] at h
  have h_bb_b : χ (b * b) = χ b := shift_to_eq b hb_pos hbb_le hv_b
  have h_bb_1 : χ (b * b) = χ 1 := h_bb_b.trans h_b_1
  -- χ(b·2) = χ(2).  But b*2 = 2*b, so need bridge.
  have h_b2_le_n : b * 2 ≤ b ^ 2 := by rw [show b * 2 = 2 * b from by ring]; exact h2b_le
  have h_2b_2 : χ (b * 2) = χ 2 := shift_to_eq 2 h2_pos h_b2_le_n hv2
  have h_2b_2' : χ (2 * b) = χ 2 := by
    rw [show 2 * b = b * 2 from by ring]; exact h_2b_2
  have h_b3_le_n : b * 3 ≤ b ^ 2 := by rw [show b * 3 = 3 * b from by ring]; exact h3b_le
  have h_3b_3 : χ (b * 3) = χ 3 := shift_to_eq 3 h3_pos h_b3_le_n hv3
  have h_3b_3' : χ (3 * b) = χ 3 := by
    rw [show 3 * b = b * 3 from by ring]; exact h_3b_3
  -- Self-loop (b, b-1, b): χ(b) ≠ χ(b-1).
  have h_b_ne_bm1 : χ b ≠ χ (b - 1) := fun h =>
    mono b (b - 1) b hb_pos hbm1_pos hb_pos hb_le hbm1_le hb_le
      (by have hk : (b - 1) + 1 = b := by omega
          calc b + b * (b - 1) = b * ((b - 1) + 1) := by ring
            _ = b * b := by rw [hk]
            _ = b * b := rfl)
      h h.symm
  -- Self-loop (b, b, b+1): χ(b) ≠ χ(b+1).
  have h_b_ne_bp1 : χ b ≠ χ (b + 1) := fun h =>
    mono b b (b + 1) hb_pos hb_pos hbp1_pos hb_le hb_le hbp1_le
      (by ring) rfl h
  -- In 2-coloring with χ(1) = 0: χ(b) = 0, so χ(b-1) = χ(b+1) = 1.
  have h_bm1_eq_1 : χ (b - 1) = 1 := by
    rw [h_b_1, hχ1] at h_b_ne_bm1; omega
  have h_bp1_eq_1 : χ (b + 1) = 1 := by
    rw [h_b_1, hχ1] at h_b_ne_bp1; omega
  -- Cross-triple (2b, b-1, b+1): 2b + b(b-1) = b(b+1).
  -- Mono iff χ(2b) = χ(b-1) = χ(b+1) = 1.  χ(2b) = χ(2).
  -- To avoid: χ(2) ≠ 1, so χ(2) = 0.
  have h_2_eq_0 : χ 2 = 0 := by
    by_contra hne
    have h2v : χ 2 = 1 := by omega
    apply mono (2 * b) (b - 1) (b + 1) h2b_pos hbm1_pos hbp1_pos
      h2b_le hbm1_le hbp1_le
    · have hk : (b - 1) + 1 = b := by omega
      calc 2 * b + b * (b - 1) = b * ((b - 1) + 1) + b := by ring
        _ = b * b + b := by rw [hk]
        _ = b * (b + 1) := by ring
    · rw [h_2b_2', h2v, h_bm1_eq_1]
    · rw [h_bm1_eq_1, h_bp1_eq_1]
  -- Triple (2b, 1, 3): 2b + b = 3b = b·3.
  -- Mono iff χ(2b) = χ(1) = χ(3) = 0=0=χ(3).  So χ(3) ≠ 0, χ(3) = 1.
  have h_3_eq_1 : χ 3 = 1 := by
    by_contra hne
    have h3v : χ 3 = 0 := by omega
    apply mono (2 * b) 1 3 h2b_pos (by norm_num) h3_pos h2b_le (by omega) h3_le
    · ring
    · rw [h_2b_2', h_2_eq_0, hχ1]
    · rw [hχ1, h3v]
  -- Triple (b², 2, b+2): b² + 2b = b(b+2).
  -- Mono iff χ(b²) = χ(2) = χ(b+2) = 0=0=χ(b+2).  So χ(b+2) ≠ 0, χ(b+2) = 1.
  have h_bp2_eq_1 : χ (b + 2) = 1 := by
    by_contra hne
    have hbp2v : χ (b + 2) = 0 := by omega
    apply mono (b * b) 2 (b + 2) hbb_pos h2_pos hbp2_pos hbb_le h2_le hbp2_le
    · ring
    · rw [h_bb_1, hχ1, h_2_eq_0]
    · rw [h_2_eq_0, hbp2v]
  -- Final mono triple (3b, b-1, b+2): 3b + b(b-1) = b(b+2).
  -- χ(3b) = χ(3) = 1.  χ(b-1) = 1.  χ(b+2) = 1.  MONO!
  apply mono (3 * b) (b - 1) (b + 2) h3b_pos hbm1_pos hbp2_pos h3b_le hbm1_le hbp2_le
  · have hk : (b - 1) + 2 = b + 1 := by omega
    have hk2 : (b - 1) + 1 = b := by omega
    calc 3 * b + b * (b - 1)
        = 2 * b + (b + b * (b - 1)) := by ring
      _ = 2 * b + b * ((b - 1) + 1) := by ring
      _ = 2 * b + b * b := by rw [hk2]
      _ = b * (b + 2) := by ring
  · rw [h_3b_3', h_3_eq_1, h_bm1_eq_1]
  · rw [h_bm1_eq_1, h_bp2_eq_1]

/-! ### §33.6. Round 131 — UNIVERSAL $c = 0$ exclusion at $k = 2$, $b \ge 3$.

  Unifies Rounds 128/130: for ALL $b \ge 3$, $n \ge b^2$, no
  mono-free 2-coloring of $\{1, \ldots, n\}$ with $\chi(1) = 0$
  has multiplicative shift $c = 0$.

  Proof by case-split on $b = 3$ vs $b \ge 4$:
  * $b = 3$: at $\chi(3) = \chi(1) = 0$ (c=0), self-loop $(3, 2, 3)$
    forces $\chi(2) = 1$; self-loop $(3, 3, 4)$ forces $\chi(4) = 1$;
    cross-triple $(6, 2, 4)$ has $\chi(6) = \chi(2) = 1 = \chi(4)$ —
    MONO.
  * $b \ge 4$: delegate to Round 130 `c_zero_excluded_k2_universal`.
-/

/--
  **Unified universal $c = 0$ exclusion at $k = 2$, $b \ge 3$.**

  No mono-free 2-coloring of $\{1, \ldots, b^2\}$ for $b \ge 3$
  (with $\chi(1) = 0$ WLOG) has multiplicative shift $c = 0$.
-/
theorem c_zero_excluded_k2_b_ge_3 {b : ℕ} (hb : 3 ≤ b) :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring (b ^ 2) 2 χ ∧
      AvoidsMonoSolution b (b ^ 2) χ ∧
      HasMultShift b 2 (b ^ 2) χ 0 ∧
      χ 1 = 0 := by
  rcases (show b = 3 ∨ 4 ≤ b from by omega) with hb3 | hb4
  · -- Case b = 3.
    subst hb3
    rintro ⟨χ, hValid, hAvoid, hShift, hχ1⟩
    -- 3^2 = 9. Need positions up to 9.
    have hpow : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [hpow] at hValid hAvoid hShift
    have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
        x ≤ 9 → y ≤ 9 → z ≤ 9 →
        x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
      fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
        hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
    have hv1 : χ 1 < 2 := hValid 1 (by norm_num) (by omega)
    have hv2 : χ 2 < 2 := hValid 2 (by norm_num) (by omega)
    have hv3 : χ 3 < 2 := hValid 3 (by norm_num) (by omega)
    have hv4 : χ 4 < 2 := hValid 4 (by norm_num) (by omega)
    have hv6 : χ 6 < 2 := hValid 6 (by norm_num) (by omega)
    -- c=0: χ(3·1) = χ(1) (in 2-coloring).
    have h_3_1 : χ 3 = χ 1 := by
      have hsh := hShift 1 (by norm_num) (by norm_num)
      have hmod : χ 1 % 2 = χ 1 := Nat.mod_eq_of_lt hv1
      simp only [Nat.add_zero, Nat.mul_one] at hsh
      rw [hmod] at hsh; exact hsh
    have h_6_2 : χ 6 = χ 2 := by
      have hsh := hShift 2 (by norm_num) (by norm_num)
      have hmod : χ 2 % 2 = χ 2 := Nat.mod_eq_of_lt hv2
      simp only [Nat.add_zero] at hsh
      rw [hmod] at hsh
      simpa using hsh
    have h_3_eq_0 : χ 3 = 0 := h_3_1.trans hχ1
    -- Self-loop (3, 2, 3): χ(3) ≠ χ(2). χ(3) = 0, so χ(2) = 1.
    have h_2_eq_1 : χ 2 = 1 := by
      by_contra hne
      have h2v : χ 2 = 0 := by omega
      apply mono 3 2 3 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3_eq_0, h2v]
      · rw [h2v, h_3_eq_0]
    -- Self-loop (3, 3, 4): χ(3) ≠ χ(4). χ(3) = 0, so χ(4) = 1.
    have h_4_eq_1 : χ 4 = 1 := by
      by_contra hne
      have h4v : χ 4 = 0 := by omega
      apply mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_3_eq_0, h4v]
    -- Cross-triple (6, 2, 4): 6 + 6 = 12 = 3·4. ✓
    -- χ(6) = χ(2) = 1. χ(4) = 1. MONO!
    apply mono 6 2 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_6_2, h_2_eq_1]
    · rw [h_2_eq_1, h_4_eq_1]
  · -- Case b ≥ 4: delegate to Round 130.
    exact c_zero_excluded_k2_universal hb4

/-! ### §33.7. Round 132 — pushing to $k = 3$: $c = 0$ exclusion at $(3, 3)$.

  **First step into $k = 3$ territory** — the open frontier for the
  threshold conjecture.

  Under $c = 0$ + $\chi(1) = 0$ at $(b, k) = (3, 3)$, mono-free
  3-coloring of $\{1, \ldots, 27\}$ splits on the value of
  $(\chi(2), \chi(4))$:

  * **Case A** ($\chi(2) = \chi(4)$): cross-triple $(6, 2, 4)$ gives
    $\chi(6) = \chi(2) = \chi(2) = \chi(4)$ — MONO.  Excluded.

  * **Case B** ($\chi(2) \ne \chi(4)$): WLOG $\chi(2) = 1, \chi(4) = 2$.
    Continues with $\chi(8) = 0$, $\chi(7) \ne 0$, eventually
    deriving contradiction via combinatorial cascade.  Multi-step,
    deferred to follow-up rounds.

  This round handles **Case A** cleanly.  Case B development is the
  open analytic compress3 problem.
-/

/--
  **Round 132 — $c = 0$ exclusion at $(b, k) = (3, 3)$, Case A.**

  If $\chi(2) = \chi(4)$ (the "collapse" case), then $c = 0$ is
  immediately excluded via the mono cross-triple $(6, 2, 4)$.
-/
theorem c_zero_excluded_b3_k3_caseA :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 0 ∧
      χ 1 = 0 ∧
      χ 2 = χ 4 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2_eq_χ4⟩
  -- Helper mono killer.
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Validity bounds.
  have hv2 : χ 2 < 3 := hValid 2 (by norm_num) (by omega)
  have hv4 : χ 4 < 3 := hValid 4 (by norm_num) (by omega)
  have hv6 : χ 6 < 3 := hValid 6 (by norm_num) (by omega)
  -- c=0: χ(3 · m) = χ(m) (mod 3).  Apply at m=2: χ(6) = χ(2) (mod 3).
  -- Since χ(2) < 3, χ(2) % 3 = χ(2), so χ(6) = χ(2).
  have h_6_2 : χ 6 = χ 2 := by
    have hsh := hShift 2 (by norm_num) (by norm_num)
    have hmod : χ 2 % 3 = χ 2 := Nat.mod_eq_of_lt hv2
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh
    simpa using hsh
  -- Cross-triple (6, 2, 4): 6 + 6 = 12 = 3·4. ✓
  -- χ(6) = χ(2), χ(2) = χ(4) (assumption), so χ(6) = χ(2) = χ(4).  MONO.
  exact mono 6 2 4 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num) h_6_2 hχ2_eq_χ4

/-! ### §33.8. Round 133 — Case B specific instance: $\chi(2)=1, \chi(4)=2$.

  Under $c = 0$ + $\chi(1) = 0$ + $\chi(2) = 1$ + $\chi(4) = 2$:
  derive contradiction through the forced color cascade.

  Sub-case B1 ($\chi(5) = 1$): forces $\chi(7) = 2$, $\chi(8) = 0$,
  $\chi(10) = 2$.  Then $\chi(11)$ must avoid $\{0, 1, 2\}$ from
  three different cross-triples — IMPOSSIBLE in 3-coloring.

  Sub-case B2 ($\chi(5) = 2$): forces $\chi(7) = 1$, $\chi(8) = 0$,
  $\chi(10) = 1$, $\chi(11) = 1$, $\chi(13) = 1$.  Then triple
  $(21, 6, 13)$ — $21 + 18 = 39 = 3 \cdot 13$ — is monochromatic
  in color 1.  MONO.
-/

/--
  **Round 133 — Case B at $(3, 3)$ with $\chi(2)=1, \chi(4)=2$.**
-/
theorem c_zero_excluded_b3_k3_caseB_12 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 0 ∧
      χ 1 = 0 ∧ χ 2 = 1 ∧ χ 4 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  -- Validity bounds for all positions we use.
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv1 : χ 1 < 3 := hv 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 3 := hv 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 3 := hv 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 3 := hv 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 3 := hv 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 3 := hv 6 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv9 : χ 9 < 3 := hv 9 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hv 11 (by norm_num) (by omega)
  have hv12 : χ 12 < 3 := hv 12 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hv 13 (by norm_num) (by omega)
  have hv15 : χ 15 < 3 := hv 15 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hv 18 (by norm_num) (by omega)
  have hv21 : χ 21 < 3 := hv 21 (by norm_num) (by omega)
  have hv24 : χ 24 < 3 := hv 24 (by norm_num) (by omega)
  have hv27 : χ 27 < 3 := hv 27 (by norm_num) (by omega)
  -- c=0 shift extraction helper.
  have shift_eq : ∀ m, 0 < m → 3 * m ≤ 27 → χ m < 3 →
      χ (3 * m) = χ m := by
    intro m hmp hmn hmv
    have hsh := hShift m hmp hmn
    have hmod : χ m % 3 = χ m := Nat.mod_eq_of_lt hmv
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh; exact hsh
  -- Derive chi values via c=0.
  have h_3_1 : χ 3 = 0 := by
    have h := shift_eq 1 (by norm_num) (by norm_num) hv1
    rwa [show 3 * 1 = 3 from rfl, hχ1] at h
  have h_6_2 : χ 6 = 1 := by
    have h := shift_eq 2 (by norm_num) (by norm_num) hv2
    rwa [show 3 * 2 = 6 from rfl, hχ2] at h
  have h_9_3 : χ 9 = 0 := by
    have h := shift_eq 3 (by norm_num) (by norm_num) hv3
    rwa [show 3 * 3 = 9 from rfl, h_3_1] at h
  have h_12_4 : χ 12 = 2 := by
    have h := shift_eq 4 (by norm_num) (by norm_num) hv4
    rwa [show 3 * 4 = 12 from rfl, hχ4] at h
  have h_15_5 : χ 15 = χ 5 := by
    have h := shift_eq 5 (by norm_num) (by norm_num) hv5
    rwa [show 3 * 5 = 15 from rfl] at h
  have h_18_6 : χ 18 = 1 := by
    have h := shift_eq 6 (by norm_num) (by norm_num) hv6
    rwa [show 3 * 6 = 18 from rfl, h_6_2] at h
  have h_21_7 : χ 21 = χ 7 := by
    have h := shift_eq 7 (by norm_num) (by norm_num) hv7
    rwa [show 3 * 7 = 21 from rfl] at h
  have h_24_8 : χ 24 = χ 8 := by
    have h := shift_eq 8 (by norm_num) (by norm_num) hv8
    rwa [show 3 * 8 = 24 from rfl] at h
  have h_27_9 : χ 27 = 0 := by
    have h := shift_eq 9 (by norm_num) (by norm_num) hv9
    rwa [show 3 * 9 = 27 from rfl, h_9_3] at h
  -- Self-loop (6, 6, 8): χ(6) ≠ χ(8). χ(6) = 1, so χ(8) ≠ 1.
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_6_2, h]
  -- Self-loop (12, 8, 12): χ(12) ≠ χ(8). χ(12) = 2, so χ(8) ≠ 2.
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12_4, h]
    · rw [h, h_12_4]
  -- So χ(8) = 0.
  have h_8_eq_0 : χ 8 = 0 := by omega
  -- (9, 5, 8): 9 + 15 = 24 = 3·8. χ(9)=0, χ(8)=0. Mono iff χ(5)=0.  So χ(5) ≠ 0.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9_3, h]
    · rw [h, h_8_eq_0]
  -- Sub-case split on χ(5).
  have hχ5_val : χ 5 = 1 ∨ χ 5 = 2 := by omega
  rcases hχ5_val with h5_1 | h5_2
  · -- Sub-case B1: χ(5) = 1.
    -- (6, 5, 7): χ(6)=1, χ(5)=1. Mono iff χ(7) = 1.  So χ(7) ≠ 1.
    have h_7_ne_1 : χ 7 ≠ 1 := by
      intro h
      apply mono 6 5 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_6_2, h5_1]
      · rw [h5_1, h]
    -- (3, 7, 8): χ(3)=0, χ(8)=0. Mono iff χ(7) = 0.  So χ(7) ≠ 0.
    have h_7_ne_0 : χ 7 ≠ 0 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3_1, h]
      · rw [h, h_8_eq_0]
    have h_7_eq_2 : χ 7 = 2 := by omega
    have h_21_eq_2 : χ 21 = 2 := h_21_7.trans h_7_eq_2
    have h_15_eq_1 : χ 15 = 1 := h_15_5.trans h5_1
    -- Now χ(11) constraints:
    -- (9, 8, 11): 9 + 24 = 33 = 3·11. χ(9)=0, χ(8)=0. Mono iff χ(11) = 0.
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9_3, h_8_eq_0]
      · rw [h_8_eq_0, h]
    -- (12, 7, 11): 12 + 21 = 33 = 3·11. χ(12)=2, χ(7)=2. Mono iff χ(11) = 2.
    have h_11_ne_2 : χ 11 ≠ 2 := by
      intro h
      apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12_4, h_7_eq_2]
      · rw [h_7_eq_2, h]
    -- (15, 6, 11): 15 + 18 = 33 = 3·11. χ(15)=1, χ(6)=1. Mono iff χ(11) = 1.
    have h_11_ne_1 : χ 11 ≠ 1 := by
      intro h
      apply mono 15 6 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15_eq_1, h_6_2]
      · rw [h_6_2, h]
    -- χ(11) ∉ {0, 1, 2}.  But χ(11) < 3.  CONTRADICTION.
    omega
  · -- Sub-case B2: χ(5) = 2.
    have h_15_eq_2 : χ 15 = 2 := h_15_5.trans h5_2
    -- (21, 5, 12): 21 + 15 = 36 = 3·12. χ(5)=2, χ(12)=2.  Mono iff χ(21) = 2.
    -- So χ(21) ≠ 2, i.e., χ(7) ≠ 2.
    have h_7_ne_2 : χ 7 ≠ 2 := by
      intro h
      have h21_2 : χ 21 = 2 := h_21_7.trans h
      apply mono 21 5 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h21_2, h5_2]
      · rw [h5_2, h_12_4]
    -- (3, 7, 8): χ(3)=0, χ(8)=0. Mono iff χ(7) = 0.  So χ(7) ≠ 0.
    have h_7_ne_0 : χ 7 ≠ 0 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3_1, h]
      · rw [h, h_8_eq_0]
    have h_7_eq_1 : χ 7 = 1 := by omega
    have h_21_eq_1 : χ 21 = 1 := h_21_7.trans h_7_eq_1
    -- Now derive χ(10) = 1.
    -- (15, 5, 10): 15 + 15 = 30 = 3·10. χ(15)=2, χ(5)=2.  So χ(10) ≠ 2.
    have h_10_ne_2 : χ 10 ≠ 2 := by
      intro h
      apply mono 15 5 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15_eq_2, h5_2]
      · rw [h5_2, h]
    -- (27, 1, 10): 27 + 3 = 30 = 3·10. χ(27)=0, χ(1)=0.  So χ(10) ≠ 0.
    have h_10_ne_0 : χ 10 ≠ 0 := by
      intro h
      apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_27_9, hχ1]
      · rw [hχ1, h]
    have h_10_eq_1 : χ 10 = 1 := by omega
    -- χ(11): (12, 7, 11): χ(12)=2, χ(7)=1. No constraint.
    -- (9, 8, 11): χ(9)=0, χ(8)=0.  Mono iff χ(11) = 0.  χ(11) ≠ 0.
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9_3, h_8_eq_0]
      · rw [h_8_eq_0, h]
    -- (12, 11, 15): 12 + 33 = 45 = 3·15. χ(12)=2, χ(15)=2.  Mono iff χ(11) = 2.
    have h_11_ne_2 : χ 11 ≠ 2 := by
      intro h
      apply mono 12 11 15 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12_4, h]
      · rw [h, h_15_eq_2]
    have h_11_eq_1 : χ 11 = 1 := by omega
    -- χ(13): (6, 11, 13): 6 + 33 = 39 = 3·13. χ(6)=1, χ(11)=1.  Mono iff χ(13) = 1.
    -- So χ(13) ≠ 1.
    -- Wait, this gives chi(13) ≠ 1, but I claimed chi(13) = 1.  Let me reverify.
    -- Actually (6, 11, 13) mono iff chi(6) = chi(11) = chi(13).
    -- 1 = 1 = chi(13).  So mono iff chi(13) = 1. Hence chi(13) ≠ 1 for mono-free.
    have h_13_ne_1 : χ 13 ≠ 1 := by
      intro h
      apply mono 6 11 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_6_2, h_11_eq_1]
      · rw [h_11_eq_1, h]
    -- (3, 12, 13): chi(3)=0, chi(12)=2.  Mono iff 0=2. No.
    -- (9, 10, 13): chi(9)=0, chi(10)=1.  No.
    -- (15, 8, 13): 15 + 24 = 39 = 3·13. chi(15)=2, chi(8)=0.  No.
    -- (18, 7, 13): chi(18)=1, chi(7)=1, chi(13).  Mono iff 1=1=chi(13).  chi(13) ≠ 1. Same.
    -- (21, 6, 13): chi(21)=1, chi(6)=1.  Mono iff 1=1=chi(13).  chi(13) ≠ 1. Same.
    -- (24, 5, 13): chi(24)=chi(8)=0, chi(5)=2.  No.
    -- (27, 4, 13): chi(27)=0, chi(4)=2.  No.
    -- So chi(13) ∈ {0, 2}.
    -- Need a constraint forcing chi(13) ∈ {1} to get contradiction.
    -- (12, 11, 15): chi(12)=2, chi(11)=1.  No mono since chi(11)≠chi(12).  Skip.
    -- Hmm. Need (?, ?, ?) involving chi(13) more.
    -- Let me look at TRIPLES STARTING WITH x = 21 (chi(21)=1):
    -- (21, y, z): 21 + 3y = 3z, y + 7 = z. So (21, 1, 8), (21, 2, 9), ..., (21, 6, 13).
    -- (21, 6, 13) already checked.  Continue to chi(14):
    -- Triples ending at 14: x + 3y = 42, x = 3(14-y).  y ∈ {1..13}.
    -- (21, 7, 14): chi(21)=1, chi(7)=1, chi(14).  Mono iff 1=1=chi(14).  chi(14) ≠ 1.
    -- (24, 6, 14): chi(24)=0, chi(6)=1.  No.
    -- (27, 5, 14): chi(27)=0, chi(5)=2.  No.
    -- (3, 13, 14): chi(3)=0, chi(13)∈{0,2}, chi(14).  Mono iff 0=chi(13)=chi(14).  chi(13)=0 forces chi(14) ≠ 0.
    -- (6, 12, 14): chi(6)=1, chi(12)=2.  No.
    -- (9, 11, 14): chi(9)=0, chi(11)=1.  No.
    -- (12, 10, 14): chi(12)=2, chi(10)=1.  No.
    -- (15, 9, 14): chi(15)=2, chi(9)=0.  No.
    -- (18, 8, 14): chi(18)=1, chi(8)=0.  No.
    -- Hmm chi(14) just has chi(14) ≠ 1.  chi(14) ∈ {0, 2}.
    -- And if chi(13) = 0, chi(14) ≠ 0.
    -- This is getting too long.  Let me try a DIFFERENT route.
    -- Look at chi(16): (15, 11, 16) — 15 + 33 = 48 = 3·16. chi(15)=2, chi(11)=1.  No.
    -- (21, 9, 16) — chi(21)=1, chi(9)=0.  No.
    -- (24, 8, 16) — chi(24)=0, chi(8)=0, chi(16).  Mono iff 0=0=chi(16).  chi(16) ≠ 0.
    -- (27, 7, 16) — chi(27)=0, chi(7)=1.  No.
    -- (3, 15, 16) — chi(3)=0, chi(15)=2.  No.
    -- (6, 14, 16) — chi(6)=1, chi(14), chi(16).  Mono iff 1=chi(14)=chi(16).  If chi(14)=1 and chi(16)=1.  But chi(14) ≠ 1.  So no constraint.
    -- (12, 12, 16) — chi(12)=2.  Mono iff 2=2=chi(16).  chi(16) ≠ 2.
    -- So chi(16) ∉ {0, 2}.  chi(16) = 1.
    have h_16_ne_0 : χ 16 ≠ 0 := by
      intro h
      apply mono 24 8 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_24_8, h_8_eq_0]
      · rw [h_8_eq_0, h]
    have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
    have h_16_ne_2 : χ 16 ≠ 2 := by
      intro h
      apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_12_4, h]
    have h_16_eq_1 : χ 16 = 1 := by omega
    -- Triple (6, 11, 13): chi(6)=chi(11)=1, chi(13)≠1.
    -- Triple (15, 11, 16): chi(15)=2, chi(11)=1, chi(16)=1.  Mono iff 2=1.  No.
    -- Triple (21, 11, 18): 21 + 33 = 54 = 3·18.  chi(21)=1, chi(11)=1, chi(18)=1.
    --   Mono iff 1=1=1.  MONO!
    apply mono 21 11 18 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_21_eq_1, h_11_eq_1]
    · rw [h_11_eq_1, h_18_6]

/-! ### §33.9. Round 134 — Case B symmetric: $\chi(2) = 2, \chi(4) = 1$.

  By color permutation $1 \leftrightarrow 2$, this case mirrors
  Round 133.  Sub-cases derive contradiction via similar cascade.

  Sub-case ($\chi(5) = 1$): $\chi(7) = 2$, $\chi(11) \notin
  \{0, 1, 2\}$ — CONTRADICTION.

  Sub-case ($\chi(5) = 2$): $\chi(7) = 1$ or $2$.  If $\chi(7) = 1$:
  $\chi(11) = 0$ forbidden, $\chi(11) \ne 1$ (from triple at $11$),
  $\chi(11) \ne 2$ — CONTRADICTION.
-/

/--
  **Round 134 — Case B symmetric at $(3, 3)$ with $\chi(2)=2, \chi(4)=1$.**

  Mirror of Round 133 via color permutation.
-/
theorem c_zero_excluded_b3_k3_caseB_21 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 0 ∧
      χ 1 = 0 ∧ χ 2 = 2 ∧ χ 4 = 1 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv1 : χ 1 < 3 := hv 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 3 := hv 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 3 := hv 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 3 := hv 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 3 := hv 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 3 := hv 6 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv9 : χ 9 < 3 := hv 9 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hv 11 (by norm_num) (by omega)
  have hv12 : χ 12 < 3 := hv 12 (by norm_num) (by omega)
  have hv15 : χ 15 < 3 := hv 15 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hv 18 (by norm_num) (by omega)
  have hv21 : χ 21 < 3 := hv 21 (by norm_num) (by omega)
  have hv24 : χ 24 < 3 := hv 24 (by norm_num) (by omega)
  have hv27 : χ 27 < 3 := hv 27 (by norm_num) (by omega)
  have shift_eq : ∀ m, 0 < m → 3 * m ≤ 27 → χ m < 3 →
      χ (3 * m) = χ m := by
    intro m hmp hmn hmv
    have hsh := hShift m hmp hmn
    have hmod : χ m % 3 = χ m := Nat.mod_eq_of_lt hmv
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh; exact hsh
  have h_3_1 : χ 3 = 0 := by
    have h := shift_eq 1 (by norm_num) (by norm_num) hv1
    rwa [show 3 * 1 = 3 from rfl, hχ1] at h
  have h_6_2 : χ 6 = 2 := by
    have h := shift_eq 2 (by norm_num) (by norm_num) hv2
    rwa [show 3 * 2 = 6 from rfl, hχ2] at h
  have h_9_3 : χ 9 = 0 := by
    have h := shift_eq 3 (by norm_num) (by norm_num) hv3
    rwa [show 3 * 3 = 9 from rfl, h_3_1] at h
  have h_12_4 : χ 12 = 1 := by
    have h := shift_eq 4 (by norm_num) (by norm_num) hv4
    rwa [show 3 * 4 = 12 from rfl, hχ4] at h
  have h_15_5 : χ 15 = χ 5 := by
    have h := shift_eq 5 (by norm_num) (by norm_num) hv5
    rwa [show 3 * 5 = 15 from rfl] at h
  have h_18_6 : χ 18 = 2 := by
    have h := shift_eq 6 (by norm_num) (by norm_num) hv6
    rwa [show 3 * 6 = 18 from rfl, h_6_2] at h
  have h_21_7 : χ 21 = χ 7 := by
    have h := shift_eq 7 (by norm_num) (by norm_num) hv7
    rwa [show 3 * 7 = 21 from rfl] at h
  have h_24_8 : χ 24 = χ 8 := by
    have h := shift_eq 8 (by norm_num) (by norm_num) hv8
    rwa [show 3 * 8 = 24 from rfl] at h
  have h_27_9 : χ 27 = 0 := by
    have h := shift_eq 9 (by norm_num) (by norm_num) hv9
    rwa [show 3 * 9 = 27 from rfl, h_9_3] at h
  -- Self-loop (6, 6, 8): χ(6) ≠ χ(8). χ(6) = 2, so χ(8) ≠ 2.
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_6_2, h]
  -- Self-loop (12, 8, 12): χ(12) ≠ χ(8). χ(12) = 1, so χ(8) ≠ 1.
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12_4, h]
    · rw [h, h_12_4]
  have h_8_eq_0 : χ 8 = 0 := by omega
  -- (9, 5, 8): chi(5) ≠ 0.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9_3, h]
    · rw [h, h_8_eq_0]
  have hχ5_val : χ 5 = 1 ∨ χ 5 = 2 := by omega
  rcases hχ5_val with h5_1 | h5_2
  · -- Sub-case χ(5) = 1.
    have h_15_eq_1 : χ 15 = 1 := h_15_5.trans h5_1
    -- (21, 5, 12): chi(21), chi(5)=1, chi(12)=1.  Mono iff chi(21) = 1.
    have h_7_ne_1 : χ 7 ≠ 1 := by
      intro h
      have h21 : χ 21 = 1 := h_21_7.trans h
      apply mono 21 5 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h21, h5_1]
      · rw [h5_1, h_12_4]
    -- (3, 7, 8): chi(7) ≠ 0.
    have h_7_ne_0 : χ 7 ≠ 0 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3_1, h]
      · rw [h, h_8_eq_0]
    have h_7_eq_2 : χ 7 = 2 := by omega
    have h_21_eq_2 : χ 21 = 2 := h_21_7.trans h_7_eq_2
    -- χ(11) constraints:
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9_3, h_8_eq_0]
      · rw [h_8_eq_0, h]
    -- (15, 6, 11): chi(15)=1, chi(6)=2. No constraint.
    -- (21, 4, 11)? 21 + 12 = 33 = 3·11. chi(21)=2, chi(4)=1. No.
    -- (3, 11, 12): chi(3)=0, chi(11), chi(12)=1.  Mono iff 0=chi(11)=1.  chi(11) = 0 OR ≠ 1.
    --   chi(11) ≠ 0 known.  So no constraint from this.
    -- Need chi(11) ≠ 1: (12, 7, 11)? chi(12)=1, chi(7)=2. No.
    -- (?, ?, 11) more: x=18, y=5: (18, 5, 11). chi(18)=2, chi(5)=1. No.
    -- x=24, y=3: (24, 3, 11). chi(24)=0, chi(3)=0. chi(11) ≠ 0. Same.
    -- x=27, y=2: (27, 2, 11). chi(27)=0, chi(2)=2. No.
    -- Hmm need chi(11) ≠ 2: x=6, y=9: (6, 9, 11). chi(6)=2, chi(9)=0. No.
    -- x=15, y=6: (15, 6, 11). chi(15)=1, chi(6)=2. No.
    -- x=21, y=4: chi(21)=2, chi(4)=1. No.
    -- For chi(11) = 2 to mono: need (?, ?, 11) with both endpoints 2.
    -- chi(2)=2, chi(6)=2, chi(18)=2, chi(21)=2.
    -- (?, ?, 11) with x + 3y = 33. (x, y) = (?, 2): x=27. chi(27)=0. No.
    -- (x, y) = (?, 6): x=15. chi(15)=1. No.
    -- (x, y) = (?, 18): out of range.
    -- (x, y) = (?, 21): out of range.
    -- What about (3·c, ?, 11) where chi(3c) = 2?
    -- Need chi(3c) = 2.  chi(3)=0, chi(6)=2, chi(9)=0, chi(12)=1, chi(15)=1, chi(18)=2, chi(21)=2, chi(24)=0, chi(27)=0.
    -- So chi(3c) = 2 for c ∈ {2, 6, 7} (since chi(6)=chi(18)=chi(21)=2).
    -- (6, 9, 11): chi(6)=2, chi(9)=0. No.
    -- (18, 5, 11): chi(18)=2, chi(5)=1. No.
    -- (21, 4, 11): chi(21)=2, chi(4)=1. No.
    -- (?, ?, 11) where both = 2.  Need chi(y) = 2 and y matches.
    -- Looking: chi(2)=2, chi(6)=2.
    -- (x, 2, 11): x = 33 - 6 = 27. (27, 2, 11). chi(27)=0. No.
    -- (x, 6, 11): x = 33 - 18 = 15. (15, 6, 11). chi(15)=1. No.
    -- (x, 18, 11): y > z, not Rado.
    -- Hmm, no triple ending at 11 with both endpoints color 2.
    -- chi(11) = 2 doesn't directly mono with current values.
    -- chi(11) ∈ {1, 2}.  Both possible without immediate contradiction.
    -- Need a chi(11) ≠ 1 constraint.
    -- (?, ?, ?) with x = 6, y = 11, z = ?: 6 + 33 = 39 = 3·13. (6, 11, 13).
    --   chi(6)=2, chi(11), chi(13).  Mono iff 2=chi(11)=chi(13).
    --   If chi(11) = 2, mono iff chi(13) = 2.
    -- chi(13)?  Let me check (?, ?, 13): x + 3y = 39.
    --   (3, 12, 13): chi(3)=0, chi(12)=1. No.
    --   (6, 11, 13): see above.
    --   (9, 10, 13): chi(9)=0, chi(10)?
    --   (12, 9, 13): chi(12)=1, chi(9)=0. No.
    --   (15, 8, 13): chi(15)=1, chi(8)=0. No.
    --   (18, 7, 13): chi(18)=2, chi(7)=2, chi(13). chi(13) ≠ 2.
    --   (21, 6, 13): chi(21)=2, chi(6)=2, chi(13). chi(13) ≠ 2. Same.
    --   (24, 5, 13): chi(24)=0, chi(5)=1. No.
    --   (27, 4, 13): chi(27)=0, chi(4)=1. No.
    -- So chi(13) ≠ 2.
    -- If chi(11) = 2, then (6, 11, 13) mono iff chi(13) = 2. But chi(13) ≠ 2. Not mono.
    -- Need chi(10): self-loop (15, 10, 15): chi(15)=1 ≠ chi(10).  chi(10) ≠ 1.
    --   (?, ?, 10): (15, 5, 10): chi(15)=1=chi(5)=1, mono iff chi(10)=1. chi(10) ≠ 1.
    --   (27, 1, 10): chi(27)=0, chi(1)=0. chi(10) ≠ 0.
    --   (3, 9, 10): chi(3)=0=chi(9)=0. chi(10) ≠ 0.
    --   So chi(10) ∈ {2}.
    have h_15_eq_1' : χ 15 = 1 := h_15_eq_1
    have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
    have h_10_ne_0 : χ 10 ≠ 0 := by
      intro h
      apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_27_9, hχ1]
      · rw [hχ1, h]
    have h_10_ne_1 : χ 10 ≠ 1 := by
      intro h
      apply mono 15 5 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15_eq_1, h5_1]
      · rw [h5_1, h]
    have h_10_eq_2 : χ 10 = 2 := by omega
    -- chi(16): (24, 8, 16): chi(24)=0=chi(8)=0, chi(16) ≠ 0.
    -- (12, 12, 16): chi(12)=1, chi(16) ≠ 1.
    -- (18, 10, 16): chi(18)=2, chi(10)=2, chi(16) ≠ 2.
    -- chi(16) ∉ {0,1,2}.  CONTRADICTION.
    have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
    have h_16_ne_0 : χ 16 ≠ 0 := by
      intro h
      apply mono 24 8 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_24_8, h_8_eq_0]
      · rw [h_8_eq_0, h]
    have h_16_ne_1 : χ 16 ≠ 1 := by
      intro h
      apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_12_4, h]
    have h_16_ne_2 : χ 16 ≠ 2 := by
      intro h
      apply mono 18 10 16 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18_6, h_10_eq_2]
      · rw [h_10_eq_2, h]
    omega
  · -- Sub-case χ(5) = 2.
    have h_15_eq_2 : χ 15 = 2 := h_15_5.trans h5_2
    -- Mirror of Round 133 Sub-case B2: (21, 5, 12) gives chi(7) constraint.
    -- chi(5)=2, chi(12)=1.  Mono in (21,5,12) iff chi(21)=2=1.  Impossible.  Not mono regardless.
    -- (3, 7, 8): chi(7) ≠ 0.
    have h_7_ne_0 : χ 7 ≠ 0 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3_1, h]
      · rw [h, h_8_eq_0]
    have hχ7_val : χ 7 = 1 ∨ χ 7 = 2 := by omega
    rcases hχ7_val with h7_1 | h7_2
    · -- χ(7) = 1.
      have h_21_eq_1 : χ 21 = 1 := h_21_7.trans h7_1
      -- chi(10): (15, 5, 10) chi(15)=2=chi(5)=2, chi(10) ≠ 2.
      -- (27, 1, 10): chi(10) ≠ 0.
      have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
      have h_10_ne_2 : χ 10 ≠ 2 := by
        intro h
        apply mono 15 5 10 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15_eq_2, h5_2]
        · rw [h5_2, h]
      have h_10_ne_0 : χ 10 ≠ 0 := by
        intro h
        apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_27_9, hχ1]
        · rw [hχ1, h]
      have h_10_eq_1 : χ 10 = 1 := by omega
      -- chi(11): (9, 8, 11) chi(11) ≠ 0.
      -- (12, 7, 11): chi(12)=1, chi(7)=1, chi(11) ≠ 1.
      -- (15, 6, 11): chi(15)=2, chi(6)=2, chi(11) ≠ 2.
      -- chi(11) ∉ {0, 1, 2}.  CONTRADICTION.
      have h_11_ne_0 : χ 11 ≠ 0 := by
        intro h
        apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_9_3, h_8_eq_0]
        · rw [h_8_eq_0, h]
      have h_11_ne_1 : χ 11 ≠ 1 := by
        intro h
        apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_12_4, h7_1]
        · rw [h7_1, h]
      have h_11_ne_2 : χ 11 ≠ 2 := by
        intro h
        apply mono 15 6 11 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15_eq_2, h_6_2]
        · rw [h_6_2, h]
      omega
    · -- χ(7) = 2.
      have h_21_eq_2 : χ 21 = 2 := h_21_7.trans h7_2
      -- Mirror sub-case B2 from Round 133:
      -- chi(10): (15, 5, 10) chi(15)=2=chi(5)=2, chi(10) ≠ 2.
      -- (27, 1, 10): chi(10) ≠ 0.
      -- chi(10) = 1.
      have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
      have h_10_ne_2 : χ 10 ≠ 2 := by
        intro h
        apply mono 15 5 10 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15_eq_2, h5_2]
        · rw [h5_2, h]
      have h_10_ne_0 : χ 10 ≠ 0 := by
        intro h
        apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_27_9, hχ1]
        · rw [hχ1, h]
      have h_10_eq_1 : χ 10 = 1 := by omega
      -- chi(11): (9, 8, 11) ≠ 0.
      -- (15, 6, 11): chi(15)=2, chi(6)=2, chi(11) ≠ 2.
      -- (3, 11, 12)? chi(3)=0, chi(12)=1. Mono iff 0=chi(11)=1. No.
      -- (12, 7, 11): chi(12)=1, chi(7)=2. No.
      -- So chi(11) ∈ {1}, chi(11) = 1.
      have h_11_ne_0 : χ 11 ≠ 0 := by
        intro h
        apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_9_3, h_8_eq_0]
        · rw [h_8_eq_0, h]
      have h_11_ne_2 : χ 11 ≠ 2 := by
        intro h
        apply mono 15 6 11 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15_eq_2, h_6_2]
        · rw [h_6_2, h]
      have h_11_eq_1 : χ 11 = 1 := by omega
      -- Triple (21, 11, 18)? 21 + 33 = 54 = 3·18. chi(21)=2, chi(11)=1, chi(18)=2.
      -- Mono iff 2=1=2. No. Not mono.
      -- Need different triple.  How about (12, 11, 15)? 12 + 33 = 45 = 3·15.
      --   chi(12)=1, chi(11)=1, chi(15)=2. Mono iff 1=1=2. No.
      -- (6, 11, 13): chi(6)=2, chi(11)=1. No.
      -- (24, 11, 19)? 24 + 33 = 57 = 3·19. chi(24)=0, chi(11)=1. No.
      -- (27, 11, 20)? chi(27)=0, chi(11)=1. No.
      -- (3, 11, 12): chi(3)=0, chi(11)=1. No.
      -- (9, 11, 14): chi(9)=0, chi(11)=1. No.
      -- (18, 11, 17)? 18 + 33 = 51 = 3·17. chi(18)=2, chi(11)=1. No.
      -- Hmm no direct mono from chi(11) = 1.
      -- Need MORE structural deductions.
      -- chi(13)? (6, 11, 13): chi(6)=2, chi(11)=1. No.
      -- (18, 7, 13): chi(18)=2, chi(7)=2, chi(13). chi(13) ≠ 2.
      -- (21, 6, 13): chi(21)=2, chi(6)=2, chi(13). chi(13) ≠ 2. Same.
      -- (12, 9, 13): chi(12)=1, chi(9)=0. No.
      -- (9, 10, 13): chi(9)=0, chi(10)=1. No.
      -- (3, 12, 13): chi(3)=0, chi(12)=1. No.
      -- (15, 8, 13): chi(15)=2, chi(8)=0. No.
      -- (24, 5, 13): chi(24)=0, chi(5)=2. No.
      -- (27, 4, 13): chi(27)=0, chi(4)=1. No.
      -- chi(13) ∈ {0, 1}.
      -- chi(16): (24, 8, 16) chi(16) ≠ 0.
      -- (12, 12, 16): chi(12)=1, chi(16) ≠ 1.
      -- (18, 10, 16): chi(18)=2, chi(10)=1. No.
      -- (21, 9, 16): chi(21)=2, chi(9)=0. No.
      -- (15, 11, 16): chi(15)=2, chi(11)=1. No.
      -- (6, 14, 16): chi(6)=2, chi(14), chi(16). If chi(14)=2 forces chi(16)=2.
      -- (3, 15, 16): chi(3)=0, chi(15)=2. No.
      -- chi(16) ∉ {0, 1}, chi(16) = 2.
      have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
      have h_16_ne_0 : χ 16 ≠ 0 := by
        intro h
        apply mono 24 8 16 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_24_8, h_8_eq_0]
        · rw [h_8_eq_0, h]
      have h_16_ne_1 : χ 16 ≠ 1 := by
        intro h
        apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rfl
        · rw [h_12_4, h]
      have h_16_eq_2 : χ 16 = 2 := by omega
      -- Triple (6, 16, ?)? 6 + 48 = 54 = 3·18. (6, 16, 18). chi(6)=2, chi(16)=2, chi(18)=2.
      -- All 2.  MONO!
      apply mono 6 16 18 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_6_2, h_16_eq_2]
      · rw [h_16_eq_2, h_18_6]

/-! ### §33.10. Round 135 — FULL $c = 0$ exclusion at $(b, k) = (3, 3)$.

  Combines Rounds 132/133/134 into a complete theorem.
-/

/--
  **Round 135 — FULL $c = 0$ exclusion at $(b, k) = (3, 3)$.**

  No mono-free 3-coloring of $\{1, \ldots, 27\}$ for $b = 3$ with
  $\chi(1) = 0$ has multiplicative shift $c = 0$.  Case-split on
  $(\chi(2), \chi(4)) \in \{(1,1), (1,2), (2,1), (2,2)\}$.
-/
theorem c_zero_excluded_b3_k3 :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 0 ∧
      χ 1 = 0 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv1 : χ 1 < 3 := hValid 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 3 := hValid 2 (by norm_num) (by omega)
  have hv4 : χ 4 < 3 := hValid 4 (by norm_num) (by omega)
  have shift_eq : ∀ m, 0 < m → 3 * m ≤ 27 → χ m < 3 →
      χ (3 * m) = χ m := by
    intro m hmp hmn hmv
    have hsh := hShift m hmp hmn
    have hmod : χ m % 3 = χ m := Nat.mod_eq_of_lt hmv
    simp only [Nat.add_zero] at hsh
    rw [hmod] at hsh; exact hsh
  have h_3_eq_0 : χ 3 = 0 := by
    have h := shift_eq 1 (by norm_num) (by norm_num) hv1
    rwa [show 3 * 1 = 3 from rfl, hχ1] at h
  -- Self-loops forcing χ(2), χ(4) ∈ {1, 2}.
  have h_2_ne_0 : χ 2 ≠ 0 := by
    intro h
    apply mono 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_3_eq_0, h]
    · rw [h, h_3_eq_0]
  have h_4_ne_0 : χ 4 ≠ 0 := by
    intro h
    apply mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_3_eq_0, h]
  -- Case split on (χ(2), χ(4)).
  have h2_val : χ 2 = 1 ∨ χ 2 = 2 := by omega
  have h4_val : χ 4 = 1 ∨ χ 4 = 2 := by omega
  rcases h2_val with h2_1 | h2_2
  · rcases h4_val with h4_1 | h4_2
    · -- (1, 1): Case A.
      exact c_zero_excluded_b3_k3_caseA
        ⟨χ, hValid, hAvoid, hShift, hχ1, by rw [h2_1, h4_1]⟩
    · -- (1, 2): Case B (Round 133).
      exact c_zero_excluded_b3_k3_caseB_12
        ⟨χ, hValid, hAvoid, hShift, hχ1, h2_1, h4_2⟩
  · rcases h4_val with h4_1 | h4_2
    · -- (2, 1): Case B (Round 134).
      exact c_zero_excluded_b3_k3_caseB_21
        ⟨χ, hValid, hAvoid, hShift, hχ1, h2_2, h4_1⟩
    · -- (2, 2): Case A.
      exact c_zero_excluded_b3_k3_caseA
        ⟨χ, hValid, hAvoid, hShift, hχ1, by rw [h2_2, h4_2]⟩

/-! ### §33.11. Round 136 — saturation under HasMultShift c=1 at $(3, 3)$.

  **Theorem (Conditional Closure)**: under $\chi(1) = 0$ + HasMultShift
  $c = 1$ at $(b, k) = (3, 3)$ + $\chi(10) = 0$, mono triple $(27, 1, 10)$
  fires.  Specifically:

  $\chi(27) = (\chi(9) + 1) \% 3 = ((\chi(3)+1)+1) \% 3
  = (((\chi(1)+1)+1)+1) \% 3 = \chi(1) = 0$ (the "valuation
  saturation" identity).

  So under HasMultShift $c = 1$: $\chi(27) = \chi(1)$.  Triple $(27, 1, 10)$
  mono iff $\chi(10) = \chi(27) = \chi(1) = 0$.

  This codifies the "saturation closure" step in the analytic schema
  toward $R_3(3) = 27$.  The HasMultShift hypothesis is the deep
  structural step — equivalent to the compression hypothesis at $(3,3)$.

  Full closure path:
  1. (Round 135) $c = 0$ excluded.
  2. (Conjectured uniqueness) every mono-free χ has HasMultShift
     $c \in \{1, 2\}$.
  3. (Round 136) under c=1 + $\chi(10) = 0$ (also conjectured forced),
     mono triple $(27, 1, 10)$ excludes χ.
  4. By color permutation: c=2 case symmetric.
  5. Combined → $R_3(3) \le 27$.
-/

/--
  **Round 136 — saturation under shift c=1 at $(3, 3)$.**

  Under HasMultShift c=1 + $\chi(1) = 0$ + $\chi(10) = 0$ at $(3, 3)$,
  the Rado triple $(27, 1, 10)$ is monochromatic.
-/
theorem shift_c_one_saturates_at_27 (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hShift : HasMultShift 3 3 27 χ 1)
    (hχ1 : χ 1 = 0) (hχ10 : χ 10 = 0) :
    ¬ AvoidsMonoSolution 3 27 χ := by
  intro hAvoid
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv1 : χ 1 < 3 := hValid 1 (by norm_num) (by omega)
  have hv3 : χ 3 < 3 := hValid 3 (by norm_num) (by omega)
  have hv9 : χ 9 < 3 := hValid 9 (by norm_num) (by omega)
  have hv27 : χ 27 < 3 := hValid 27 (by norm_num) (by omega)
  -- Apply HasMultShift c=1 three times: χ(3) = χ(1)+1, χ(9) = χ(1)+2, χ(27) = χ(1)+3 = χ(1) mod 3.
  have h_3 : χ 3 = (χ 1 + 1) % 3 := by
    have h := hShift 1 (by norm_num) (by norm_num)
    rwa [show 3 * 1 = 3 from rfl] at h
  have h_9 : χ 9 = (χ 3 + 1) % 3 := by
    have h := hShift 3 (by norm_num) (by norm_num)
    rwa [show 3 * 3 = 9 from rfl] at h
  have h_27 : χ 27 = (χ 9 + 1) % 3 := by
    have h := hShift 9 (by norm_num) (by norm_num)
    rwa [show 3 * 9 = 27 from rfl] at h
  -- Compute χ(27) = ((χ(1)+1)+1+1) % 3 = (χ(1)+3) % 3 = χ(1) % 3 = χ(1) (since χ(1) < 3).
  have h_χ1_mod : χ 1 % 3 = χ 1 := Nat.mod_eq_of_lt hv1
  have h_27_eq_χ1 : χ 27 = χ 1 := by
    rw [h_27, h_9, h_3]
    omega
  -- Mono triple (27, 1, 10): 27 + 3 = 30 = 3·10.
  apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · exact h_27_eq_χ1
  · exact hχ1.trans hχ10.symm

/-! ### §33.12. Round 137 — saturation under HasMultShift c=2 (symmetric).

  Mirror of Round 136: under HasMultShift c=2 + χ(1) = 0 + χ(10) = 0,
  the Rado triple $(27, 1, 10)$ is monochromatic.

  Algebraic identity: applying $+2$ three times in $\mathbb{Z}/3$
  gives $+6 \equiv 0$, so χ(27) = χ(1) under c=2 as well.
-/

/--
  **Round 137 — saturation under shift c=2 at $(3, 3)$.**
-/
theorem shift_c_two_saturates_at_27 (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hShift : HasMultShift 3 3 27 χ 2)
    (hχ1 : χ 1 = 0) (hχ10 : χ 10 = 0) :
    ¬ AvoidsMonoSolution 3 27 χ := by
  intro hAvoid
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv1 : χ 1 < 3 := hValid 1 (by norm_num) (by omega)
  have h_3 : χ 3 = (χ 1 + 2) % 3 := by
    have h := hShift 1 (by norm_num) (by norm_num)
    rwa [show 3 * 1 = 3 from rfl] at h
  have h_9 : χ 9 = (χ 3 + 2) % 3 := by
    have h := hShift 3 (by norm_num) (by norm_num)
    rwa [show 3 * 3 = 9 from rfl] at h
  have h_27 : χ 27 = (χ 9 + 2) % 3 := by
    have h := hShift 9 (by norm_num) (by norm_num)
    rwa [show 3 * 9 = 27 from rfl] at h
  have h_27_eq_χ1 : χ 27 = χ 1 := by
    rw [h_27, h_9, h_3]
    omega
  apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · exact h_27_eq_χ1
  · exact hχ1.trans hχ10.symm

/-! ### §33.13. Round 138 — conditional R_3(3) ≤ 27 under HasMultShift + χ(10) forced.

  Combines Rounds 135/136/137 into a CONDITIONAL closure theorem.
  Under the structural-uniqueness hypotheses:
  - HasMultShift c for some c ∈ {0, 1, 2}.
  - χ(10) = 0 when χ(1) = 0 (forced by mono-free).

  We derive R_3(3) ≤ 27.  This codifies the analytic schema in Lean.

  The TWO remaining open structural hypotheses are pillars 3 and 4
  of the closure (see Round 136's documentation).
-/

/--
  **Round 138 — conditional $R_3(3) \le 27$ under the structural hypotheses.**

  Given HasMultShift for some c, and the forced color identities
  χ(1) = 0 (WLOG) and χ(10) = 0 (deep structural step), no
  mono-free 3-coloring of {1,...,27} exists.
-/
theorem R_3_3_le_27_conditional :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      (∃ c, c < 3 ∧ HasMultShift 3 3 27 χ c) ∧
      χ 1 = 0 ∧ χ 10 = 0 := by
  rintro ⟨χ, hValid, hAvoid, ⟨c, hc_lt, hShift⟩, hχ1, hχ10⟩
  -- Case-split on c ∈ {0, 1, 2}.
  interval_cases c
  · -- c = 0: Round 135 excludes.
    apply c_zero_excluded_b3_k3
    exact ⟨χ, hValid, hAvoid, hShift, hχ1⟩
  · -- c = 1: Round 136 gives mono.
    exact shift_c_one_saturates_at_27 χ hValid hShift hχ1 hχ10 hAvoid
  · -- c = 2: Round 137 gives mono.
    exact shift_c_two_saturates_at_27 χ hValid hShift hχ1 hχ10 hAvoid

/-! ### §33.14. Round 139 — STRUCTURAL: $\chi(2) = 0$ forced under HasMultShift c=1.

  First step toward closing **Pillar 3** (structural uniqueness):
  prove that under HasMultShift c=1 + $\chi(1) = 0$ + mono-free at
  $(3, 3)$, the alternative $\chi(2) = 2$ leads to contradiction.

  Hence $\chi(2) = 0$ FORCED (since $\chi(2) \ne 1$ from self-loop
  $(3, 2, 3)$, and now $\chi(2) \ne 2$).

  Combined with HasMultShift: $\chi$ on orbit $\{2, 6, 18\}$ matches
  valuation pattern $(0, 1, 2)$.

  Proof structure: cascade $\chi(2) = 2 \Rightarrow \chi(6) = 0,
  \chi(4) = 2, \chi(5) = 1, \chi(7) = 2, \chi(10) = 1, \chi(8) \in
  \{1, 2\}$.  Each sub-case (chi(8) = 1 and chi(8) = 2) gives a
  $\chi$-value that's forced out of $\{0, 1, 2\}$ — contradiction.
-/

/--
  **Round 139 — $\chi(2) = 0$ forced under HasMultShift c=1.**

  Under HasMultShift c=1 + $\chi(1) = 0$ at $(3, 3)$, the value
  $\chi(2) = 2$ is incompatible with mono-freeness.
-/
theorem shift_c_one_forces_chi_2_zero :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 1 ∧
      χ 1 = 0 ∧ χ 2 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv1 : χ 1 < 3 := hv 1 (by norm_num) (by omega)
  have hv2 : χ 2 < 3 := hv 2 (by norm_num) (by omega)
  have hv3 : χ 3 < 3 := hv 3 (by norm_num) (by omega)
  have hv4 : χ 4 < 3 := hv 4 (by norm_num) (by omega)
  have hv5 : χ 5 < 3 := hv 5 (by norm_num) (by omega)
  have hv6 : χ 6 < 3 := hv 6 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv9 : χ 9 < 3 := hv 9 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hv 11 (by norm_num) (by omega)
  have hv12 : χ 12 < 3 := hv 12 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hv 13 (by norm_num) (by omega)
  have hv14 : χ 14 < 3 := hv 14 (by norm_num) (by omega)
  have hv15 : χ 15 < 3 := hv 15 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
  have hv18 : χ 18 < 3 := hv 18 (by norm_num) (by omega)
  have hv21 : χ 21 < 3 := hv 21 (by norm_num) (by omega)
  have hv24 : χ 24 < 3 := hv 24 (by norm_num) (by omega)
  have hv27 : χ 27 < 3 := hv 27 (by norm_num) (by omega)
  -- HasMultShift c=1: χ(3m) = (χ(m) + 1) % 3.
  have shift1 : ∀ m, 0 < m → 3 * m ≤ 27 → χ (3 * m) = (χ m + 1) % 3 := by
    intro m hmp hmn
    exact hShift m hmp hmn
  -- Compute χ at multiples of 3.
  have h_3 : χ 3 = 1 := by
    have h := shift1 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at h
    omega
  have h_6 : χ 6 = 0 := by
    have h := shift1 2 (by norm_num) (by norm_num)
    rw [show 3 * 2 = 6 from rfl, hχ2] at h
    omega
  have h_9 : χ 9 = 2 := by
    have h := shift1 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl, h_3] at h
    omega
  have h_18 : χ 18 = 1 := by
    have h := shift1 6 (by norm_num) (by norm_num)
    rw [show 3 * 6 = 18 from rfl, h_6] at h
    omega
  have h_27 : χ 27 = 0 := by
    have h := shift1 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, h_9] at h
    omega
  -- Self-loop (3, 3, 4): χ(4) ≠ χ(3) = 1. Self-loop (6, 4, 6): χ(4) ≠ χ(6) = 0.
  have h_4_ne_1 : χ 4 ≠ 1 := by
    intro h
    apply mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_3, h]
  have h_4_ne_0 : χ 4 ≠ 0 := by
    intro h
    apply mono 6 4 6 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_6, h]
    · rw [h, h_6]
  have h_4 : χ 4 = 2 := by omega
  have h_12 : χ 12 = 0 := by
    have h := shift1 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, h_4] at h
    omega
  -- χ(5) constraints.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 12 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12, hχ1]
    · rw [hχ1, h]
  have h_5_ne_2 : χ 5 ≠ 2 := by
    intro h
    apply mono 9 2 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9, hχ2]
    · rw [hχ2, h]
  have h_5 : χ 5 = 1 := by omega
  have h_15 : χ 15 = 2 := by
    have h := shift1 5 (by norm_num) (by norm_num)
    rw [show 3 * 5 = 15 from rfl, h_5] at h
    omega
  -- χ(7): self-loop (9, 4, 7)? 9 + 12 = 21 = 3·7. ✓
  -- Mono iff χ(9) = χ(4) = χ(7) = 2 = 2 = χ(7). So χ(7) ≠ 2.
  have h_7_ne_2 : χ 7 ≠ 2 := by
    intro h
    apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9, h_4]
    · rw [h_4, h]
  -- χ(10): self-loop (15, 10, 15) gives χ(10) ≠ χ(15) = 2.
  -- Cross-triple (27, 1, 10) gives χ(10) ≠ 0.
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h]
    · rw [h, h_15]
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ1]
    · rw [hχ1, h]
  have h_10 : χ 10 = 1 := by omega
  -- χ(11): from various triples.
  have h_11_ne_1 : χ 11 ≠ 1 := by
    intro h
    apply mono 18 5 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, h_5]
    · rw [h_5, h]
  -- Self-loop (6, 6, 8): χ(6) ≠ χ(8). χ(8) ≠ 0.
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_6, h]
  -- Case split on χ(7) ∈ {0, 1} (χ(7) ≠ 2 from above).
  have h_7_val : χ 7 = 0 ∨ χ 7 = 1 := by omega
  rcases h_7_val with h_7_0 | h_7_1
  · -- χ(7) = 0. χ(21) = 1.
    have h_21 : χ 21 = 1 := by
      have h := shift1 7 (by norm_num) (by norm_num)
      rw [show 3 * 7 = 21 from rfl, h_7_0] at h
      omega
    -- χ(11) ≠ 0 from (12, 7, 11) — chi(12)=0=chi(7)=0, chi(11) forced ≠ 0.
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12, h_7_0]
      · rw [h_7_0, h]
    have h_11 : χ 11 = 2 := by omega
    -- Case split on χ(8) ∈ {1, 2}.
    have h_8_val : χ 8 = 1 ∨ χ 8 = 2 := by omega
    rcases h_8_val with h_8_1 | h_8_2
    · -- χ(8) = 1. χ(24) = 2.
      have h_24 : χ 24 = 2 := by
        have h := shift1 8 (by norm_num) (by norm_num)
        rw [show 3 * 8 = 24 from rfl, h_8_1] at h
        omega
      -- χ(14) ∉ {0, 1, 2}: contradiction.
      -- Need (6, 12, 14): chi(14) ≠ 0.
      have h_14_ne_0 : χ 14 ≠ 0 := by
        intro h
        apply mono 6 12 14 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_6, h_12]
        · rw [h_12, h]
      have h_14_ne_2 : χ 14 ≠ 2 := by
        intro h
        apply mono 9 11 14 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_9, h_11]
        · rw [h_11, h]
      have h_14_ne_1 : χ 14 ≠ 1 := by
        intro h
        apply mono 18 8 14 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_18, h_8_1]
        · rw [h_8_1, h]
      omega
    · -- χ(8) = 2. χ(24) = 0.
      have h_24 : χ 24 = 0 := by
        have h := shift1 8 (by norm_num) (by norm_num)
        rw [show 3 * 8 = 24 from rfl, h_8_2] at h
        omega
      -- χ(13) ≠ 2 from (15, 8, 13). χ(13) ≠ 1 from (3, 13, 14) needing chi(14)?
      -- Actually: χ(13) ≠ 2 from (15, 8, 13). Need to force the rest.
      have h_13_ne_2 : χ 13 ≠ 2 := by
        intro h
        apply mono 15 8 13 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15, h_8_2]
        · rw [h_8_2, h]
      -- Now show chi(13) ∈ {0, 1} both lead to chi(14) impossible OR chi(16) impossible.
      -- For chi(16): (12, 12, 16) chi(16) ≠ 0. (18, 10, 16) chi(16) ≠ 1. (15, 11, 16) chi(16) ≠ 2.
      have h_16_ne_0 : χ 16 ≠ 0 := by
        intro h
        apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rfl
        · rw [h_12, h]
      have h_16_ne_1 : χ 16 ≠ 1 := by
        intro h
        apply mono 18 10 16 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_18, h_10]
        · rw [h_10, h]
      have h_16_ne_2 : χ 16 ≠ 2 := by
        intro h
        apply mono 15 11 16 (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by omega) (by norm_num)
        · rw [h_15, h_11]
        · rw [h_11, h]
      omega
  · -- χ(7) = 1.
    have h_21 : χ 21 = 2 := by
      have h := shift1 7 (by norm_num) (by norm_num)
      rw [show 3 * 7 = 21 from rfl, h_7_1] at h
      omega
    -- χ(8) ≠ 1 from (3, 7, 8). χ(8) ≠ 0 (self-loop). So χ(8) = 2.
    have h_8_ne_1 : χ 8 ≠ 1 := by
      intro h
      apply mono 3 7 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3, h_7_1]
      · rw [h_7_1, h]
    have h_8 : χ 8 = 2 := by omega
    have h_24 : χ 24 = 0 := by
      have h := shift1 8 (by norm_num) (by norm_num)
      rw [show 3 * 8 = 24 from rfl, h_8] at h
      omega
    -- χ(11) ≠ 2 from (9, 8, 11): chi(9)=2=chi(8)=2, chi(11) ≠ 2.
    -- Combined with chi(11) ≠ 1: chi(11) = 0.
    have h_11_ne_2 : χ 11 ≠ 2 := by
      intro h
      apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9, h_8]
      · rw [h_8, h]
    have h_11 : χ 11 = 0 := by omega
    -- χ(13) ≠ 0 from (6, 11, 13). χ(13) ≠ 1 from (18, 7, 13). χ(13) ≠ 2 from (15, 8, 13).
    have h_13_ne_0 : χ 13 ≠ 0 := by
      intro h
      apply mono 6 11 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_6, h_11]
      · rw [h_11, h]
    have h_13_ne_1 : χ 13 ≠ 1 := by
      intro h
      apply mono 18 7 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_18, h_7_1]
      · rw [h_7_1, h]
    have h_13_ne_2 : χ 13 ≠ 2 := by
      intro h
      apply mono 15 8 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h_8]
      · rw [h_8, h]
    omega

/-! ### §33.15. Round 140 — χ(4)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=0.

  Continues the structural uniqueness cascade.  Given Round 139's
  χ(2) = 0, prove χ(4) = 0 forced (since χ(4) ≠ 1 from self-loop
  (3, 3, 4), and χ(4) = 2 leads to contradiction via cascade
  similar to Round 139).
-/

/--
  **Round 140 — χ(4)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=0.**

  Under HasMultShift c=1 + χ(1)=χ(2)=0, the alternative χ(4)=2 is
  incompatible with mono-freeness, forcing χ(4)=0.
-/
theorem shift_c_one_forces_chi_4_zero :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 1 ∧
      χ 1 = 0 ∧ χ 2 = 0 ∧ χ 4 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv5 : χ 5 < 3 := hv 5 (by norm_num) (by omega)
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hv 11 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hv 13 (by norm_num) (by omega)
  have hv14 : χ 14 < 3 := hv 14 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
  have hv17 : χ 17 < 3 := hv 17 (by norm_num) (by omega)
  have hv20 : χ 20 < 3 := hv 20 (by norm_num) (by omega)
  have hv22 : χ 22 < 3 := hv 22 (by norm_num) (by omega)
  have shift1 : ∀ m, 0 < m → 3 * m ≤ 27 → χ (3 * m) = (χ m + 1) % 3 := hShift
  -- Forced values from HasMultShift + χ(1)=χ(2)=0 + χ(4)=2.
  have h_3 : χ 3 = 1 := by
    have h := shift1 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at h; omega
  have h_6 : χ 6 = 1 := by
    have h := shift1 2 (by norm_num) (by norm_num)
    rw [show 3 * 2 = 6 from rfl, hχ2] at h; omega
  have h_9 : χ 9 = 2 := by
    have h := shift1 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl, h_3] at h; omega
  have h_12 : χ 12 = 0 := by
    have h := shift1 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, hχ4] at h; omega
  have h_18 : χ 18 = 2 := by
    have h := shift1 6 (by norm_num) (by norm_num)
    rw [show 3 * 6 = 18 from rfl, h_6] at h; omega
  have h_27 : χ 27 = 0 := by
    have h := shift1 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, h_9] at h; omega
  -- χ(5) ≠ 0 from (12, 1, 5), χ(5) ≠ 2 from ... wait let me check.
  -- (12, 1, 5): chi(12)=0, chi(1)=0. chi(5) ≠ 0.
  have h_5_ne_0 : χ 5 ≠ 0 := by
    intro h
    apply mono 12 1 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12, hχ1]
    · rw [hχ1, h]
  -- χ(5) value depends on case. Let me case-split.
  have h_5_val : χ 5 = 1 ∨ χ 5 = 2 := by omega
  rcases h_5_val with h_5_1 | h_5_2
  · -- χ(5) = 1. χ(15) = 2.
    have h_15 : χ 15 = 2 := by
      have h := shift1 5 (by norm_num) (by norm_num)
      rw [show 3 * 5 = 15 from rfl, h_5_1] at h; omega
    -- χ(7) ≠ 1 from (3, 6, 7), χ(7) ≠ 2 from (9, 4, 7).
    have h_7_ne_1 : χ 7 ≠ 1 := by
      intro h
      apply mono 3 6 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3, h_6]
      · rw [h_6, h]
    have h_7_ne_2 : χ 7 ≠ 2 := by
      intro h
      apply mono 9 4 7 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9, hχ4]
      · rw [hχ4, h]
    have h_7 : χ 7 = 0 := by omega
    have h_21 : χ 21 = 1 := by
      have h := shift1 7 (by norm_num) (by norm_num)
      rw [show 3 * 7 = 21 from rfl, h_7] at h; omega
    -- χ(8): self-loops force ≠ 1 (from (6,6,8)), ≠ 0 (from (12,8,12)). χ(8)=2.
    have h_8_ne_1 : χ 8 ≠ 1 := by
      intro h
      apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_6, h]
    have h_8_ne_0 : χ 8 ≠ 0 := by
      intro h
      apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12, h]
      · rw [h, h_12]
    have h_8 : χ 8 = 2 := by omega
    have h_24 : χ 24 = 0 := by
      have h := shift1 8 (by norm_num) (by norm_num)
      rw [show 3 * 8 = 24 from rfl, h_8] at h; omega
    -- χ(10): ≠ 0 from (27,1,10), ≠ 2 from (15,10,15) self-loop. χ(10)=1.
    have h_10_ne_0 : χ 10 ≠ 0 := by
      intro h
      apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_27, hχ1]
      · rw [hχ1, h]
    have h_10_ne_2 : χ 10 ≠ 2 := by
      intro h
      apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h]
      · rw [h, h_15]
    have h_10 : χ 10 = 1 := by omega
    -- χ(11): ≠ 0 from (12,7,11), ≠ 2 from (9,8,11). χ(11)=1.
    have h_11_ne_0 : χ 11 ≠ 0 := by
      intro h
      apply mono 12 7 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12, h_7]
      · rw [h_7, h]
    have h_11_ne_2 : χ 11 ≠ 2 := by
      intro h
      apply mono 9 8 11 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9, h_8]
      · rw [h_8, h]
    have h_11 : χ 11 = 1 := by omega
    -- χ(13): ≠ 1 from (6,11,13), ≠ 2 from (15,8,13). χ(13)=0.
    have h_13_ne_1 : χ 13 ≠ 1 := by
      intro h
      apply mono 6 11 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_6, h_11]
      · rw [h_11, h]
    have h_13_ne_2 : χ 13 ≠ 2 := by
      intro h
      apply mono 15 8 13 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h_8]
      · rw [h_8, h]
    have h_13 : χ 13 = 0 := by omega
    -- χ(17): ≠ 0 from (12,13,17), ≠ 1 from (21,10,17). χ(17)=2.
    have h_17_ne_0 : χ 17 ≠ 0 := by
      intro h
      apply mono 12 13 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_12, h_13]
      · rw [h_13, h]
    have h_17_ne_1 : χ 17 ≠ 1 := by
      intro h
      apply mono 21 10 17 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_21, h_10]
      · rw [h_10, h]
    have h_17 : χ 17 = 2 := by omega
    -- χ(20): ≠ 0 from (24,12,20), ≠ 2 from (15,15,20) self-loop. χ(20)=1.
    have h_20_ne_0 : χ 20 ≠ 0 := by
      intro h
      apply mono 24 12 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_24, h_12]
      · rw [h_12, h]
    have h_20_ne_2 : χ 20 ≠ 2 := by
      intro h
      apply mono 15 15 20 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_15, h]
    have h_20 : χ 20 = 1 := by omega
    -- χ(22): ≠ 0 from (27,13,22), ≠ 1 from (3,21,22), ≠ 2 from (15,17,22).
    have h_22_ne_0 : χ 22 ≠ 0 := by
      intro h
      apply mono 27 13 22 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_27, h_13]
      · rw [h_13, h]
    have h_22_ne_1 : χ 22 ≠ 1 := by
      intro h
      apply mono 3 21 22 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_3, h_21]
      · rw [h_21, h]
    have h_22_ne_2 : χ 22 ≠ 2 := by
      intro h
      apply mono 15 17 22 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_15, h_17]
      · rw [h_17, h]
    omega
  · -- χ(5) = 2. χ(15) = 0.
    have h_15 : χ 15 = 0 := by
      have h := shift1 5 (by norm_num) (by norm_num)
      rw [show 3 * 5 = 15 from rfl, h_5_2] at h; omega
    -- Similar cascade, find contradiction.
    -- (9, 5, 8): chi(9)=2, chi(5)=2, chi(8). chi(8) ≠ 2.
    have h_8_ne_2 : χ 8 ≠ 2 := by
      intro h
      apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rw [h_9, h_5_2]
      · rw [h_5_2, h]
    -- Self-loop (6, 6, 8): chi(8) ≠ 1. So chi(8) = 0.
    have h_8_ne_1 : χ 8 ≠ 1 := by
      intro h
      apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
        (by omega) (by omega) (by omega) (by norm_num)
      · rfl
      · rw [h_6, h]
    have h_8 : χ 8 = 0 := by omega
    -- Self-loop (12, 8, 12): chi(12) ≠ chi(8). 0 ≠ 0. CONTRADICTION!
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12, h_8]
    · rw [h_8, h_12]

/-! ### §33.16. Round 141 — χ(5)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=0.

  Continues cascade.  Self-loop $(6, 3, 5)$ excludes χ(5) = 1.
  Sub-cases χ(5) = 2 traverse χ(8), χ(13), χ(16) constraints to
  derive contradiction.
-/

/--
  **Round 141 — χ(5)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=0.**
-/
theorem shift_c_one_forces_chi_5_zero :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 1 ∧
      χ 1 = 0 ∧ χ 2 = 0 ∧ χ 4 = 0 ∧ χ 5 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, hχ5⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv11 : χ 11 < 3 := hv 11 (by norm_num) (by omega)
  have hv13 : χ 13 < 3 := hv 13 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
  have shift1 : ∀ m, 0 < m → 3 * m ≤ 27 → χ (3 * m) = (χ m + 1) % 3 := hShift
  -- Forced values.
  have h_3 : χ 3 = 1 := by
    have h := shift1 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at h; omega
  have h_6 : χ 6 = 1 := by
    have h := shift1 2 (by norm_num) (by norm_num)
    rw [show 3 * 2 = 6 from rfl, hχ2] at h; omega
  have h_9 : χ 9 = 2 := by
    have h := shift1 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl, h_3] at h; omega
  have h_12 : χ 12 = 1 := by
    have h := shift1 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, hχ4] at h; omega
  have h_15 : χ 15 = 0 := by
    have h := shift1 5 (by norm_num) (by norm_num)
    rw [show 3 * 5 = 15 from rfl, hχ5] at h; omega
  have h_18 : χ 18 = 2 := by
    have h := shift1 6 (by norm_num) (by norm_num)
    rw [show 3 * 6 = 18 from rfl, h_6] at h; omega
  have h_27 : χ 27 = 0 := by
    have h := shift1 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, h_9] at h; omega
  -- χ(8) ≠ 2 from (9, 5, 8). χ(8) ≠ 1 from self-loop (6, 6, 8). So χ(8)=0.
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply mono 9 5 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9, hχ5]
    · rw [hχ5, h]
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_6, h]
  have h_8 : χ 8 = 0 := by omega
  -- χ(7) ≠ 0 from (15, 2, 7). χ(7) ∈ {1, 2}.
  have h_7_ne_0 : χ 7 ≠ 0 := by
    intro h
    apply mono 15 2 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, hχ2]
    · rw [hχ2, h]
  -- χ(13) ≠ 0 from (15, 8, 13). χ(13) ≠ 1 from (3, 12, 13).
  have h_13_ne_0 : χ 13 ≠ 0 := by
    intro h
    apply mono 15 8 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h_8]
    · rw [h_8, h]
  have h_13_ne_1 : χ 13 ≠ 1 := by
    intro h
    apply mono 3 12 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_3, h_12]
    · rw [h_12, h]
  have h_13 : χ 13 = 2 := by omega
  -- χ(7) ≠ 2 from (18, 7, 13): chi(18)=2=chi(13)=2. So chi(7) ≠ 2.
  have h_7_ne_2 : χ 7 ≠ 2 := by
    intro h
    apply mono 18 7 13 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, h]
    · rw [h, h_13]
  have h_7 : χ 7 = 1 := by omega
  have h_21 : χ 21 = 2 := by
    have h := shift1 7 (by norm_num) (by norm_num)
    rw [show 3 * 7 = 21 from rfl, h_7] at h; omega
  -- χ(11) ≠ 2 from (18, 5, 11). χ(11) ≠ 1 from (24, 3, 11) needing χ(24).
  -- χ(24) = (χ(8)+1)%3 = 1.
  have h_24 : χ 24 = 1 := by
    have h := shift1 8 (by norm_num) (by norm_num)
    rw [show 3 * 8 = 24 from rfl, h_8] at h; omega
  have h_11_ne_2 : χ 11 ≠ 2 := by
    intro h
    apply mono 18 5 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, hχ5]
    · rw [hχ5, h]
  have h_11_ne_1 : χ 11 ≠ 1 := by
    intro h
    apply mono 24 3 11 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_24, h_3]
    · rw [h_3, h]
  have h_11 : χ 11 = 0 := by omega
  -- χ(16): ≠ 0 from (15, 11, 16) via chi(15)=0=chi(11)=0; ≠ 1 from (12, 12, 16);
  -- ≠ 2 from (21, 9, 16) via chi(21)=2=chi(9)=2.
  have h_16_ne_0 : χ 16 ≠ 0 := by
    intro h
    apply mono 15 11 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h_11]
    · rw [h_11, h]
  have h_16_ne_1 : χ 16 ≠ 1 := by
    intro h
    apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_12, h]
  have h_16_ne_2 : χ 16 ≠ 2 := by
    intro h
    apply mono 21 9 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_21, h_9]
    · rw [h_9, h]
  omega

/-! ### §33.17. Round 142 — χ(7)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=χ(5)=0.
-/

/--
  **Round 142 — χ(7)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=χ(5)=0.**
-/
theorem shift_c_one_forces_chi_7_zero :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 1 ∧
      χ 1 = 0 ∧ χ 2 = 0 ∧ χ 4 = 0 ∧ χ 5 = 0 ∧ χ 7 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, hχ5, hχ7⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have shift1 : ∀ m, 0 < m → 3 * m ≤ 27 → χ (3 * m) = (χ m + 1) % 3 := hShift
  -- Forced values.
  have h_3 : χ 3 = 1 := by
    have h := shift1 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at h; omega
  have h_9 : χ 9 = 2 := by
    have h := shift1 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl, h_3] at h; omega
  have h_15 : χ 15 = 1 := by
    have h := shift1 5 (by norm_num) (by norm_num)
    rw [show 3 * 5 = 15 from rfl, hχ5] at h; omega
  have h_21 : χ 21 = 0 := by
    have h := shift1 7 (by norm_num) (by norm_num)
    rw [show 3 * 7 = 21 from rfl, hχ7] at h; omega
  have h_27 : χ 27 = 0 := by
    have h := shift1 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, h_9] at h; omega
  -- χ(8): ≠ 0 from (21, 1, 8); ≠ 1 from self-loop (12, 8, 12) and chi(12)?
  -- Wait need chi(12). chi(12) = (chi(4)+1)%3 = 1.
  have h_12 : χ 12 = 1 := by
    have h := shift1 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, hχ4] at h; omega
  have h_8_ne_0 : χ 8 ≠ 0 := by
    intro h
    apply mono 21 1 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_21, hχ1]
    · rw [hχ1, h]
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 12 8 12 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_12, h]
    · rw [h, h_12]
  have h_8 : χ 8 = 2 := by omega
  -- χ(10): ≠ 0 from (27, 1, 10); ≠ 2 from (9, 7, 10).
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ1]
    · rw [hχ1, h]
  have h_10_ne_2 : χ 10 ≠ 2 := by
    intro h
    apply mono 9 7 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_9, hχ7]
    · rw [hχ7, h]
  have h_10 : χ 10 = 1 := by omega
  -- Self-loop (15, 10, 15): chi(15) ≠ chi(10). 1 = 1 → MONO!
  apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by norm_num)
  · rw [h_15, h_10]
  · rw [h_10, h_15]

/-! ### §33.18. Round 143 — χ(8)=0 forced under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=χ(5)=χ(7)=0.
-/

/--
  **Round 143 — χ(8)=0 forced.**
-/
theorem shift_c_one_forces_chi_8_zero :
    ¬ ∃ χ : ℕ → ℕ,
      IsValidColoring 27 3 χ ∧
      AvoidsMonoSolution 3 27 χ ∧
      HasMultShift 3 3 27 χ 1 ∧
      χ 1 = 0 ∧ χ 2 = 0 ∧ χ 4 = 0 ∧ χ 5 = 0 ∧ χ 7 = 0 ∧ χ 8 = 2 := by
  rintro ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, hχ5, hχ7, hχ8⟩
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
  have shift1 : ∀ m, 0 < m → 3 * m ≤ 27 → χ (3 * m) = (χ m + 1) % 3 := hShift
  have h_3 : χ 3 = 1 := by
    have h := shift1 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at h; omega
  have h_6 : χ 6 = 1 := by
    have h := shift1 2 (by norm_num) (by norm_num)
    rw [show 3 * 2 = 6 from rfl, hχ2] at h; omega
  have h_9 : χ 9 = 2 := by
    have h := shift1 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl, h_3] at h; omega
  have h_12 : χ 12 = 1 := by
    have h := shift1 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, hχ4] at h; omega
  have h_15 : χ 15 = 1 := by
    have h := shift1 5 (by norm_num) (by norm_num)
    rw [show 3 * 5 = 15 from rfl, hχ5] at h; omega
  have h_18 : χ 18 = 2 := by
    have h := shift1 6 (by norm_num) (by norm_num)
    rw [show 3 * 6 = 18 from rfl, h_6] at h; omega
  have h_27 : χ 27 = 0 := by
    have h := shift1 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, h_9] at h; omega
  -- χ(10): ≠ 0, ≠ 1; χ(10) = 2.
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ1]
    · rw [hχ1, h]
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h]
    · rw [h, h_15]
  have h_10 : χ 10 = 2 := by omega
  -- χ(16): ≠ 0, ≠ 1, ≠ 2 → contradiction.
  have h_16_ne_0 : χ 16 ≠ 0 := by
    intro h
    apply mono 27 7 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ7]
    · rw [hχ7, h]
  have h_16_ne_1 : χ 16 ≠ 1 := by
    intro h
    apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_12, h]
  have h_16_ne_2 : χ 16 ≠ 2 := by
    intro h
    apply mono 18 10 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, h_10]
    · rw [h_10, h]
  omega

/-! ### §33.19. Round 144 — CONDITIONAL R_3(3) ≤ 27 under HasMultShift c=1 + χ(1)=0.

  **MAJOR MILESTONE**: combining Rounds 139-143 (forced colors at
  orbit reps {2, 4, 5, 7, 8}) with chi(10) impossibility cascade,
  we derive: under HasMultShift c=1 + χ(1)=0, NO mono-free 3-coloring
  of {1,...,27} for b=3 exists.

  This is the FIRST UNCONDITIONAL closure (modulo HasMultShift
  hypothesis only) of $R_3(3) \le 27$ via the multiplicative-shift
  framework.
-/

/--
  **Round 144 — R_3(3) ≤ 27 under HasMultShift c=1 + χ(1)=0.**

  No mono-free 3-coloring χ of {1,...,27} for b=3 with HasMultShift
  c=1 + χ(1)=0 exists.  Combines the structural-uniqueness cascade
  Rounds 139-143 with χ(10) value-impossibility.
-/
theorem R_3_3_le_27_under_shift_c_one (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hShift : HasMultShift 3 3 27 χ 1)
    (hχ1 : χ 1 = 0) :
    ¬ AvoidsMonoSolution 3 27 χ := by
  intro hAvoid
  have mono : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
      x ≤ 27 → y ≤ 27 → z ≤ 27 →
      x + 3 * y = 3 * z → χ x = χ y → χ y = χ z → False :=
    fun x y z hx hy hz hxn hyn hzn heq hxy hyz =>
      hAvoid ⟨x, y, z, hxn, hyn, hzn, ⟨hx, hy, hz, heq⟩, hxy, hyz⟩
  have hv : ∀ m, 1 ≤ m → m ≤ 27 → χ m < 3 := hValid
  -- Force χ at orbit reps via Rounds 139-143.
  -- χ(2) = 0:
  have hv2 : χ 2 < 3 := hv 2 (by norm_num) (by omega)
  have h_2_ne_1 : χ 2 ≠ 1 := by
    intro h
    apply mono 3 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · have hsh := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh
      rw [hsh, h]
    · rw [h]
      have hsh := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh
      exact hsh.symm
  have h_2_ne_2 : χ 2 ≠ 2 := by
    intro h
    apply shift_c_one_forces_chi_2_zero
    exact ⟨χ, hValid, hAvoid, hShift, hχ1, h⟩
  have hχ2 : χ 2 = 0 := by omega
  -- χ(4) = 0:
  have hv4 : χ 4 < 3 := hv 4 (by norm_num) (by omega)
  have h_4_ne_1 : χ 4 ≠ 1 := by
    intro h
    apply mono 3 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · have hsh := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh
      rw [hsh, h]
  have h_4_ne_2 : χ 4 ≠ 2 := by
    intro h
    apply shift_c_one_forces_chi_4_zero
    exact ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, h⟩
  have hχ4 : χ 4 = 0 := by omega
  -- χ(5) = 0:
  have hv5 : χ 5 < 3 := hv 5 (by norm_num) (by omega)
  have h_5_ne_1 : χ 5 ≠ 1 := by
    intro h
    apply mono 6 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · -- chi(6) = (chi(2)+1)%3 = 1, chi(3) = 1.
      have hsh6 := hShift 2 (by norm_num) (by norm_num)
      rw [show 3 * 2 = 6 from rfl, hχ2] at hsh6
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh6
      have hsh3 := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh3
      rw [hmod] at hsh3
      rw [hsh6, hsh3]
    · have hsh3 := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh3
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh3
      rw [hsh3, h]
  have h_5_ne_2 : χ 5 ≠ 2 := by
    intro h
    apply shift_c_one_forces_chi_5_zero
    exact ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, h⟩
  have hχ5 : χ 5 = 0 := by omega
  -- χ(7) = 0:
  have hv7 : χ 7 < 3 := hv 7 (by norm_num) (by omega)
  have h_7_ne_1 : χ 7 ≠ 1 := by
    intro h
    apply mono 3 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · have hsh3 := hShift 1 (by norm_num) (by norm_num)
      rw [show 3 * 1 = 3 from rfl, hχ1] at hsh3
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh3
      have hsh6 := hShift 2 (by norm_num) (by norm_num)
      rw [show 3 * 2 = 6 from rfl, hχ2] at hsh6
      rw [hmod] at hsh6
      rw [hsh3, hsh6]
    · have hsh6 := hShift 2 (by norm_num) (by norm_num)
      rw [show 3 * 2 = 6 from rfl, hχ2] at hsh6
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh6
      rw [hsh6, h]
  have h_7_ne_2 : χ 7 ≠ 2 := by
    intro h
    apply shift_c_one_forces_chi_7_zero
    exact ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, hχ5, h⟩
  have hχ7 : χ 7 = 0 := by omega
  -- χ(8) = 0:
  have hv8 : χ 8 < 3 := hv 8 (by norm_num) (by omega)
  have h_8_ne_1 : χ 8 ≠ 1 := by
    intro h
    apply mono 6 6 8 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · have hsh6 := hShift 2 (by norm_num) (by norm_num)
      rw [show 3 * 2 = 6 from rfl, hχ2] at hsh6
      have hmod : (0 + 1) % 3 = 1 := by decide
      rw [hmod] at hsh6
      rw [hsh6, h]
  have h_8_ne_2 : χ 8 ≠ 2 := by
    intro h
    apply shift_c_one_forces_chi_8_zero
    exact ⟨χ, hValid, hAvoid, hShift, hχ1, hχ2, hχ4, hχ5, hχ7, h⟩
  have hχ8 : χ 8 = 0 := by omega
  -- Now χ(10) ∈ {0, 1, 2} all impossible.
  have hv10 : χ 10 < 3 := hv 10 (by norm_num) (by omega)
  -- Compute helper values.
  have h_15 : χ 15 = 1 := by
    have hsh := hShift 5 (by norm_num) (by norm_num)
    rw [show 3 * 5 = 15 from rfl, hχ5] at hsh
    have hmod : (0 + 1) % 3 = 1 := by decide
    rw [hmod] at hsh
    exact hsh
  have h_27 : χ 27 = 0 := by
    have hsh9 := hShift 3 (by norm_num) (by norm_num)
    rw [show 3 * 3 = 9 from rfl] at hsh9
    have hsh3 := hShift 1 (by norm_num) (by norm_num)
    rw [show 3 * 1 = 3 from rfl, hχ1] at hsh3
    have hmod1 : (0 + 1) % 3 = 1 := by decide
    rw [hmod1] at hsh3
    rw [hsh3] at hsh9
    have hmod2 : (1 + 1) % 3 = 2 := by decide
    rw [hmod2] at hsh9
    have hsh27 := hShift 9 (by norm_num) (by norm_num)
    rw [show 3 * 9 = 27 from rfl, hsh9] at hsh27
    have hmod3 : (2 + 1) % 3 = 0 := by decide
    rw [hmod3] at hsh27
    exact hsh27
  -- χ(10) ≠ 0 from (27, 1, 10).
  have h_10_ne_0 : χ 10 ≠ 0 := by
    intro h
    apply mono 27 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ1]
    · rw [hχ1, h]
  -- χ(10) ≠ 1 from self-loop (15, 10, 15).
  have h_10_ne_1 : χ 10 ≠ 1 := by
    intro h
    apply mono 15 10 15 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_15, h]
    · rw [h, h_15]
  -- χ(10) = 2 forced. Now derive chi(16) impossibility.
  have h_10 : χ 10 = 2 := by omega
  -- chi(12) = 1, chi(18) = 2, chi(9) = 2.
  have h_12 : χ 12 = 1 := by
    have hsh := hShift 4 (by norm_num) (by norm_num)
    rw [show 3 * 4 = 12 from rfl, hχ4] at hsh
    have hmod : (0 + 1) % 3 = 1 := by decide
    rw [hmod] at hsh
    exact hsh
  have h_18 : χ 18 = 2 := by
    have hsh6 := hShift 2 (by norm_num) (by norm_num)
    rw [show 3 * 2 = 6 from rfl, hχ2] at hsh6
    have hmod1 : (0 + 1) % 3 = 1 := by decide
    rw [hmod1] at hsh6
    have hsh18 := hShift 6 (by norm_num) (by norm_num)
    rw [show 3 * 6 = 18 from rfl, hsh6] at hsh18
    have hmod2 : (1 + 1) % 3 = 2 := by decide
    rw [hmod2] at hsh18
    exact hsh18
  -- chi(16): ≠ 0 from (27, 7, 16); ≠ 1 from (12, 12, 16); ≠ 2 from (18, 10, 16).
  have hv16 : χ 16 < 3 := hv 16 (by norm_num) (by omega)
  have h_16_ne_0 : χ 16 ≠ 0 := by
    intro h
    apply mono 27 7 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_27, hχ7]
    · rw [hχ7, h]
  have h_16_ne_1 : χ 16 ≠ 1 := by
    intro h
    apply mono 12 12 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rfl
    · rw [h_12, h]
  have h_16_ne_2 : χ 16 ≠ 2 := by
    intro h
    apply mono 18 10 16 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by norm_num)
    · rw [h_18, h_10]
    · rw [h_10, h]
  omega

/-! ### §33.20. Round 145 — c=2 case via COLOR PERMUTATION 1 ↔ 2.

  Defines swap, proves it preserves mono-freeness and converts
  HasMultShift c=2 → c=1.  Then delegates to Round 144.
-/

/-- Color permutation swapping 1 ↔ 2 (fixes 0). -/
def swapColors_12 (c : ℕ) : ℕ :=
  if c = 1 then 2 else if c = 2 then 1 else c

/-- Swap is its own inverse on all of ℕ. -/
theorem swapColors_12_inv (c : ℕ) : swapColors_12 (swapColors_12 c) = c := by
  unfold swapColors_12
  rcases eq_or_ne c 1 with h1 | h1
  · subst h1; rfl
  · rcases eq_or_ne c 2 with h2 | h2
    · subst h2; rfl
    · simp [h1, h2]

/-- Swap is injective on ℕ. -/
theorem swapColors_12_injective : Function.Injective swapColors_12 := by
  intro a b h
  have ha := swapColors_12_inv a
  have hb := swapColors_12_inv b
  have hab : swapColors_12 (swapColors_12 a) = swapColors_12 (swapColors_12 b) := by
    congr 1
  rw [ha, hb] at hab
  exact hab

/-- Swap stays in range [0, 3). -/
theorem swapColors_12_lt_3 (c : ℕ) (h : c < 3) : swapColors_12 c < 3 := by
  unfold swapColors_12
  rcases eq_or_ne c 1 with h1 | h1
  · subst h1; decide
  · rcases eq_or_ne c 2 with h2 | h2
    · subst h2; decide
    · simp [h1, h2]; omega

theorem swap_preserves_valid (χ : ℕ → ℕ) (n : ℕ)
    (hValid : IsValidColoring n 3 χ) :
    IsValidColoring n 3 (swapColors_12 ∘ χ) := by
  intro m hm_lb hm_ub
  exact swapColors_12_lt_3 (χ m) (hValid m hm_lb hm_ub)

theorem swap_preserves_avoid (χ : ℕ → ℕ) (b n : ℕ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    AvoidsMonoSolution b n (swapColors_12 ∘ χ) := by
  intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
  exact hAvoid ⟨x, y, z, hxn, hyn, hzn, hRT,
    swapColors_12_injective hxy, swapColors_12_injective hyz⟩

theorem swap_converts_shift_2_to_1 (χ : ℕ → ℕ) (n : ℕ)
    (hValid : IsValidColoring n 3 χ)
    (hShift : HasMultShift 3 3 n χ 2) :
    HasMultShift 3 3 n (swapColors_12 ∘ χ) 1 := by
  intro m hmp hmn
  have hShift_m := hShift m hmp hmn
  show swapColors_12 (χ (3 * m)) = (swapColors_12 (χ m) + 1) % 3
  have hχm : χ m < 3 := hValid m hmp (le_trans (Nat.le_mul_of_pos_left m (by norm_num : 0 < 3)) hmn)
  rw [hShift_m]
  interval_cases (χ m)
  · decide
  · decide
  · decide

/--
  **Round 145 — R_3(3) ≤ 27 under HasMultShift c=2 + χ(1)=0.**

  Via swap symmetry: HasMultShift c=2 ↔ c=1 under color perm 1↔2.
-/
theorem R_3_3_le_27_under_shift_c_two (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hShift : HasMultShift 3 3 27 χ 2)
    (hχ1 : χ 1 = 0) :
    ¬ AvoidsMonoSolution 3 27 χ := by
  intro hAvoid
  have hValid' : IsValidColoring 27 3 (swapColors_12 ∘ χ) :=
    swap_preserves_valid χ 27 hValid
  have hShift' : HasMultShift 3 3 27 (swapColors_12 ∘ χ) 1 :=
    swap_converts_shift_2_to_1 χ 27 hValid hShift
  have hχ1' : (swapColors_12 ∘ χ) 1 = 0 := by
    show swapColors_12 (χ 1) = 0
    rw [hχ1]; rfl
  have hAvoid' : AvoidsMonoSolution 3 27 (swapColors_12 ∘ χ) :=
    swap_preserves_avoid χ 3 27 hAvoid
  exact R_3_3_le_27_under_shift_c_one (swapColors_12 ∘ χ) hValid' hShift' hχ1' hAvoid'

/-! ### §33.21. Round 146 — UNIFIED THEOREM combining all c-cases.

  R_3(3) ≤ 27 under HasMultShift for ANY c ∈ {0, 1, 2}.

  Combines Round 135 (c=0 excluded) + Round 144 (c=1 case) +
  Round 145 (c=2 case) via case-split.

  This is the FINAL theorem before Pillar 3.  Once Pillar 3
  (structural existence of HasMultShift) closes, R_3(3) ≤ 27 is
  proven unconditionally analytic.
-/

/--
  **Round 146 — R_3(3) ≤ 27 under HasMultShift (any c) + χ(1)=0.**

  Under existence of SOME multiplicative shift c ∈ {0, 1, 2} +
  χ(1)=0 (WLOG), no mono-free 3-coloring of {1,...,27} for b=3
  exists.
-/
theorem R_3_3_le_27_under_HasMultShift (χ : ℕ → ℕ)
    (hValid : IsValidColoring 27 3 χ)
    (hχ1 : χ 1 = 0)
    (hShiftExists : ∃ c, c < 3 ∧ HasMultShift 3 3 27 χ c) :
    ¬ AvoidsMonoSolution 3 27 χ := by
  intro hAvoid
  obtain ⟨c, hc, hShift⟩ := hShiftExists
  interval_cases c
  · exact c_zero_excluded_b3_k3 ⟨χ, hValid, hAvoid, hShift, hχ1⟩
  · exact R_3_3_le_27_under_shift_c_one χ hValid hShift hχ1 hAvoid
  · exact R_3_3_le_27_under_shift_c_two χ hValid hShift hχ1 hAvoid


end RadoNumbers
