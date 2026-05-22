/-
  RadoNumbers/DPLStructure.lean

  Real-math attack on threshold conjecture's Distance Pair Lemma
  (DPL) structural mechanism. Rounds 9+.

  **Strategic pivot**: rounds 1-8 attacked compression
  (`lem_compress3`). Paper §"Failure of Compression for b=3, k=4"
  explicitly shows compression FAILS at boundary $k = 2(b-1)$, yet
  $R_k(b) = b^k$ still holds via DPL. So DPL — NOT compression —
  is the sharp structural characterization.

  **Key reformulation**: in a valid k-coloring $\chi : \{1, \ldots,
  n\} \to [k]$ avoiding mono Rado solutions to $x + by = bz$, the
  property "$\chi(b^k) = c$" forces $C_c$ to avoid distance
  $b^{k-1}$. Equivalently, the "DPL window structure":
  partition $\{1, \ldots, 2b^{k-1}\}$ into $b^{k-1}$ windows
  $W_r = \{r, r + b^{k-1}\}$ ($r \in [1, b^{k-1}]$), and $C_c$
  avoiding distance $b^{k-1}$ means $C_c$ has at most 1 element
  per window.

  **Round 9 deliverable (DPL pigeonhole)**: quantitative bound
  giving when $|C_c|$ is too large to avoid distance $b^{k-1}$.

  This is structural math — not case analysis. Forms the entry
  point for the DPL closure attack (Rounds 10+).
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Window-partition structure for distance $D$. -/

/--
  The **window partition of $[1, 2D]$ at gap $D$**: for $r \in
  [1, D]$, the window $W_r := \{r, r + D\}$. These pairwise
  disjoint windows partition $[1, 2D]$ into $D$ size-2 cells.
-/
def DPWindow (D r : ℕ) : Finset ℕ := {r, r + D}

/--
  An integer $n \in [1, 2D]$ lies in window $W_r$ for $r =$
  $((n - 1) \bmod D) + 1$ if $n \le D$, else $((n - 1 - D) \bmod D)
  + 1 = n - D$. We expose only the window-membership predicate;
  the explicit index map is not needed.
-/
def DPWindowOf (D n : ℕ) : ℕ :=
  if n ≤ D then n else n - D

/-! ### Lemma 9.1 — DPL pigeonhole bound. -/

/--
  **Lemma 9.1 (DPL Pigeonhole).**

  Let $D \ge 1$, $S \subseteq [1, 2D]$ a Finset. If
  $|S| \ge D + 1$, then $S$ contains a pair at distance $D$ —
  i.e., $\exists r \in [1, D], \{r, r + D\} \subseteq S$.

  This is a clean pigeonhole on the window partition:
  $b^{k-1}$ windows cover $[1, 2 b^{k-1}]$, so any subset with
  $> b^{k-1}$ elements has 2 in some window, giving the pair.

  **Significance**: provides quantitative bound for the cascade.
  If $\chi(b^k) = c$, then $C_c \cap [1, 2b^{k-1}]$ has
  $\le b^{k-1}$ elements. Combined with $\sum_c |C_c| = $
  whole domain, gives constraints across colors.
-/
theorem dpl_pigeonhole (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS_subset : ∀ n ∈ S, 1 ≤ n ∧ n ≤ 2 * D)
    (hS_card : D + 1 ≤ S.card) :
    ∃ r, 1 ≤ r ∧ r ≤ D ∧ r ∈ S ∧ r + D ∈ S := by
  -- Partition S = Slow ∪ Shigh by ≤ D vs > D.
  let Slow : Finset ℕ := S.filter (· ≤ D)
  let Shigh : Finset ℕ := S.filter (· > D)
  have hpartition : S = Slow ∪ Shigh := by
    ext n
    simp only [Slow, Shigh, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      by_cases hd : n ≤ D
      · exact Or.inl ⟨h, hd⟩
      · exact Or.inr ⟨h, by omega⟩
    · intro h
      cases h with
      | inl h => exact h.1
      | inr h => exact h.1
  have hdisj : Disjoint Slow Shigh := by
    rw [Finset.disjoint_filter]
    intro n _ h1 h2; omega
  have hcard_split : S.card = Slow.card + Shigh.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  -- Shifted = (Shigh - D) ⊆ [1, D].
  let Shifted : Finset ℕ := Shigh.image (· - D)
  have hSlow_sub : Slow ⊆ Finset.Icc 1 D := by
    intro n hn
    simp [Slow, Finset.mem_filter] at hn
    have h := hS_subset n hn.1
    simp [Finset.mem_Icc]; exact ⟨h.1, hn.2⟩
  have hShifted_sub : Shifted ⊆ Finset.Icc 1 D := by
    intro r hr
    simp [Shifted, Finset.mem_image] at hr
    obtain ⟨n, hn_in, hn_eq⟩ := hr
    simp [Shigh, Finset.mem_filter] at hn_in
    have hn_bnd := hS_subset n hn_in.1
    simp [Finset.mem_Icc]
    refine ⟨?_, ?_⟩ <;> omega
  have hShifted_card : Shifted.card = Shigh.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    simp only [Shigh, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    simp only [] at hab
    omega
  have hIcc_card : (Finset.Icc 1 D).card = D := by
    rw [Nat.card_Icc]; omega
  -- |Slow| + |Shifted| = |S| ≥ D + 1 > D = |Icc 1 D|; by pigeonhole intersect.
  have hsum : Slow.card + Shifted.card ≥ D + 1 := by
    rw [hShifted_card]; omega
  have h_intersect : (Slow ∩ Shifted).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h_disj : Disjoint Slow Shifted :=
      Finset.disjoint_iff_inter_eq_empty.mpr h
    have h_union_card : (Slow ∪ Shifted).card = Slow.card + Shifted.card :=
      Finset.card_union_of_disjoint h_disj
    have h_union_sub : Slow ∪ Shifted ⊆ Finset.Icc 1 D := by
      intro n hn
      rw [Finset.mem_union] at hn
      cases hn with
      | inl h => exact hSlow_sub h
      | inr h => exact hShifted_sub h
    have h_le : (Slow ∪ Shifted).card ≤ D := by
      rw [← hIcc_card]; exact Finset.card_le_card h_union_sub
    omega
  -- Extract r ∈ Slow ∩ Shifted.
  obtain ⟨r, hr⟩ := h_intersect
  simp [Finset.mem_inter] at hr
  obtain ⟨hr_low, hr_shifted⟩ := hr
  simp [Slow, Finset.mem_filter] at hr_low
  simp [Shifted, Finset.mem_image] at hr_shifted
  obtain ⟨n, hn_in, hn_eq⟩ := hr_shifted
  simp [Shigh, Finset.mem_filter] at hn_in
  have hr1 : 1 ≤ r := (hS_subset r hr_low.1).1
  have hn_bnd := hS_subset n hn_in.1
  have hrD_eq_n : r + D = n := by omega
  refine ⟨r, hr1, hr_low.2, hr_low.1, ?_⟩
  rw [hrD_eq_n]; exact hn_in.1

/-! ### Lemma 9.2 — applied to a color class. -/

/--
  **Lemma 9.2 (DPL bound on color class).**

  In a valid $k$-coloring $\chi$ of $\{1, \ldots, n\}$ avoiding
  mono Rado solutions to $x + by = bz$, if $\chi(b \cdot D) = c$
  and $2D \le n$ and $|\{m \in [1, 2D] : \chi(m) = c\}| \ge D + 1$,
  then a mono Rado triple exists — contradiction.

  Equivalently: $\chi(bD) = c$ AND $2D \le n$ AND $|C_c \cap [1, 2D]|
  \ge D + 1$ is impossible.

  This is a cascade-applicable constraint: it bounds class sizes
  given multiple colorings. Concrete corollary for DPL: at
  $D = b^{k-1}$, if $\chi(b^k) = c$ (forces $C_c$ avoids dist
  $b^{k-1}$) and $C_c \cap [1, 2b^{k-1}]$ is large, contradiction.
-/
theorem dpl_class_bound {b n D : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D)
    (h2D_le : 2 * D ≤ n) (hbD_le : b * D ≤ n)
    (χ : ℕ → ℕ) (hAvoid : AvoidsMonoSolution b n χ)
    (c : ℕ) (hχbD : χ (b * D) = c)
    (S : Finset ℕ)
    (hS_def : ∀ m, m ∈ S ↔ 1 ≤ m ∧ m ≤ 2 * D ∧ χ m = c)
    (hS_card : D + 1 ≤ S.card) :
    False := by
  -- Extract the window pair from S.
  have hS_subset : ∀ m ∈ S, 1 ≤ m ∧ m ≤ 2 * D := by
    intro m hm
    have := (hS_def m).mp hm
    exact ⟨this.1, this.2.1⟩
  obtain ⟨r, hr1, hrD, hr_in_S, hrD_in_S⟩ :=
    dpl_pigeonhole D hD S hS_subset hS_card
  -- Both r and r + D are in S, hence both colored c.
  have hχr := ((hS_def r).mp hr_in_S).2.2
  have hχrD := ((hS_def (r + D)).mp hrD_in_S).2.2
  -- Mono triple (b·D, r, r + D): bD + b·r = b·(r + D).
  apply hAvoid
  refine ⟨b * D, r, r + D, hbD_le, by linarith, by linarith, ?_, ?_, ?_⟩
  · refine ⟨Nat.mul_pos (by linarith) hD, by linarith, by linarith, ?_⟩
    -- b·D + b·r = b·(r + D)
    ring
  · rw [hχbD, hχr]
  · rw [hχr, hχrD]

/-! ### abstract DPL ⟹ upper bound.

  The **Distance Pair Property** `DistancePairProperty b k` is the
  paper's Lemma `lem:keypair` stated as a clean predicate: every
  color class in any valid k-coloring of `{1, …, b^k - 1}` avoiding
  mono contains a pair at distance `b^{k-1}`.

  Round 10 proves the abstract implication
  `DistancePairProperty b k → RadoNumberAtMost b k (b^k)`, cleanly
  separating the HARD structural part (proving DPL holds for
  `k ≤ 2(b-1)`) from the EASY derivation. After Round 10, the
  matching direction reduces to: prove `DistancePairProperty b k`
  for `k ≤ 2(b-1)`. -/

/--
  **Distance Pair Property** (paper Lemma `lem:keypair` as a
  predicate). For every valid k-coloring `χ` of `{1, …, b^k - 1}`
  avoiding monochromatic solutions to `x + by = bz`, every color
  `c < k` has a pair `(j, j + b^{k-1})` both colored `c`, within
  range.
-/
def DistancePairProperty (b k : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k - 1) k χ →
    AvoidsMonoSolution b (b ^ k - 1) χ →
    ∀ c, c < k →
      ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
           χ j = c ∧ χ (j + b ^ (k - 1)) = c

/--
  **Theorem (DPL ⟹ upper bound).**

  If the Distance Pair Property holds for `(b, k)` with `b ≥ 2,
  k ≥ 1`, then `R_k(b) ≤ b^k`.

  Proof: given a valid k-coloring `χ` of `{1, …, b^k}`, restrict to
  `{1, …, b^k - 1}`. Either `χ` already has a mono there (lift it),
  or it avoids one — then `DistancePairProperty` applied to color
  `χ(b^k)` yields `j` with `χ(j) = χ(j + b^{k-1}) = χ(b^k)`, and the
  triple `(b^k, j, j + b^{k-1})` satisfies `b^k + b·j =
  b·(j + b^{k-1})`, monochromatic.

  **Significance**: reduces the matching direction of the threshold
  conjecture to a single clean structural statement. The open
  problem is now precisely: `DistancePairProperty b k` for
  `k ≤ 2(b-1)`.
-/
theorem dpl_implies_rado_upper (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hDPL : DistancePairProperty b k) :
    RadoNumberAtMost b k (b ^ k) := by
  intro χ hValid
  have hb_pos : 0 < b := by linarith
  have hb_pow_pos : 0 < b ^ k := Nat.pow_pos hb_pos
  have hb_pow_ge_2 : 2 ≤ b ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ b ^ 1 := Nat.pow_le_pow_left hb 1
      _ ≤ b ^ k := Nat.pow_le_pow_right (by linarith) hk
  -- d := b^(k-1); key identity d * b = b^k.
  have hd_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
  have hd_mul : b ^ (k - 1) * b = b ^ k := by
    rw [← pow_succ]; congr 1; omega
  -- Restriction to {1, …, b^k - 1} is also a valid k-coloring.
  have hValid' : IsValidColoring (b ^ k - 1) k χ := fun m hm_lb hm_ub =>
    hValid m hm_lb (by omega)
  by_cases hAvoid : AvoidsMonoSolution b (b ^ k - 1) χ
  · -- Apply DPL to color c* := χ(b^k).
    have hChi_bk_lt : χ (b ^ k) < k := hValid (b ^ k) hb_pow_pos (le_refl _)
    obtain ⟨j, hj_lb, hj_ub, hχj, hχj'⟩ :=
      hDPL χ hValid' hAvoid (χ (b ^ k)) hChi_bk_lt
    -- Mono triple (b^k, j, j + b^(k-1)).
    have hj_le_bk : j ≤ b ^ k := by omega
    have hjd_le_bk : j + b ^ (k - 1) ≤ b ^ k := by omega
    refine ⟨b ^ k, j, j + b ^ (k - 1), le_refl _, hj_le_bk, hjd_le_bk, ?_, ?_, ?_⟩
    · refine ⟨hb_pow_pos, by linarith, by linarith, ?_⟩
      -- b^k + b * j = b * (j + b^(k-1))
      have h1 : b * (j + b ^ (k - 1)) = b * j + b ^ (k - 1) * b := by ring
      rw [h1, hd_mul]; ring
    · rw [hχj]
    · rw [hχj, hχj']
  · -- χ already has a mono on the smaller domain; lift it.
    have hMono : HasMonoSolution b (b ^ k - 1) χ := by
      by_contra h
      exact hAvoid h
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    exact ⟨x, y, z, le_trans hxn (Nat.sub_le _ _),
           le_trans hyn (Nat.sub_le _ _), le_trans hzn (Nat.sub_le _ _),
           hRT, hxy, hyz⟩

/--
  **Corollary.** Combined with `thm_lower`, the Distance
  Pair Property gives the full `IsRadoNumber b k (b^k)`.
-/
theorem dpl_implies_isRadoNumber (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hDPL : DistancePairProperty b k)
    (hLower : RadoNumberAtLeast b k (b ^ k)) :
    IsRadoNumber b k (b ^ k) :=
  ⟨hLower, dpl_implies_rado_upper b k hb hk hDPL⟩

/-! ### the recursion (cascade) lemma.

  The fundamental structural fact underlying the cascade: the
  "multiples sub-coloring" $\chi'(d) := \chi(b \cdot d)$ of a valid
  $k$-coloring is itself a valid $k$-coloring on the scaled-down
  domain. This is the engine of the inductive descent
  $R_k(b) \leftarrow R_{k-1}(b) \leftarrow \cdots$. -/

/--
  **Theorem (Recursion / Cascade Lemma).**

  If $\chi$ is a valid $k$-coloring of $\{1, \ldots, n\}$ avoiding
  monochromatic solutions to $x + by = bz$, then the multiples
  sub-coloring $\chi'(d) := \chi(b \cdot d)$ is a valid $k$-coloring
  of $\{1, \ldots, \lfloor n/b \rfloor\}$ that also avoids
  monochromatic solutions.

  Proof:
  * **Valid**: for $d \in [1, \lfloor n/b \rfloor]$, $b \cdot d \le
    n$, so $\chi(bd) < k$ by validity of $\chi$.
  * **Avoids mono**: a mono triple $(x', y', z')$ for $\chi'$ lifts
    to $(bx', by', bz')$, which is a Rado triple for $\chi$
    ($bx' + b(by') = b(bz')$ from $x' + by' = bz'$) and
    monochromatic — contradicting validity of $\chi$.

  **Significance**: this is the cascade engine. Combined with a
  compression step ("multiples use $\le k-1$ colors"), it yields
  $R_k(b) \le b \cdot R_{k-1}(b)$. It also underlies the structure
  of `DistancePairProperty`: the window sub-coloring inherits Rado
  structure recursively.
-/
theorem multiples_subcoloring_valid {b n k : ℕ} (hb : 2 ≤ b)
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring n k χ)
    (hAvoid : AvoidsMonoSolution b n χ) :
    IsValidColoring (n / b) k (fun d => χ (b * d)) ∧
    AvoidsMonoSolution b (n / b) (fun d => χ (b * d)) := by
  have hb_pos : 0 < b := by linarith
  -- Helper: for d ≤ n / b, b * d ≤ n.
  have hbd_le : ∀ d, d ≤ n / b → b * d ≤ n := by
    intro d hd
    calc b * d ≤ b * (n / b) := Nat.mul_le_mul (le_refl b) hd
      _ = (n / b) * b := Nat.mul_comm b (n / b)
      _ ≤ n := Nat.div_mul_le_self n b
  refine ⟨?_, ?_⟩
  · -- Valid coloring.
    intro d hd_lb hd_ub
    exact hValid (b * d)
      (by have : 1 ≤ b * d := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega))
          exact this)
      (hbd_le d hd_ub)
  · -- Avoids monochromatic solutions.
    intro hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    obtain ⟨hx, hy, hz, heq⟩ := hRT
    apply hAvoid
    refine ⟨b * x, b * y, b * z, hbd_le x hxn, hbd_le y hyn, hbd_le z hzn,
            ?_, ?_, ?_⟩
    · -- IsRadoTriple b (b*x) (b*y) (b*z)
      refine ⟨Nat.mul_pos hb_pos hx, Nat.mul_pos hb_pos hy,
              Nat.mul_pos hb_pos hz, ?_⟩
      -- b*x + b*(b*y) = b*(b*z), from x + b*y = b*z
      calc b * x + b * (b * y)
          = b * (x + b * y) := by ring
        _ = b * (b * z) := by rw [heq]
    · -- χ(b*x) = χ(b*y) — directly from hxy (beta-reduced)
      exact hxy
    · exact hyz

/-! ### the cascade theorem.

  Combines the recursion lemma with a compression step to get the
  inductive descent $R_k(b) \le b \cdot R_{k-1}(b)$. Needs a
  color-relabeling helper: when the multiples sub-coloring omits a
  color, relabel to a genuine $(k-1)$-coloring. -/

/-- Color relabeling that "skips" color `c₀`: shifts colors above
    `c₀` down by one. Bijective from `[0,k-1] \ {c₀}` to `[0,k-2]`. -/
def skipColor (c₀ c : ℕ) : ℕ := if c < c₀ then c else c - 1

/-- `skipColor c₀` is injective on `ℕ \ {c₀}`. -/
lemma skipColor_inj {c₀ a b : ℕ} (ha : a ≠ c₀) (hb : b ≠ c₀)
    (h : skipColor c₀ a = skipColor c₀ b) : a = b := by
  unfold skipColor at h
  split_ifs at h <;> omega

/-- `skipColor c₀` maps `[0, k-1] \ {c₀}` into `[0, k-2]`. -/
lemma skipColor_lt {c₀ c k : ℕ} (hc₀ : c₀ < k) (hc : c < k) (hne : c ≠ c₀) :
    skipColor c₀ c < k - 1 := by
  unfold skipColor
  split_ifs with h <;> omega

/--
  **Round 12 helper (relabel omitted color).**

  If a valid `k`-coloring `χ` of `{1, …, n}` never uses color `c₀`,
  then `skipColor c₀ ∘ χ` is a valid `(k-1)`-coloring of
  `{1, …, n}` with the SAME monochromatic-solution structure: it
  avoids monochromatic solutions iff `χ` does.
-/
theorem relabel_omitted_color {n k c₀ : ℕ} (hc₀ : c₀ < k)
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring n k χ)
    (hOmit : ∀ m, 1 ≤ m → m ≤ n → χ m ≠ c₀) :
    IsValidColoring n (k - 1) (fun m => skipColor c₀ (χ m)) ∧
    (∀ b, AvoidsMonoSolution b n χ →
          AvoidsMonoSolution b n (fun m => skipColor c₀ (χ m))) := by
  refine ⟨?_, ?_⟩
  · -- Valid (k-1)-coloring.
    intro m hm_lb hm_ub
    exact skipColor_lt hc₀ (hValid m hm_lb hm_ub) (hOmit m hm_lb hm_ub)
  · -- Avoidance transfers (relabeling preserves mono structure).
    intro b hAvoid hMono
    obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
    have hx : 0 < x := hRT.1
    have hy : 0 < y := hRT.2.1
    have hz : 0 < z := hRT.2.2.1
    -- From skipColor c₀ (χ x) = skipColor c₀ (χ y), get χ x = χ y.
    have hχx_ne : χ x ≠ c₀ := hOmit x hx hxn
    have hχy_ne : χ y ≠ c₀ := hOmit y hy hyn
    have hχz_ne : χ z ≠ c₀ := hOmit z hz hzn
    have hxy' : χ x = χ y := skipColor_inj hχx_ne hχy_ne hxy
    have hyz' : χ y = χ z := skipColor_inj hχy_ne hχz_ne hyz
    exact hAvoid ⟨x, y, z, hxn, hyn, hzn, hRT, hxy', hyz'⟩

/--
  **Theorem (Cascade Step).**

  Suppose $b \ge 2$, $k \ge 2$, and:
  * **(Induction hypothesis)** $R_{k-1}(b) \le b^{k-1}$;
  * **(Compression)** in every valid $k$-coloring $\chi$ of
    $\{1, \ldots, b^k\}$ avoiding monochromatic solutions, the
    multiples sub-coloring omits at least one color on
    $\{1, \ldots, b^{k-1}\}$ (i.e., $\exists c_0 < k$ with
    $\chi(b \cdot d) \ne c_0$ for all $d \in [1, b^{k-1}]$).

  Then $R_k(b) \le b^k$.

  Proof: given valid $\chi$ on $\{1, \ldots, b^k\}$, suppose it
  avoids mono. By the recursion lemma `multiples_subcoloring_valid`,
  $\chi'(d) := \chi(bd)$ is a valid mono-free $k$-coloring of
  $\{1, \ldots, b^{k-1}\}$. By compression, $\chi'$ omits some
  color $c_0$. By `relabel_omitted_color`, $\text{skipColor } c_0
  \circ \chi'$ is a valid mono-free $(k-1)$-coloring of
  $\{1, \ldots, b^{k-1}\}$ — contradicting the induction hypothesis
  $R_{k-1}(b) \le b^{k-1}$.

  **Significance**: this is the rigorous form of the paper §6
  thm:k3b3 reduction, generalised. The matching direction of the
  threshold conjecture for non-boundary $k$ reduces to proving the
  Compression hypothesis. (At the boundary $k = 2(b-1)$,
  compression fails — see paper §"Failure of Compression for
  b=3,k=4" — and one routes through `dpl_implies_rado_upper`
  instead.)
-/
theorem cascade_step (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hInd : RadoNumberAtMost b (k - 1) (b ^ (k - 1)))
    (hCompress : ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k) k χ →
      AvoidsMonoSolution b (b ^ k) χ →
      ∃ c₀, c₀ < k ∧ ∀ d, 1 ≤ d → d ≤ b ^ (k - 1) → χ (b * d) ≠ c₀) :
    RadoNumberAtMost b k (b ^ k) := by
  intro χ hValid
  by_contra hNoMono
  have hAvoid : AvoidsMonoSolution b (b ^ k) χ := hNoMono
  -- Recursion lemma: χ' := χ(b·_) valid mono-free on {1,...,b^k / b}.
  obtain ⟨hχ'_valid, hχ'_avoid⟩ :=
    multiples_subcoloring_valid hb χ hValid hAvoid
  -- b^k / b = b^(k-1).
  have hdiv : b ^ k / b = b ^ (k - 1) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    have h1 : b ^ k = b ^ (k - 1) * b := by
      conv_lhs => rw [hk_eq]
      rw [pow_succ]
    rw [h1, Nat.mul_div_assoc _ (dvd_refl b), Nat.div_self (by linarith), Nat.mul_one]
  rw [hdiv] at hχ'_valid hχ'_avoid
  -- Compression: χ' omits some color c₀.
  obtain ⟨c₀, hc₀_lt, hc₀_omit⟩ := hCompress χ hValid hAvoid
  -- The omitted-color hypothesis in terms of χ' = χ(b·_).
  have hOmit' : ∀ m, 1 ≤ m → m ≤ b ^ (k - 1) → (fun d => χ (b * d)) m ≠ c₀ :=
    fun m hm_lb hm_ub => hc₀_omit m hm_lb hm_ub
  -- Relabel: skipColor c₀ ∘ χ' is a valid mono-free (k-1)-coloring.
  obtain ⟨hχ''_valid, hχ''_avoid_fn⟩ :=
    relabel_omitted_color hc₀_lt (fun d => χ (b * d)) hχ'_valid hOmit'
  have hχ''_avoid := hχ''_avoid_fn b hχ'_avoid
  -- Apply induction hypothesis: every (k-1)-coloring of {1,...,b^(k-1)}
  -- has a mono solution.
  have hχ''_mono := hInd (fun d => skipColor c₀ (χ (b * d))) hχ''_valid
  -- Contradiction with hχ''_avoid.
  exact hχ''_avoid hχ''_mono

/-! ### base case $R_1(b) = b$.

  The base case of the cascade induction. A `1`-coloring forces
  every element to color `0`; the triple $(b, 1, 2)$ is then
  monochromatic. -/

/--
  **Theorem (`thm_k1`).** For all $b \ge 2$,
  $R_1(b) = b$.

  Lower bound: `thm_lower` at $k = 1$. Upper bound: a valid
  `1`-coloring of $\{1, \ldots, b\}$ has every value `< 1`, i.e.,
  all `0`; the Rado triple $(b, 1, 2)$ (satisfying
  $b + b \cdot 1 = b \cdot 2$) is then monochromatic.

  This is the base case of the cascade induction (`cascade_step`
  descends $k \to k - 1$, bottoming out at $k = 1$).
-/
theorem thm_k1 (b : ℕ) (hb : 2 ≤ b) : IsRadoNumber b 1 b := by
  refine ⟨?_, ?_⟩
  · -- Lower bound: R_1(b) ≥ b^1 = b.
    have h := thm_lower b 1 hb (le_refl 1)
    simpa using h
  · -- Upper bound: every valid 1-coloring of {1,…,b} has a mono.
    intro χ hValid
    -- All values are 0 (since χ m < 1).
    have h1 : χ 1 = 0 := by have := hValid 1 (by norm_num) (by linarith); omega
    have h2 : χ 2 = 0 := by have := hValid 2 (by norm_num) (by linarith); omega
    have hb0 : χ b = 0 := by have := hValid b (by linarith) (le_refl b); omega
    -- Mono triple (b, 1, 2): b + b·1 = b·2.
    refine ⟨b, 1, 2, le_refl b, by linarith, by linarith, ?_, ?_, ?_⟩
    · refine ⟨by linarith, by norm_num, by norm_num, ?_⟩
      ring
    · rw [hb0, h1]
    · rw [h1, h2]

/-! ### the DPL recursion lift step.

  The cascade engine `multiples_subcoloring_valid` pushes
  Rado structure DOWN to the multiples sub-coloring $\chi'(d) :=
  \chi(b \cdot d)$. The **lift step** is the dual direction: a
  distance-$d$ pair *found* in $\chi'$ pulls back UP to a
  distance-$(b \cdot d)$ pair in $\chi$.

  Concretely: if $\chi'(j) = \chi'(j + d) = c$, then since
  $\chi'(j) = \chi(bj)$ and $\chi'(j+d) = \chi(b(j+d)) =
  \chi(bj + bd)$, the pair $(bj,\; bj + bd)$ is a distance-$(bd)$
  pair in $\chi$, both colored $c$, with the range scaled by $b$.

  This is the second half of the DPL recursion: combined with
  `DistancePairProperty b (k-1)` applied to $\chi'$, it produces
  distance-$b^{k-1}$ pairs in $\chi$ for every color that $\chi'$
  uses — exactly the `DistancePairProperty b k` conclusion for the
  non-omitted colors. (The omitted color $c_0$ needs the separate
  compression argument; see `dpl_property_k2` for the $k = 2$
  instance where $c_0$ is handled by the $(b, 2b)$ multiple pair.) -/

/--
  **Theorem (DPL recursion lift step).**

  Let $b \ge 2$ and $\chi : \mathbb{N} \to \mathbb{N}$. If the
  multiples sub-coloring agrees at $j$ and $j + d$ — i.e.,
  $\chi(b j) = \chi(b(j + d)) = c$ — then $\chi$ has a
  distance-$(b d)$ pair at color $c$: namely
  $(b j,\; b j + b d)$, with $b j \ge 1$ and (given $j \ge 1$,
  $j + d \le m$) $b j + b d \le b m$.

  Proof: the identity $b j + b d = b (j + d)$ rewrites the second
  coordinate, after which both color equations are the hypotheses
  and the range bound is `Nat.mul_le_mul`.

  **Significance**: this is the "lift" half of the DPL recursion.
  Where `multiples_subcoloring_valid` pushes Rado structure DOWN to
  $\chi'$, this lemma pulls a distance pair UP from $\chi'$ to
  $\chi$, scaling the gap by $b$. Iterating: a distance-$1$ pair at
  the recursion base lifts to distance-$b$, then $b^2$, …,
  $b^{k-1}$ — the gap appearing in `DistancePairProperty b k`.
-/
theorem dpl_lift_distance_pair {b : ℕ} (hb : 2 ≤ b) (χ : ℕ → ℕ)
    (c d j m : ℕ) (hj_lb : 1 ≤ j) (hjd_ub : j + d ≤ m)
    (hχj : χ (b * j) = c) (hχjd : χ (b * (j + d)) = c) :
    1 ≤ b * j ∧ b * j + b * d ≤ b * m ∧
    χ (b * j) = c ∧ χ (b * j + b * d) = c := by
  have hb_pos : 0 < b := by omega
  have hkey : b * j + b * d = b * (j + d) := by ring
  refine ⟨?_, ?_, hχj, ?_⟩
  · -- 1 ≤ b * j
    have : 0 < b * j := Nat.mul_pos hb_pos (by omega)
    omega
  · -- b * j + b * d ≤ b * m
    rw [hkey]
    exact Nat.mul_le_mul (le_refl b) hjd_ub
  · -- χ (b * j + b * d) = c
    rw [hkey]; exact hχjd

/-! ### domain arithmetic for the recursion.

  `DistancePairProperty b k` lives on $\{1, \ldots, b^k - 1\}$;
  the multiples sub-coloring $\chi'$ then lives on
  $\{1, \ldots, (b^k - 1) / b\}$ (per `multiples_subcoloring_valid`).
  For the recursion to feed into `DistancePairProperty b (k-1)`
  (which lives on $\{1, \ldots, b^{k-1} - 1\}$), we need the
  identity $(b^k - 1) / b = b^{k-1} - 1$.

  This is the integer-division fact $b^k - 1 = b \cdot (b^{k-1} - 1)
  + (b - 1)$ with remainder $b - 1 < b$. -/

/--
  **Lemma (recursion domain identity).**

  For $b \ge 2$, $k \ge 1$: $(b^k - 1) / b = b^{k-1} - 1$.

  Proof: $b^k = b \cdot b^{k-1}$, and with $P := b^{k-1} \ge 1$,
  $b^k - 1 = (b - 1) + b \cdot (P - 1)$. Integer division by $b$
  drops the remainder $b - 1$ (`Nat.add_mul_div_left`,
  $(b-1)/b = 0$), leaving $P - 1 = b^{k-1} - 1$.

  **Significance**: aligns the domain of the multiples sub-coloring
  $\chi'$ with the domain `DistancePairProperty b (k-1)` expects —
  the bookkeeping that lets `multiples_subcoloring_valid` chain into
  the DPL recursion.
-/
theorem pow_sub_one_div {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (b ^ k - 1) / b = b ^ (k - 1) - 1 := by
  have hb_pos : 0 < b := by omega
  have hk_eq : k = (k - 1) + 1 := by omega
  have hbk : b ^ k = b * b ^ (k - 1) := by
    conv_lhs => rw [hk_eq, pow_succ]
    ring
  have hP_pos : 1 ≤ b ^ (k - 1) := Nat.one_le_pow _ _ hb_pos
  -- Generalize b^(k-1) to a genuine free variable P.
  rw [hbk]
  revert hP_pos
  generalize b ^ (k - 1) = P
  intro hP_pos
  -- Goal: (b * P - 1) / b = P - 1, with hP_pos : 1 ≤ P.
  rcases Nat.exists_eq_add_of_le hP_pos with ⟨q, hq⟩
  subst hq
  have e1 : (1 : ℕ) + q - 1 = q := by omega
  rw [e1]
  -- Goal: (b * (1 + q) - 1) / b = q.
  have hexp : b * (1 + q) - 1 = (b - 1) + b * q := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hexp, Nat.add_mul_div_left _ _ hb_pos]
  have hrem : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
  omega

/-! ### recursion lemma at the DPL domain.

  `multiples_subcoloring_valid` states the recursion on a
  generic domain $\{1, \ldots, n\}$ with $\chi'$ landing on
  $\{1, \ldots, n/b\}$. For the DPL recursion we instantiate at
  $n = b^k - 1$ and apply `pow_sub_one_div` to rewrite
  $n/b = (b^k - 1)/b$ as $b^{k-1} - 1$ — the exact domain on which
  `DistancePairProperty b (k-1)` is stated. -/

/--
  **Corollary (recursion at the DPL domain).**

  For $b \ge 2$, $k \ge 1$: if $\chi$ is a valid $k$-coloring of
  $\{1, \ldots, b^k - 1\}$ avoiding monochromatic solutions, then
  the multiples sub-coloring $\chi'(d) := \chi(b d)$ is a valid
  $k$-coloring of $\{1, \ldots, b^{k-1} - 1\}$ that also avoids
  monochromatic solutions.

  Proof: `multiples_subcoloring_valid` lands $\chi'$ on
  $\{1, \ldots, (b^k - 1)/b\}$; `pow_sub_one_div` rewrites the
  bound to $b^{k-1} - 1$.

  **Significance**: the recursion lemma in exactly the form the DPL
  cascade consumes — $\chi'$ ready to feed into
  `DistancePairProperty b (k-1)` (after the compression + relabel
  step drops it to a $(k-1)$-coloring).
-/
theorem multiples_subcoloring_valid_at_pow {b k : ℕ} (hb : 2 ≤ b)
    (hk : 1 ≤ k) (χ : ℕ → ℕ)
    (hValid : IsValidColoring (b ^ k - 1) k χ)
    (hAvoid : AvoidsMonoSolution b (b ^ k - 1) χ) :
    IsValidColoring (b ^ (k - 1) - 1) k (fun d => χ (b * d)) ∧
    AvoidsMonoSolution b (b ^ (k - 1) - 1) (fun d => χ (b * d)) := by
  have h := multiples_subcoloring_valid hb χ hValid hAvoid
  rwa [pow_sub_one_div hb hk] at h

/-! ### non-omitted-color half of the DPL
    recursion.

  This is the assembly that turns `DistancePairProperty b (k-1)`
  into the `DistancePairProperty b k` conclusion **for every color
  the multiples sub-coloring still uses** — i.e., every color other
  than the one compression omits.

  Pipeline (all pieces now in hand):
  * `multiples_subcoloring_valid_at_pow`: $\chi'(d) :=
    \chi(bd)$ is valid mono-free on $\{1, \ldots, b^{k-1}-1\}$.
  * `relabel_omitted_color`: since $\chi'$ omits $c_0$,
    $\chi'' := \text{skipColor}\,c_0 \circ \chi'$ is a valid
    mono-free $(k-1)$-coloring on the same domain.
  * `DistancePairProperty b (k-1)` applied to $\chi''$ gives, for
    the relabelled target $c' := \text{skipColor}\,c_0\,c$, a
    distance-$b^{k-2}$ pair in $\chi''$.
  * `skipColor_inj` un-relabels it to a distance-$b^{k-2}$ pair in
    $\chi'$ at the original color $c$ (using that $\chi'$ omits
    $c_0$, so both endpoints are $\ne c_0$).
  * `dpl_lift_distance_pair` lifts it to a
    distance-$b^{k-1}$ pair in $\chi$ at color $c$.

  The OMITTED color $c_0$ is **not** handled here — it needs a
  separate argument from non-multiples (compare `dpl_property_k2`,
  where the omitted color is served by the $(1, b+1)$ non-multiple
  pair). Isolating the non-omitted half is the point: it is the
  part that recurses cleanly, with zero new axioms. -/

/--
  **Theorem (DPL recursion — non-omitted colors).**

  Let $b \ge 2$, $k \ge 2$, and suppose `DistancePairProperty
  b (k-1)` holds. Let $\chi$ be a valid mono-free $k$-coloring of
  $\{1, \ldots, b^k - 1\}$ whose multiples sub-coloring omits color
  $c_0 < k$ (i.e. $\chi(bd) \ne c_0$ for all $d \in
  [1, b^{k-1}-1]$).

  Then for **every** color $c < k$ with $c \ne c_0$, $\chi$ has a
  distance-$b^{k-1}$ pair at color $c$: some $j$ with $1 \le j$,
  $j + b^{k-1} \le b^k - 1$, and $\chi(j) = \chi(j + b^{k-1}) = c$.

  Proof: the pipeline described in the section header — descend to
  $\chi'$, relabel away $c_0$ to a $(k-1)$-coloring $\chi''$, apply
  `DistancePairProperty b (k-1)`, un-relabel via `skipColor_inj`,
  lift via `dpl_lift_distance_pair`.

  **Significance**: this is the structural core of the DPL
  recursion. With this in hand, proving `DistancePairProperty b k`
  reduces to exactly two remaining obligations: (i) the compression
  hypothesis (multiples omit a color), and (ii) the omitted color
  $c_0$ gets its own distance-$b^{k-1}$ pair. Both are isolated,
  named, and axiom-free-derivable-or-explicitly-open — no longer
  buried inside a monolithic SAT atom.
-/
theorem dpl_recursion_nonomitted (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hDPL_prev : DistancePairProperty b (k - 1))
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring (b ^ k - 1) k χ)
    (hAvoid : AvoidsMonoSolution b (b ^ k - 1) χ)
    (c₀ : ℕ) (hc₀ : c₀ < k)
    (hOmit : ∀ d, 1 ≤ d → d ≤ b ^ (k - 1) - 1 → χ (b * d) ≠ c₀) :
    ∀ c, c < k → c ≠ c₀ →
      ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
           χ j = c ∧ χ (j + b ^ (k - 1)) = c := by
  intro c hc hne
  have hb_pos : 0 < b := by omega
  have hk1 : 1 ≤ k := by omega
  -- Exponent arithmetic.
  have hbk : b ^ k = b ^ (k - 1) * b := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    rw [pow_succ]
  have hbe : b ^ (k - 1) = b ^ (k - 1 - 1) * b := by
    have hkm1_eq : k - 1 = (k - 1 - 1) + 1 := by omega
    conv_lhs => rw [hkm1_eq]
    rw [pow_succ]
  have hpkm1_pos : 1 ≤ b ^ (k - 1) := Nat.one_le_pow _ _ hb_pos
  -- χ' := χ(b·_) is a valid mono-free k-coloring of {1,…,b^(k-1)-1}.
  obtain ⟨hχ'_valid, hχ'_avoid⟩ :=
    multiples_subcoloring_valid_at_pow hb hk1 χ hValid hAvoid
  -- χ' omits c₀ (this is exactly `hOmit`).
  have hOmit' : ∀ m, 1 ≤ m → m ≤ b ^ (k - 1) - 1 →
      (fun d => χ (b * d)) m ≠ c₀ := fun m hm_lb hm_ub => hOmit m hm_lb hm_ub
  -- Relabel: χ'' := skipColor c₀ ∘ χ' is a valid mono-free (k-1)-coloring.
  obtain ⟨hχ''_valid, hχ''_avoid_fn⟩ :=
    relabel_omitted_color hc₀ (fun d => χ (b * d)) hχ'_valid hOmit'
  have hχ''_avoid := hχ''_avoid_fn b hχ'_avoid
  -- Target color in the (k-1)-palette.
  set c' := skipColor c₀ c with hc'_def
  have hc'_lt : c' < k - 1 := skipColor_lt hc₀ hc hne
  -- Apply DistancePairProperty b (k-1) to χ''.
  obtain ⟨j, hj_lb, hj_dist_ub, hχ''j, hχ''jd⟩ :=
    hDPL_prev (fun d => skipColor c₀ (χ (b * d))) hχ''_valid hχ''_avoid c' hc'_lt
  -- Beta-reduce the χ'' color equations.
  have hχ''j' : skipColor c₀ (χ (b * j)) = c' := hχ''j
  have hχ''jd' : skipColor c₀ (χ (b * (j + b ^ (k - 1 - 1)))) = c' := hχ''jd
  -- j and j + b^(k-1-1) lie in the range of `hOmit`.
  have hj_le : j ≤ b ^ (k - 1) - 1 := by omega
  have hjd_lb : 1 ≤ j + b ^ (k - 1 - 1) := by omega
  -- Un-relabel: χ'(j) = c and χ'(j + b^(k-1-1)) = c.
  have hχ'j_ne : χ (b * j) ≠ c₀ := hOmit j hj_lb hj_le
  have hχ'jd_ne : χ (b * (j + b ^ (k - 1 - 1))) ≠ c₀ :=
    hOmit _ hjd_lb hj_dist_ub
  have hχ'j_eq : χ (b * j) = c :=
    skipColor_inj hχ'j_ne hne (hχ''j'.trans hc'_def)
  have hχ'jd_eq : χ (b * (j + b ^ (k - 1 - 1))) = c :=
    skipColor_inj hχ'jd_ne hne (hχ''jd'.trans hc'_def)
  -- Lift the distance-b^(k-1-1) pair in χ' to a distance-b^(k-1) pair in χ.
  obtain ⟨_, hlift_ub, hlift_j, hlift_jd⟩ :=
    dpl_lift_distance_pair hb χ c (b ^ (k - 1 - 1)) j (b ^ (k - 1) - 1)
      hj_lb hj_dist_ub hχ'j_eq hχ'jd_eq
  -- b · b^(k-1-1) = b^(k-1).
  have hbbe : b * b ^ (k - 1 - 1) = b ^ (k - 1) := by rw [hbe]; ring
  -- b · (b^(k-1) - 1) + b = b^k ⟹ b·(b^(k-1)-1) ≤ b^k - 1.
  have hbm_eq : b * (b ^ (k - 1) - 1) + b = b ^ k := by
    have h1 : b ^ (k - 1) - 1 + 1 = b ^ (k - 1) := by omega
    calc b * (b ^ (k - 1) - 1) + b
        = b * ((b ^ (k - 1) - 1) + 1) := by ring
      _ = b * b ^ (k - 1) := by rw [h1]
      _ = b ^ k := by rw [hbk]; ring
  -- Assemble: the distance-b^(k-1) pair is (b·j, b·j + b^(k-1)).
  refine ⟨b * j, ?_, ?_, ?_, ?_⟩
  · -- 1 ≤ b · j
    have : 0 < b * j := Nat.mul_pos hb_pos (by omega)
    omega
  · -- b·j + b^(k-1) ≤ b^k - 1
    rw [← hbbe]
    omega
  · -- χ (b·j) = c
    exact hlift_j
  · -- χ (b·j + b^(k-1)) = c
    rw [← hbbe]
    exact hlift_jd

/-! ### the full conditional DPL recursion.

  `dpl_recursion_nonomitted` handles every color except
  the one compression omits. Round 27 composes it with the two
  remaining obligations, stated as explicit hypotheses, to derive
  the full `DistancePairProperty b k` from
  `DistancePairProperty b (k-1)`:

  * **Compression** — every valid mono-free $k$-coloring's multiples
    sub-coloring omits some color $c_0$. (Analytic for $k = 2$ via
    `lem_compress2`; SAT-verified for $k = 3$ via
    `lem_compress3_general`; open in general.)
  * **Omitted-color pair** — that omitted color $c_0$ nonetheless
    has a distance-$b^{k-1}$ pair in $\chi$, necessarily among
    non-multiples. (Analytic for $k = 2$ inside `dpl_property_k2`,
    where the 2-coloring pins $\chi(1) = \chi(b+1) = 1 - c_0$;
    open in general — this is the genuinely hard half the paper
    SAT-verifies.)

  The value of this theorem is **isolation**: the threshold
  conjecture's matching direction, at the recursion step, is now
  exactly these two named hypotheses — no monolithic SAT atom, no
  hidden case analysis. Each can be attacked independently. -/

/--
  **Theorem (conditional DPL recursion step).**

  Let $b \ge 2$, $k \ge 2$. Given:
  * `DistancePairProperty b (k-1)` (the recursion input);
  * **Compression** `hCompress`: every valid mono-free $k$-coloring
    of $\{1, \ldots, b^k-1\}$ has its multiples sub-coloring omit
    some color $c_0 < k$;
  * **Omitted-color pair** `hOmittedPair`: whenever the multiples
    sub-coloring omits $c_0$, the color $c_0$ still has a
    distance-$b^{k-1}$ pair in $\chi$;

  then `DistancePairProperty b k` holds.

  Proof: given a valid mono-free $k$-coloring $\chi$ and target
  color $c$, `hCompress` produces the omitted $c_0$. If $c = c_0$,
  `hOmittedPair` supplies the pair directly; otherwise
  `dpl_recursion_nonomitted` does.

  **Significance**: the clean inductive step of the DPL cascade.
  Combined with the base case `dpl_property_k2`, an
  induction on $k$ would yield `DistancePairProperty b k` for all
  $k$ in the threshold range — conditional only on `hCompress` and
  `hOmittedPair` holding at each level. Those two are the entire
  remaining mathematical content of the matching direction.
-/
theorem dpl_recursion_conditional (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hDPL_prev : DistancePairProperty b (k - 1))
    (hCompress : ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k - 1) k χ →
      AvoidsMonoSolution b (b ^ k - 1) χ →
      ∃ c₀, c₀ < k ∧ ∀ d, 1 ≤ d → d ≤ b ^ (k - 1) - 1 → χ (b * d) ≠ c₀)
    (hOmittedPair : ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k - 1) k χ →
      AvoidsMonoSolution b (b ^ k - 1) χ →
      ∀ c₀, c₀ < k →
        (∀ d, 1 ≤ d → d ≤ b ^ (k - 1) - 1 → χ (b * d) ≠ c₀) →
        ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
             χ j = c₀ ∧ χ (j + b ^ (k - 1)) = c₀) :
    DistancePairProperty b k := by
  intro χ hValid hAvoid c hc
  obtain ⟨c₀, hc₀, hOmit⟩ := hCompress χ hValid hAvoid
  by_cases hcc : c = c₀
  · -- c = c₀: the omitted color, handled by `hOmittedPair`.
    subst hcc
    exact hOmittedPair χ hValid hAvoid c hc hOmit
  · -- c ≠ c₀: a non-omitted color, handled by `dpl_recursion_nonomitted`.
    exact dpl_recursion_nonomitted b k hb hk hDPL_prev χ hValid hAvoid
      c₀ hc₀ hOmit c hc hcc

/-! ### the omitted color: counting, not
    avoidance.

  A structural observation sharpens the omitted-color obligation.
  Every Rado triple $(x, y, z)$ for $x + by = bz$ has $x = b(z-y)$
  — its **first element is always a multiple of $b$**. So in any
  monochromatic triple, the shared color is the color of a
  multiple of $b$. A color $c_0$ omitted by *every* multiple
  therefore can never be a monochromatic-triple color: the class
  $C_{c_0}$ carries **no Rado constraint at all**.

  Consequently the omitted color's distance pair cannot come from
  an avoidance argument (there is nothing to avoid). It must come
  from **counting**: $C_{c_0}$ is whatever the constrained colors
  leave behind, and if that residue is large enough in the window
  $[1, 2b^{k-1}]$, `dpl_pigeonhole` forces a
  distance-$b^{k-1}$ pair.

  This is exactly why the Distance Pair Lemma is SAT-verified in
  the paper for $k \le 4$ and **fails at $k = 5$** (a valid
  5-coloring of $\{1, \ldots, 242\}$ has color 0 avoiding all
  distance-81 pairs): the counting margin runs out. Round 28
  records the reduction `omitted-color pair` $\Leftarrow$ `count
  bound`, isolating the genuine content as a pure counting
  statement. -/

/--
  **Theorem (omitted-color pair from a count bound).**

  Let $b \ge 2$. If the color-$c_0$ elements of the window
  $[1, 2b^{k-1}]$ number at least $b^{k-1} + 1$ — captured by a
  Finset $S$ with the stated membership characterization and
  cardinality bound — and the window fits in the domain
  ($2b^{k-1} \le b^k - 1$), then $c_0$ has a distance-$b^{k-1}$
  pair: some $j$ with $1 \le j$, $j + b^{k-1} \le b^k - 1$, and
  $\chi(j) = \chi(j + b^{k-1}) = c_0$.

  Proof: `dpl_pigeonhole` at $D = b^{k-1}$ — the $b^{k-1}$ windows
  $\{r, r + b^{k-1}\}$ cover $[1, 2b^{k-1}]$, so $> b^{k-1}$
  elements force two into one window.

  **Significance**: this is the bridge from `dpl_pigeonhole` to the
  `hOmittedPair` slot of `dpl_recursion_conditional`.
  No mono-avoidance hypothesis is used — fitting the observation
  that $C_{c_0}$ is Rado-unconstrained. After Round 28, closing
  `hOmittedPair` reduces entirely to proving the count bound
  $|C_{c_0} \cap [1, 2b^{k-1}]| \ge b^{k-1} + 1$ — a counting
  statement about the constrained colors' residue, the genuine
  hard content the paper SAT-verifies.
-/
theorem dpl_omitted_pair_of_count {b k : ℕ} (hb : 2 ≤ b)
    (χ : ℕ → ℕ) (c₀ : ℕ) (S : Finset ℕ)
    (hS_def : ∀ m, m ∈ S ↔ 1 ≤ m ∧ m ≤ 2 * b ^ (k - 1) ∧ χ m = c₀)
    (hS_card : b ^ (k - 1) + 1 ≤ S.card)
    (hwin : 2 * b ^ (k - 1) ≤ b ^ k - 1) :
    ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
         χ j = c₀ ∧ χ (j + b ^ (k - 1)) = c₀ := by
  have hd_pos : 1 ≤ b ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hS_subset : ∀ m ∈ S, 1 ≤ m ∧ m ≤ 2 * b ^ (k - 1) := fun m hm =>
    ⟨((hS_def m).mp hm).1, ((hS_def m).mp hm).2.1⟩
  obtain ⟨r, hr1, _, hr_in, hrD_in⟩ :=
    dpl_pigeonhole (b ^ (k - 1)) hd_pos S hS_subset hS_card
  have hr_props := (hS_def r).mp hr_in
  have hrD_props := (hS_def (r + b ^ (k - 1))).mp hrD_in
  exact ⟨r, hr1, by omega, hr_props.2.2, hrD_props.2.2⟩

/-! ### per-level hypothesis predicates.

  The two obligations of `dpl_recursion_conditional`,
  packaged as predicate families indexed by level $(b, k)$. These
  are the inputs the DPL cascade induction consumes; the cascade
  theorem `dpl_cascade` itself is assembled in `K3General.lean`,
  where the base case `dpl_property_k2` is available. -/

/--
  **Compression hypothesis** at level $(b, k)$: in every valid
  mono-free $k$-coloring of $\{1, \ldots, b^k - 1\}$, the multiples
  sub-coloring omits at least one color on
  $\{1, \ldots, b^{k-1}-1\}$.

  Analytic at $k = 2$ (`lem_compress2`), SAT-verified at $k = 3$
  (`lem_compress3_general`), and FALSE at the boundary
  $k = 2(b-1)$ (paper §"Failure of Compression").
-/
def CompressionHyp (b k : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k - 1) k χ →
    AvoidsMonoSolution b (b ^ k - 1) χ →
    ∃ c₀, c₀ < k ∧ ∀ d, 1 ≤ d → d ≤ b ^ (k - 1) - 1 → χ (b * d) ≠ c₀

/--
  **Omitted-color-pair hypothesis** at level $(b, k)$: whenever a
  valid mono-free $k$-coloring's multiples sub-coloring omits a
  color $c_0$, that $c_0$ nonetheless has a distance-$b^{k-1}$
  pair in $\chi$.

  By `dpl_omitted_pair_of_count` this reduces to a pure
  counting bound. SAT-verified for $k \le 4$; FALSE at $k = 5$,
  $b = 3$ (paper §"Breakdown").
-/
def OmittedPairHyp (b k : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k - 1) k χ →
    AvoidsMonoSolution b (b ^ k - 1) χ →
    ∀ c₀, c₀ < k →
      (∀ d, 1 ≤ d → d ≤ b ^ (k - 1) - 1 → χ (b * d) ≠ c₀) →
      ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
           χ j = c₀ ∧ χ (j + b ^ (k - 1)) = c₀

/-! ### the multiple-of-$b$ structural
    lemma.

  The single fact underlying the omitted color's special
  behaviour, promoted from a Round-28 docstring remark to a named
  theorem. For the equation $x + by = bz$, the first coordinate
  of every Rado triple satisfies $x = b(z - y)$ — it is **always a
  positive multiple of $b$**.

  Corollary `rado_triple_fst_not_omitted`: a color $c_0$ that no
  multiple of $b$ uses can never be the color of a Rado triple's
  first element. Combined with monochromaticity, this is why a
  color omitted by all multiples carries no Rado obstruction (cf.
  Round 28). -/

/--
  **Theorem (Rado triple's first element is a multiple).**

  Every Rado triple $(x, y, z)$ for $x + by = bz$ has
  $x = b \cdot m$ for some $m \ge 1$.

  Proof: $x + by = bz$ with $x > 0$ forces $y < z$ (else
  $bz \le by$, contradicting $x > 0$); writing $z = y + w + 1$
  gives $x = b(w + 1)$.

  **Significance**: the structural root of the threshold
  phenomenon. Because $x$ is always a multiple of $b$, the
  monochromatic color of any Rado triple is the color of *some
  multiple of $b$* — so a color the multiples omit is
  Rado-unconstrained, and its distance pair (if any) is a pure
  counting fact, not an avoidance one.
-/
theorem rado_triple_fst_multiple {b x y z : ℕ} (h : IsRadoTriple b x y z) :
    ∃ m, 1 ≤ m ∧ x = b * m := by
  obtain ⟨hx, _, _, heq⟩ := h
  have hyz : y < z := by
    by_contra hcon
    have hcon' : z ≤ y := Nat.le_of_not_lt hcon
    have hle : b * z ≤ b * y := Nat.mul_le_mul (le_refl b) hcon'
    omega
  obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_lt hyz
  refine ⟨w + 1, by omega, ?_⟩
  subst hw
  have hexp : b * (y + w + 1) = b * y + b * (w + 1) := by ring
  omega

/--
  **Corollary (omitted color is never a triple's first
  color).**

  If color $c_0$ is used by no multiple of $b$ within $[1, n]$,
  then the first element $x$ of any Rado triple lying in $[1, n]$
  is not colored $c_0$.

  Proof: `rado_triple_fst_multiple` writes $x = b m$ with
  $m \ge 1$; the omission hypothesis applies.

  **Significance**: with monochromaticity ($\chi(x) = \chi(y) =
  \chi(z)$), this says no monochromatic triple is colored $c_0$ —
  the class $C_{c_0}$ has no Rado obstruction, formalizing the
  Round-28 observation that drives the counting route for the
  omitted color.
-/
theorem rado_triple_fst_not_omitted {b n c₀ : ℕ} (χ : ℕ → ℕ)
    (hOmit : ∀ m, 1 ≤ m → b * m ≤ n → χ (b * m) ≠ c₀)
    {x y z : ℕ} (hxn : x ≤ n) (hRT : IsRadoTriple b x y z) :
    χ x ≠ c₀ := by
  obtain ⟨m, hm_pos, hm_eq⟩ := rado_triple_fst_multiple hRT
  rw [hm_eq]
  exact hOmit m hm_pos (by rw [← hm_eq]; exact hxn)

/-! ### the economical matching-direction
    capstone: iterating `cascade_step`.

  The DPL route (Rounds 23-31) reduces the matching direction to
  TWO hypothesis families — `CompressionHyp` and `OmittedPairHyp`
  — because it routes through the paper's SAT-verified Distance
  Pair Lemma. But `cascade_step`, already proven and
  kernel-pure, gives the recursion DIRECTLY:
  `RadoNumberAtMost b (k-1) (b^{k-1})` $+$ compression
  $\Rightarrow$ `RadoNumberAtMost b k (b^k)` — no DPL, no
  omitted-color pair.

  Round 38 iterates it: from base case `thm_k1` ($R_1(b) = b$)
  and the compression family alone, the matching direction holds
  for ALL $k \ge 1$. This is the strictly more economical
  capstone — ONE hypothesis family, and valid for $b \ge 2$,
  $k \ge 1$ (versus the DPL route's $b \ge 3$, $k \ge 2$).

  The DPL route remains valuable: it formalizes the paper's
  *stated* mechanism (`lem:keypair`). But for the matching
  direction *as an implication*, the cascade route is the lean
  one. -/

/--
  **Cascade compression hypothesis** at level $(b, k)$ — the
  hypothesis `cascade_step` consumes. In every valid mono-free
  $k$-coloring of $\{1, \ldots, b^k\}$, the multiples sub-coloring
  omits a color on $\{1, \ldots, b^{k-1}\}$.

  Differs from `CompressionHyp` (the DPL-route form) only in
  domain: $\{1, \ldots, b^k\}$ here vs $\{1, \ldots, b^k - 1\}$
  there, and $d \le b^{k-1}$ here (covering $b^k$ itself) vs
  $d \le b^{k-1} - 1$ there.
-/
def CascadeCompressionHyp (b k : ℕ) : Prop :=
  ∀ χ : ℕ → ℕ, IsValidColoring (b ^ k) k χ →
    AvoidsMonoSolution b (b ^ k) χ →
    ∃ c₀, c₀ < k ∧ ∀ d, 1 ≤ d → d ≤ b ^ (k - 1) → χ (b * d) ≠ c₀

/--
  **Theorem (iterated cascade — matching direction).**

  For $b \ge 2$ and any $k \ge 1$: if `CascadeCompressionHyp b j`
  holds for every level $j \in [2, k]$, then
  `RadoNumberAtMost b k (b^k)`.

  Proof: induction from base $k = 1$ (`thm_k1`, unconditional)
  with inductive step `cascade_step`.

  **Significance**: the matching direction reduced to a SINGLE
  hypothesis family — `CascadeCompressionHyp` — with no DPL and no
  omitted-color pair. Strictly more economical than the DPL route
  (`dpl_cascade` + `thm_threshold_conditional`), which needs two
  families. Valid for all $b \ge 2$, $k \ge 1$.
-/
theorem thm_cascade_matching (b : ℕ) (hb : 2 ≤ b) :
    ∀ k, 1 ≤ k →
      (∀ j, 2 ≤ j → j ≤ k → CascadeCompressionHyp b j) →
      RadoNumberAtMost b k (b ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    have h := (thm_k1 b hb).2
    simpa using h
  | succ k hk1 ih =>
    intro hHyps
    have hInd : RadoNumberAtMost b (k + 1 - 1) (b ^ (k + 1 - 1)) := by
      have hkk : k + 1 - 1 = k := by omega
      rw [hkk]
      exact ih (fun j hj2 hjk => hHyps j hj2 (by omega))
    exact cascade_step b (k + 1) hb (by omega) hInd
      (hHyps (k + 1) (by omega) (le_refl _))

/--
  **Theorem (economical conditional threshold capstone).**

  For $b \ge 2$ and any $k \ge 1$: if `CascadeCompressionHyp b j`
  holds for every level $j \in [2, k]$, then $R_k(b) = b^k$.

  Proof: `thm_lower` for the lower bound, `thm_cascade_matching`
  for the upper bound.

  **Significance**: the cleanest possible conditional statement of
  the threshold conjecture's matching direction — $R_k(b) = b^k$
  conditional on a SINGLE per-level family, `CascadeCompressionHyp`,
  with zero project axioms in the derivation. The compression
  family is analytic at $k = 2$ (`lem_compress2`-derivable),
  SAT-verified at $k = 3$ (`lem_compress3_general`), and FALSE at
  the boundary $k = 2(b-1)$ — precisely the conjectured threshold.
-/
theorem thm_threshold_via_cascade (b : ℕ) (hb : 2 ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (hHyps : ∀ j, 2 ≤ j → j ≤ k → CascadeCompressionHyp b j) :
    IsRadoNumber b k (b ^ k) :=
  ⟨thm_lower b k hb hk, thm_cascade_matching b hb k hk hHyps⟩

/-! ### the cascade compression hypothesis
    is *equivalent* to the matching conclusion at each level.

  A structural discovery clarifying the cascade route's analytic
  content. `CascadeCompressionHyp b k` is stated on the domain
  $\{1, \ldots, b^k\}$ — but `R_k(b) \le b^k` says **no** valid
  mono-free $k$-coloring of $\{1, \ldots, b^k\}$ exists, so the
  hypothesis's universal premise is **unsatisfiable**. Hence the
  hypothesis is vacuously true precisely when the conclusion
  holds.

  Formally, given the induction hypothesis $R_{k-1}(b) \le
  b^{k-1}$:
  $$
    \text{`CascadeCompressionHyp b k'} \iff \text{`RadoNumberAtMost
    b k (b^k)'}.
  $$

  **Methodological consequence**: the cascade route at level $k$
  does **not** carry independent analytic content beyond the prior
  level. The compression hypothesis is logically the same
  statement as the conclusion at each level — so proving
  `CascadeCompressionHyp b k` requires the same SAT-equivalent
  work as proving the matching direction directly.

  For genuine analytic content, one needs either (a) a
  non-cascade proof at the level (paper's $G^*$-tree for $b=3,
  k=4$), or (b) compression on a SMALLER domain where the premise
  is satisfiable, then extending — the paper's "Color Compression
  Thresholds" route at $n = 2b^2 < b^3$.

  The DPL route's `CompressionHyp` (on $\{1, \ldots, b^k - 1\}$)
  is the genuinely non-vacuous version: valid mono-free
  $k$-colorings of $\{1, \ldots, b^k - 1\}$ DO exist (the
  valuation coloring), so its premise is satisfiable and it
  carries real content. -/

/--
  **Theorem (cascade compression equivalence).**

  For $b \ge 2$, $k \ge 2$, given the induction hypothesis
  $R_{k-1}(b) \le b^{k-1}$: `CascadeCompressionHyp b k`
  $\iff$ `RadoNumberAtMost b k (b^k)`.

  Proof:
  * **→**: `cascade_step`.
  * **←**: vacuously — `RadoNumberAtMost b k (b^k)` makes every
    valid $k$-coloring of $\{1, \ldots, b^k\}$ have a mono, so the
    `AvoidsMonoSolution` premise of `CascadeCompressionHyp b k`
    cannot be satisfied.

  **Significance**: the cascade hypothesis is not an independent
  analytic statement — it is logically equivalent to its own
  matching-direction conclusion (modulo the prior level).
  Explains why `lem_compress3_general` is SAT-verified rather than
  analytically proven, and why my Rounds 38-40 cascade-route
  re-derivations have the same axiom cost as the bespoke routes.
-/
theorem cascade_compression_iff_upper_bound (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hInd : RadoNumberAtMost b (k - 1) (b ^ (k - 1))) :
    CascadeCompressionHyp b k ↔ RadoNumberAtMost b k (b ^ k) := by
  constructor
  · intro hHyp
    exact cascade_step b k hb hk hInd hHyp
  · intro hUpper χ hValid hAvoid
    exact absurd (hUpper χ hValid) hAvoid

/--
  **Theorem (universal abstraction of breakdown).**

  For $b \ge 2$, $k \ge 2$, with the induction hypothesis
  $R_{k-1}(b) \le b^{k-1}$: any breakdown witness — a valid
  mono-free $k$-coloring of $\{1, \ldots, b^k\}$ — *falsifies*
  `CascadeCompressionHyp b k`.

  Proof: by Round 42's equivalence, `CascadeCompressionHyp b k`
  implies `RadoNumberAtMost b k (b^k)`, which contradicts the
  breakdown witness's `AvoidsMonoSolution`.

  **Significance**: the universal abstraction of Round 45 (which
  was the $b = 3, k = 5$ instance). Says: ANY witnessed breakdown
  at level $k$ falsifies the cascade hypothesis at that level.
  The architecture's hypothesis is in EXACT correspondence with
  the conjecture's threshold mechanism — the hypothesis fails
  precisely at the levels where the matching direction fails.
-/
theorem cascade_compression_fails_of_breakdown (b k : ℕ) (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hInd : RadoNumberAtMost b (k - 1) (b ^ (k - 1)))
    (χ : ℕ → ℕ) (hValid : IsValidColoring (b ^ k) k χ)
    (hAvoid : AvoidsMonoSolution b (b ^ k) χ) :
    ¬ CascadeCompressionHyp b k := by
  intro hHyp
  have hUpper : RadoNumberAtMost b k (b ^ k) :=
    (cascade_compression_iff_upper_bound b k hb hk hInd).mp hHyp
  exact hAvoid (hUpper χ hValid)

/-! ### the canonical Rado triple form.

  Round 32 showed $x = bm$. Substituting into $x + by = bz$ gives
  $bm + by = bz$, hence (cancelling $b$) $z = m + y$. So **every
  Rado triple is $(bm,\; y,\; m + y)$** for some $m \ge 1$,
  $y \ge 1$ — a complete two-parameter parametrization.

  This collapses the Rado structure to its essence: a
  monochromatic solution is exactly a choice of $m, y$ with
  $\chi(bm) = \chi(y) = \chi(m + y)$. The reformulation
  `mono_solution_characterization` restates `HasMonoSolution` in
  these terms — the form a SAT encoder or a counting argument
  actually consumes. -/

/--
  **Theorem (canonical Rado triple characterization).**

  For $b \ge 1$: $(x, y, z)$ is a Rado triple for $x + by = bz$
  **iff** $y \ge 1$ and $x = bm$, $z = m + y$ for some $m \ge 1$.

  Proof: forward — `rado_triple_fst_multiple` gives $x = bm$, then
  $bm + by = bz$ cancels to $z = m + y$. Backward — $(bm, y,
  m+y)$ satisfies $bm + by = b(m+y)$ by `ring`, with positivity
  from $b, m, y \ge 1$.

  **Significance**: the full Rado structure in two parameters.
  Every monochromatic solution is a pair $(m, y)$ with $\chi(bm) =
  \chi(y) = \chi(m+y)$ — no existential over a constrained triple,
  just a free choice of $m \ge 1$, $y \ge 1$.
-/
theorem rado_triple_characterization {b : ℕ} (hb : 1 ≤ b) {x y z : ℕ} :
    IsRadoTriple b x y z ↔
    1 ≤ y ∧ ∃ m, 1 ≤ m ∧ x = b * m ∧ z = m + y := by
  constructor
  · intro h
    obtain ⟨hx, hy, hz, heq⟩ := h
    obtain ⟨m, hm_pos, hm_eq⟩ := rado_triple_fst_multiple ⟨hx, hy, hz, heq⟩
    refine ⟨hy, m, hm_pos, hm_eq, ?_⟩
    have hb_pos : 0 < b := by omega
    have hkey : b * (m + y) = b * z := by
      rw [hm_eq] at heq
      calc b * (m + y) = b * m + b * y := by ring
        _ = b * z := heq
    have hmy : m + y = z := Nat.eq_of_mul_eq_mul_left hb_pos hkey
    omega
  · intro ⟨hy, m, hm_pos, hm_eq, hz_eq⟩
    have hb_pos : 0 < b := by omega
    refine ⟨?_, hy, ?_, ?_⟩
    · rw [hm_eq]; exact Nat.mul_pos hb_pos hm_pos
    · omega
    · rw [hm_eq, hz_eq]; ring

/--
  **Corollary (monochromatic solution characterization).**

  For $b \ge 1$: $\chi$ has a monochromatic Rado solution in
  $\{1, \ldots, n\}$ **iff** there exist $m, y \ge 1$ with
  $bm \le n$, $y \le n$, $m + y \le n$, and $\chi(bm) = \chi(y) =
  \chi(m + y)$.

  Proof: `rado_triple_characterization` applied inside the
  existential of `HasMonoSolution`.

  **Significance**: `HasMonoSolution` in the two-parameter form a
  SAT encoder or a counting argument consumes — no constrained
  triple, just free $m, y$.
-/
theorem mono_solution_characterization {b n : ℕ} (hb : 1 ≤ b) (χ : ℕ → ℕ) :
    HasMonoSolution b n χ ↔
    ∃ m y, 1 ≤ m ∧ 1 ≤ y ∧ b * m ≤ n ∧ y ≤ n ∧ m + y ≤ n ∧
           χ (b * m) = χ y ∧ χ y = χ (m + y) := by
  constructor
  · intro ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩
    obtain ⟨hy_pos, m, hm_pos, hm_eq, hz_eq⟩ :=
      (rado_triple_characterization hb).mp hRT
    refine ⟨m, y, hm_pos, hy_pos, ?_, hyn, ?_, ?_, ?_⟩
    · rw [← hm_eq]; exact hxn
    · rw [← hz_eq]; exact hzn
    · rw [← hm_eq]; exact hxy
    · rw [← hz_eq]; exact hyz
  · intro ⟨m, y, hm_pos, hy_pos, hbm_n, hy_n, hmy_n, hc1, hc2⟩
    refine ⟨b * m, y, m + y, hbm_n, hy_n, hmy_n, ?_, hc1, hc2⟩
    exact (rado_triple_characterization hb).mpr ⟨hy_pos, m, hm_pos, rfl, rfl⟩

end RadoNumbers
