/-
  RadoNumbers/LowerBound.lean

  Theorem `thm:lower` ($R_k(b) \ge b^k$). Companion to Li 2026
  "On Rado Numbers for $x + by = bz$".

  Originally established by Chang–De Loera–Wesley
  (`\cite[Lemma 4.1]{CDW}`); the paper restates the proof for
  completeness. We derive `thm_lower` in Lean 4 from three Cat 2
  atomic bridges on the b-adic valuation (each a standard
  number-theory textbook fact). The compositional proof here is
  kernel-pure.

  Proof skeleton:
    1. Witness coloring χ(n) := v_b(n).
    2. Validity: for n ∈ {1, …, b^k - 1}, v_b(n) < k
        (bridge `bAdicVal_lt_pow`).
    3. Avoidance: suppose χ(x) = χ(y) = χ(z) = c with
        x + b·y = b·z. Then z > y (from x > 0 and b ≥ 2);
        x = b·(z - y), so v_b(x) = 1 + v_b(z - y)
        (bridge `bAdicVal_b_mul`). Hence c = 1 + v_b(d) with
        d := z - y, so v_b(d) < c = v_b(y). Ultrametric
        (bridge `bAdicVal_add_of_lt`) gives
        v_b(z) = v_b(y + d) = v_b(d) = c - 1, contradicting
        v_b(z) = c.
-/

import RadoNumbers.Basic
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Cat 2 atomic bridges — b-adic valuation properties.

  Each bridge is a standard number-theory textbook fact (Ireland &
  Rosen, *A Classical Introduction to Modern Number Theory*,
  Springer 1990, Ch 1; Apostol, *Introduction to Analytic Number
  Theory*, Springer 1976, §4). Encoded here as Cat 2 axioms
  pending Mathlib derivation. Mathlib's `multiplicity` and
  `padicValNat` cover related infrastructure but their direct
  application to the recursive `bAdicVal` of `Basic.lean` is
  deferred.
-/

/-- For `b ≥ 2` and `0 < n < b^k`, the b-adic valuation satisfies
    `v_b(n) < k`.

    ANALYTICALLY PROVEN Round 16 — previously a Cat 2
    axiom. Strong induction on `n`: if `b ∤ n` then `v_b(n) = 0 < k`
    (since `0 < n < b^k` forces `k ≥ 1`); if `b ∣ n` then
    `v_b(n) = 1 + v_b(n/b)` with `n/b < b^{k-1}`, so the IH gives
    `v_b(n/b) < k - 1`, hence `v_b(n) < k`. -/
theorem bAdicVal_lt_pow (b k n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) (h : n < b ^ k) :
    bAdicVal b n < k := by
  have hb_pos : 0 < b := by omega
  -- Strong induction on `n`, with `k` (here `j`) universally quantified.
  have main : ∀ m, 0 < m → ∀ j, m < b ^ j → bAdicVal b m < j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm j hmj
      -- `j ≥ 1`: else `m < b^0 = 1` contradicts `0 < m`.
      have hj_pos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · rw [hj0, pow_zero] at hmj; omega
        · exact hj0
      by_cases hmod : m % b = 0
      · -- `b ∣ m`: unfold to `1 + bAdicVal b (m/b)`.
        have hdvd : b ∣ m := Nat.dvd_of_mod_eq_zero hmod
        have hm_ge_b : b ≤ m := Nat.le_of_dvd hm hdvd
        have hmb_pos : 0 < m / b := Nat.div_pos hm_ge_b hb_pos
        have hmb_lt : m / b < m := Nat.div_lt_self hm hb
        have hm_eq : b * (m / b) = m := Nat.mul_div_cancel' hdvd
        have hpow_eq : b ^ j = b * b ^ (j - 1) := by
          conv_lhs => rw [show j = (j - 1) + 1 from by omega]
          rw [pow_succ]; ring
        have hmb_lt_pow : m / b < b ^ (j - 1) := by
          have hstep : b * (m / b) < b * b ^ (j - 1) := by
            rw [hm_eq]; omega
          exact Nat.lt_of_mul_lt_mul_left hstep
        have hrec : bAdicVal b (m / b) < j - 1 :=
          IH (m / b) hmb_lt hmb_pos (j - 1) hmb_lt_pow
        have hcond : 2 ≤ b ∧ 0 < m ∧ m % b = 0 := ⟨hb, hm, hmod⟩
        have hunfold : bAdicVal b m = 1 + bAdicVal b (m / b) := by
          conv_lhs => rw [bAdicVal]
          rw [dif_pos hcond]
        rw [hunfold]; omega
      · -- `b ∤ m`: `bAdicVal b m = 0 < j`.
        have hcond : ¬ (2 ≤ b ∧ 0 < m ∧ m % b = 0) := by
          rintro ⟨_, _, hh⟩; exact hmod hh
        have hunfold : bAdicVal b m = 0 := by
          conv_lhs => rw [bAdicVal]
          rw [dif_neg hcond]
        rw [hunfold]; exact hj_pos
  exact main n hn k h

/-- For `b ≥ 2` and `0 < n`, multiplication by `b` increments the
    b-adic valuation by 1: `v_b(b · n) = 1 + v_b(n)`.

    ANALYTICALLY PROVEN Round 16 — previously a Cat 2
    axiom, now derived by directly unfolding the recursive
    `bAdicVal` definition. Since `b ∣ b · n` and `b · n > 0`, the
    `dite` branch fires, giving `1 + bAdicVal b ((b·n)/b) =
    1 + bAdicVal b n`. -/
theorem bAdicVal_b_mul (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) :
    bAdicVal b (b * n) = 1 + bAdicVal b n := by
  have hb_pos : 0 < b := by omega
  have hbn_pos : 0 < b * n := Nat.mul_pos hb_pos hn
  have hmod : b * n % b = 0 := Nat.mul_mod_right b n
  have hcond : 2 ≤ b ∧ 0 < b * n ∧ b * n % b = 0 := ⟨hb, hbn_pos, hmod⟩
  have hdiv : b * n / b = n := Nat.mul_div_cancel_left n hb_pos
  have hunfold : bAdicVal b (b * n) = 1 + bAdicVal b (b * n / b) := by
    conv_lhs => rw [bAdicVal]
    rw [dif_pos hcond]
  rw [hunfold, hdiv]

/-- Ultrametric, strict-comparison form: if `v_b(d) < v_b(y)`, then
    `v_b(y + d) = v_b(d)`.

    ANALYTICALLY PROVEN Round 17 — previously a Cat 2
    axiom. Strong induction on `d` (with `y` universally
    quantified). Since `v_b(d) < v_b(y)`, `v_b(y) > 0` so `b ∣ y`.
    * If `b ∤ d`: `v_b(d) = 0`, and `b ∣ y, b ∤ d` give `b ∤ (y+d)`,
      so `v_b(y+d) = 0 = v_b(d)`.
    * If `b ∣ d`: `v_b(d) = 1 + v_b(d/b)`, `v_b(y) = 1 + v_b(y/b)`,
      so `v_b(d/b) < v_b(y/b)`; `(y+d)/b = y/b + d/b`, and the IH
      gives `v_b(y/b + d/b) = v_b(d/b)`, hence `v_b(y+d) =
      1 + v_b(d/b) = v_b(d)`. -/
theorem bAdicVal_add_of_lt (b y d : ℕ) (hb : 2 ≤ b)
    (hy : 0 < y) (hd : 0 < d) (h : bAdicVal b d < bAdicVal b y) :
    bAdicVal b (y + d) = bAdicVal b d := by
  have hb_pos : 0 < b := by omega
  -- Strong induction on `d`, with `y` universally quantified.
  have main : ∀ d', 0 < d' → ∀ y', 0 < y' →
      bAdicVal b d' < bAdicVal b y' →
      bAdicVal b (y' + d') = bAdicVal b d' := by
    intro d'
    induction d' using Nat.strong_induction_on with
    | _ d' IH =>
      intro hd' y' hy' hlt
      -- `bAdicVal b y' > 0`, so `b ∣ y'`.
      have hy'_val_pos : 0 < bAdicVal b y' := by omega
      have hmod_y : y' % b = 0 := by
        by_contra hmy
        have hzero : bAdicVal b y' = 0 := by
          have hcond_neg : ¬ (2 ≤ b ∧ 0 < y' ∧ y' % b = 0) := by
            rintro ⟨_, _, hh⟩; exact hmy hh
          conv_lhs => rw [bAdicVal]
          rw [dif_neg hcond_neg]
        omega
      have hdvd_y : b ∣ y' := Nat.dvd_of_mod_eq_zero hmod_y
      by_cases hmod_d : d' % b = 0
      · -- `b ∣ d'`.
        have hdvd_d : b ∣ d' := Nat.dvd_of_mod_eq_zero hmod_d
        have hcond_d : 2 ≤ b ∧ 0 < d' ∧ d' % b = 0 := ⟨hb, hd', hmod_d⟩
        have hcond_y : 2 ≤ b ∧ 0 < y' ∧ y' % b = 0 := ⟨hb, hy', hmod_y⟩
        have hunfold_d : bAdicVal b d' = 1 + bAdicVal b (d' / b) := by
          conv_lhs => rw [bAdicVal]
          rw [dif_pos hcond_d]
        have hunfold_y : bAdicVal b y' = 1 + bAdicVal b (y' / b) := by
          conv_lhs => rw [bAdicVal]
          rw [dif_pos hcond_y]
        have hdb_lt : d' / b < d' := Nat.div_lt_self hd' hb
        have hdb_pos : 0 < d' / b := Nat.div_pos (Nat.le_of_dvd hd' hdvd_d) hb_pos
        have hyb_pos : 0 < y' / b := Nat.div_pos (Nat.le_of_dvd hy' hdvd_y) hb_pos
        have hlt' : bAdicVal b (d' / b) < bAdicVal b (y' / b) := by
          rw [hunfold_d, hunfold_y] at hlt; omega
        have hrec := IH (d' / b) hdb_lt hdb_pos (y' / b) hyb_pos hlt'
        have hd'_eq : d' = b * (d' / b) := (Nat.mul_div_cancel' hdvd_d).symm
        have hadd_div : (y' + d') / b = y' / b + d' / b := by
          conv_lhs => rw [hd'_eq]
          rw [Nat.add_mul_div_left _ _ hb_pos]
        have hmod_sum : (y' + d') % b = 0 := by
          rw [Nat.add_mod, hmod_y, hmod_d]; simp
        have hcond_sum : 2 ≤ b ∧ 0 < y' + d' ∧ (y' + d') % b = 0 :=
          ⟨hb, by omega, hmod_sum⟩
        have hunfold_sum : bAdicVal b (y' + d') = 1 + bAdicVal b ((y' + d') / b) := by
          conv_lhs => rw [bAdicVal]
          rw [dif_pos hcond_sum]
        rw [hunfold_sum, hadd_div, hrec, hunfold_d]
      · -- `b ∤ d'`.
        have hcond_d_neg : ¬ (2 ≤ b ∧ 0 < d' ∧ d' % b = 0) := by
          rintro ⟨_, _, hh⟩; exact hmod_d hh
        have hunfold_d : bAdicVal b d' = 0 := by
          conv_lhs => rw [bAdicVal]
          rw [dif_neg hcond_d_neg]
        have hmod_sum_ne : (y' + d') % b ≠ 0 := by
          have heq : (y' + d') % b = d' % b := by
            rw [Nat.add_mod, hmod_y, Nat.zero_add,
                Nat.mod_mod_of_dvd d' (dvd_refl b)]
          rw [heq]; exact hmod_d
        have hcond_sum_neg : ¬ (2 ≤ b ∧ 0 < y' + d' ∧ (y' + d') % b = 0) := by
          rintro ⟨_, _, hh⟩; exact hmod_sum_ne hh
        have hunfold_sum : bAdicVal b (y' + d') = 0 := by
          conv_lhs => rw [bAdicVal]
          rw [dif_neg hcond_sum_neg]
        rw [hunfold_sum, hunfold_d]
  exact main d hd y hy h

/-! ### structural properties of the
    valuation coloring.

  The valuation coloring $\chi_v(n) = v_b(n) \bmod k$ is the
  canonical witness for `thm_lower` ($R_k(b) \ge b^k$). Round 43
  surfaces its concrete structure:

  * $v_b(1) = 0$ (units have zero valuation).
  * $v_b(b) = 1$ (the first multiple has valuation 1).
  * **`bAdicVal_multiples_omit_zero`**: for every positive
    multiple $b \cdot d$ ($d \ge 1$), $v_b(b \cdot d) \ne 0$ —
    the valuation coloring's multiples sub-coloring **omits color
    0**.

  This is a concrete realization of compression: the valuation
  coloring witnesses `CompressionHyp` non-vacuously (its multiples
  use $\{1, 2, \ldots\}$, omitting $0$). The same structural fact
  works for `CompressionHyp b k` on the $b^k - 1$ domain at every
  $k \ge 1$.

  The hypothesis `CompressionHyp b k` (DPL route) is therefore
  realized for at least one valid mono-free coloring at every
  level — confirming that it is a *genuine* non-vacuous
  hypothesis, unlike `CascadeCompressionHyp` (Round 42's
  vacuity-equivalence). -/

/--
  **Lemma — $v_b(1) = 0$.**

  For $b \ge 2$: the b-adic valuation of $1$ is $0$. Proof: the
  recursive definition's `dite` branch requires $b \mid n$;
  $b \nmid 1$ (since $1 < b$).
-/
theorem bAdicVal_one {b : ℕ} (hb : 2 ≤ b) : bAdicVal b 1 = 0 := by
  conv_lhs => rw [bAdicVal]
  rw [dif_neg]
  intro h
  have h_mod : (1 : ℕ) % b = 1 := Nat.mod_eq_of_lt (by omega)
  omega

/--
  **Lemma — $v_b(b) = 1$.**

  For $b \ge 2$: the b-adic valuation of $b$ is $1$. Combines
  `bAdicVal_b_mul` at $d = 1$ with `bAdicVal_one`.
-/
theorem bAdicVal_b_value {b : ℕ} (hb : 2 ≤ b) : bAdicVal b b = 1 := by
  have h := bAdicVal_b_mul b 1 hb (by norm_num)
  rw [Nat.mul_one] at h
  rw [h, bAdicVal_one hb]

/--
  **Theorem (valuation's multiples omit zero).**

  For $b \ge 2$ and any $d \ge 1$: $v_b(b \cdot d) \ne 0$ —
  the multiples sub-coloring of the valuation coloring **omits
  color 0**.

  Proof: `bAdicVal_b_mul` gives $v_b(b d) = 1 + v_b(d) \ge 1 \ne
  0$.

  **Significance**: a concrete realization of compression by the
  canonical lower-bound construction. The valuation coloring
  witnesses `CompressionHyp b k` (DPL route) non-vacuously at
  every level $k$ — confirming the hypothesis is a *genuine*
  constraint with at least one inhabitant, unlike the
  vacuity-equivalent `CascadeCompressionHyp`.
-/
theorem bAdicVal_multiples_omit_zero {b : ℕ} (hb : 2 ≤ b) {d : ℕ} (hd : 1 ≤ d) :
    bAdicVal b (b * d) ≠ 0 := by
  rw [bAdicVal_b_mul b d hb hd]
  omega

/-! ### the valuation realizes the
    omitted-color distance pair (ultrametric).

  Round 43 showed the valuation coloring's multiples omit color 0
  — realizing `CompressionHyp` non-vacuously. Round 44 closes the
  story: for $k \ge 2$, the **specific pair** $(1, 1 + b^{k-1})$
  is both color 0 under the valuation, so the valuation also
  realizes `OmittedPairHyp` non-vacuously at every level.

  The mechanism is the **ultrametric inequality**: since
  $v_b(b^{k-1}) = k - 1 \ge 1 > 0 = v_b(1)$, the strict
  ultrametric (`bAdicVal_add_of_lt`) gives $v_b(b^{k-1} + 1) =
  v_b(1) = 0$.

  So at every level $k \ge 2$, the valuation coloring concretely
  inhabits the **full DPL hypothesis family** — both
  `CompressionHyp` and `OmittedPairHyp`. This shows the DPL route
  is not vacuous; the architecture's hypothesis families are
  non-empty even when fully analytic. (Of course, the universal
  $\forall \chi$ in those families requires more than one
  inhabitant — that is the SAT-hard content.) -/

/--
  **Theorem (valuation's omitted-color distance pair).**

  For $b \ge 2$ and $k \ge 2$: $v_b(1 + b^{k-1}) = 0$.

  Proof: $v_b(b^{k-1}) = 1 + v_b(b^{k-2}) \ge 1 > 0 = v_b(1)$, so
  the strict ultrametric `bAdicVal_add_of_lt` gives
  $v_b(b^{k-1} + 1) = v_b(1) = 0$.

  **Significance**: under the valuation coloring, the pair
  $(1, 1 + b^{k-1})$ is monochromatic at color 0 — exactly the
  distance-$b^{k-1}$ pair that `OmittedPairHyp b k` asks for at
  the omitted color $c_0 = 0$. The valuation thus realizes both
  DPL hypothesis families non-vacuously at every $k \ge 2$.
-/
theorem bAdicVal_one_plus_pow_eq_zero {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    bAdicVal b (1 + b ^ (k - 1)) = 0 := by
  have hb_pos : 0 < b := by omega
  have h_pow_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
  have h_v_pow_ge : 1 ≤ bAdicVal b (b ^ (k - 1)) := by
    have hk_eq : k - 1 = (k - 2) + 1 := by omega
    have h_decomp : b ^ (k - 1) = b * b ^ (k - 2) := by
      conv_lhs => rw [hk_eq, pow_succ]
      ring
    rw [h_decomp, bAdicVal_b_mul b (b ^ (k - 2)) hb (Nat.pow_pos hb_pos)]
    omega
  have h_v1 : bAdicVal b 1 = 0 := bAdicVal_one hb
  have h_lt : bAdicVal b 1 < bAdicVal b (b ^ (k - 1)) := by omega
  have h_comm : 1 + b ^ (k - 1) = b ^ (k - 1) + 1 := by ring
  rw [h_comm,
      bAdicVal_add_of_lt b (b ^ (k - 1)) 1 hb h_pow_pos (by norm_num) h_lt,
      h_v1]

/--
  **Corollary (valuation's distance pair monochromatic
  at 0).**

  For $b \ge 2$ and $k \ge 2$: $v_b(1) = v_b(1 + b^{k-1})$ (both
  equal to $0$) — the distance-$b^{k-1}$ pair $(1, 1 + b^{k-1})$
  is monochromatic at color 0 under the valuation coloring.
-/
theorem bAdicVal_distance_pair_color_zero {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    bAdicVal b 1 = bAdicVal b (1 + b ^ (k - 1)) := by
  rw [bAdicVal_one hb, bAdicVal_one_plus_pow_eq_zero hb hk]

/-! ### universal abstraction of Round 44.

  Round 44 showed $v_b(1 + b^{k-1}) = 0$ — the specific pair
  $(1, 1 + b^{k-1})$ is both color 0. Round 47 generalizes: for
  **any b-unit** $y$ (any $y$ with $v_b(y) = 0$), the pair
  $(y, y + b^{k-1})$ is both color 0.

  The strict ultrametric $v_b(y) = 0 < k - 1 \le v_b(b^{k-1})$
  gives $v_b(b^{k-1} + y) = v_b(y) = 0$. Round 44 is the $y = 1$
  case.

  Consequence: the valuation coloring has *many* distance-$b^{k-1}$
  pairs at color 0 — every b-unit gives one. In the range
  $[1, b^k - 1 - b^{k-1}]$ there are roughly $b^{k-1}(b - 2)/(b-1)$
  b-units, so the omitted-color class $C_0$ is large and pair-rich
  under the valuation. -/

/--
  **Theorem (b-unit lifts to color 0 at distance $b^{k-1}$).**

  For $b \ge 2$, $k \ge 2$, and any positive $y$ with $v_b(y) = 0$:
  $v_b(y + b^{k-1}) = 0$.

  Proof: strict ultrametric `bAdicVal_add_of_lt` applied to
  $b^{k-1} + y$ (rewriting via commutativity), using
  $v_b(b^{k-1}) \ge 1 > 0 = v_b(y)$.

  Generalizes Round 44 (`bAdicVal_one_plus_pow_eq_zero`, the
  $y = 1$ case).
-/
theorem bAdicVal_add_pow_zero_of_unit {b k y : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hy_pos : 0 < y) (hy_val : bAdicVal b y = 0) :
    bAdicVal b (y + b ^ (k - 1)) = 0 := by
  have hb_pos : 0 < b := by omega
  have h_pow_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
  have h_v_pow_ge : 1 ≤ bAdicVal b (b ^ (k - 1)) := by
    have hk_eq : k - 1 = (k - 2) + 1 := by omega
    have h_decomp : b ^ (k - 1) = b * b ^ (k - 2) := by
      conv_lhs => rw [hk_eq, pow_succ]
      ring
    rw [h_decomp, bAdicVal_b_mul b (b ^ (k - 2)) hb (Nat.pow_pos hb_pos)]
    omega
  have h_lt : bAdicVal b y < bAdicVal b (b ^ (k - 1)) := by
    rw [hy_val]; omega
  have h_comm : y + b ^ (k - 1) = b ^ (k - 1) + y := by ring
  rw [h_comm, bAdicVal_add_of_lt b (b ^ (k - 1)) y hb h_pow_pos hy_pos h_lt]
  exact hy_val

/-! ### valuation of $b^c \cdot u$ and
    distance pairs for interior colors.

  Toward formalizing that the valuation coloring realizes the
  full Distance Pair Lemma at every level $k \ge 2$:

  * **`bAdicVal_b_pow_mul_unit`** — for a b-unit $u$ (i.e.,
    $v_b(u) = 0$) and any $c \ge 0$: $v_b(b^c \cdot u) = c$. The
    structural identity underlying the valuation coloring's
    color stratification.
  * **`bAdicVal_distance_pair_color_c`** — for any interior color
    $c \in [0, k-2]$ and any b-unit $u$: the pair $(b^c u,
    b^c u + b^{k-1})$ is both color $c$ under the valuation.

  Generalizes Round 47 (the $c = 0$ case). Handles all "interior"
  colors via the strict ultrametric (which needs the inequality
  $c < k - 1$ for the valuations to differ). The highest color
  $c = k - 1$ needs a separate argument. -/

/--
  **Lemma — $v_b(b^c \cdot u) = c$ for b-units.**

  For $b \ge 2$ and a b-unit $u > 0$ (i.e., $v_b(u) = 0$): for
  every $c \ge 0$, $v_b(b^c \cdot u) = c$.

  Proof: induction on $c$, with `bAdicVal_b_mul` providing the
  step $v_b(b \cdot (b^c u)) = 1 + v_b(b^c u)$.

  **Significance**: the structural identity of the valuation
  coloring's color stratification — color $c$ is exactly the set
  $\{b^c \cdot u : u \text{ is a b-unit}\}$.
-/
theorem bAdicVal_b_pow_mul_unit {b : ℕ} (hb : 2 ≤ b) {u : ℕ}
    (hu_pos : 0 < u) (hu_val : bAdicVal b u = 0) (c : ℕ) :
    bAdicVal b (b ^ c * u) = c := by
  induction c with
  | zero =>
    simp only [pow_zero, one_mul]
    exact hu_val
  | succ c ih =>
    have hb_pos : 0 < b := by omega
    have h_pos : 0 < b ^ c * u := Nat.mul_pos (Nat.pow_pos hb_pos) hu_pos
    have h_decomp : b ^ (c + 1) * u = b * (b ^ c * u) := by ring
    rw [h_decomp, bAdicVal_b_mul b (b ^ c * u) hb h_pos, ih]
    omega

/--
  **Theorem (interior-color distance pair under valuation).**

  For $b \ge 2$, $k \ge 2$, any *interior* color $c \le k - 2$,
  and any b-unit $u > 0$ (i.e., $v_b(u) = 0$): the pair
  $(b^c \cdot u, \; b^c \cdot u + b^{k-1})$ is monochromatic at
  color $c$ under the valuation coloring.

  Proof: $v_b(b^c \cdot u) = c < k - 1 = v_b(b^{k-1})$, so the
  strict ultrametric `bAdicVal_add_of_lt` gives $v_b(b^{k-1} +
  b^c u) = v_b(b^c u) = c$.

  Generalizes Round 47 ($c = 0$). Handles all interior colors
  uniformly; the boundary color $c = k - 1$ needs a separate
  argument.
-/
theorem bAdicVal_distance_pair_color_c {b k c u : ℕ}
    (hb : 2 ≤ b) (hk : 2 ≤ k) (hc : c ≤ k - 2)
    (hu_pos : 0 < u) (hu_val : bAdicVal b u = 0) :
    bAdicVal b (b ^ c * u + b ^ (k - 1)) = c := by
  have hb_pos : 0 < b := by omega
  have h_target_pos : 0 < b ^ c * u := Nat.mul_pos (Nat.pow_pos hb_pos) hu_pos
  have h_pow_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
  have h_v_target : bAdicVal b (b ^ c * u) = c :=
    bAdicVal_b_pow_mul_unit hb hu_pos hu_val c
  have h_v_pow : bAdicVal b (b ^ (k - 1)) = k - 1 := by
    have h := bAdicVal_b_pow_mul_unit hb (by norm_num : (0 : ℕ) < 1)
              (bAdicVal_one hb) (k - 1)
    rwa [Nat.mul_one] at h
  have h_lt : bAdicVal b (b ^ c * u) < bAdicVal b (b ^ (k - 1)) := by
    rw [h_v_target, h_v_pow]; omega
  have h_comm : b ^ c * u + b ^ (k - 1) = b ^ (k - 1) + b ^ c * u := by ring
  rw [h_comm,
      bAdicVal_add_of_lt b (b ^ (k - 1)) (b ^ c * u) hb h_pow_pos h_target_pos h_lt,
      h_v_target]

/-! ### boundary-color distance pair
    under the valuation.

  Round 48's strict-ultrametric argument breaks at the highest
  color $c = k - 1$ (the ultrametric is non-strict when the
  valuations match). Round 49 supplies the boundary case via a
  different pair: $(b^{k-1}, 2 b^{k-1})$. For $b \ge 3$, the
  element $2$ is a b-unit ($v_b(2) = 0$ since $2 < b$), so
  $v_b(2 b^{k-1}) = k - 1$ matches $v_b(b^{k-1}) = k - 1$.

  Together with Round 48, this completes the realization: under
  the valuation coloring (for $b \ge 3$), **every color** $c \in
  [0, k-1]$ has a concrete distance-$b^{k-1}$ pair. The
  valuation realizes the full `DistancePairProperty` conclusion
  non-vacuously.

  ($b = 2$ is excluded because $v_b(2) = 1 \ne 0$ there; for $b =
  2$, the pair $(b^{k-1}, 2 b^{k-1}) = (2^{k-1}, 2^k)$ has
  $v_b(2^k) = k$, color $k \bmod k = 0$, NOT $k - 1$. Consistent
  with the conjecture's $b = 2$ threshold $2(b-1) = 2$ being more
  restrictive.) -/

/--
  **Lemma — $v_b(2) = 0$ for $b \ge 3$.**

  For $b \ge 3$: $2$ is a b-unit (not divisible by $b$). Proof:
  the recursive definition's `dite` branch needs $b \mid 2$;
  $2 < b$ ensures $2 \% b = 2 \ne 0$.
-/
theorem bAdicVal_two_eq_zero {b : ℕ} (hb : 3 ≤ b) : bAdicVal b 2 = 0 := by
  conv_lhs => rw [bAdicVal]
  rw [dif_neg]
  intro h
  have h_mod : (2 : ℕ) % b = 2 := Nat.mod_eq_of_lt (by omega)
  omega

/--
  **Theorem (boundary-color distance pair).**

  For $b \ge 3$ and $k \ge 1$: $v_b(b^{k-1}) = v_b(2 b^{k-1}) =
  k - 1$. The pair $(b^{k-1}, 2 b^{k-1})$ is monochromatic at
  color $k - 1$ under the valuation coloring.

  Proof: both via `bAdicVal_b_pow_mul_unit` — $b^{k-1} = b^{k-1}
  \cdot 1$ (with $u = 1$ a b-unit), $2 b^{k-1} = b^{k-1} \cdot 2$
  (with $u = 2$ a b-unit for $b \ge 3$).
-/
theorem bAdicVal_distance_pair_color_kminus1 {b k : ℕ} (hb : 3 ≤ b) :
    bAdicVal b (b ^ (k - 1)) = k - 1 ∧
    bAdicVal b (b ^ (k - 1) + b ^ (k - 1)) = k - 1 := by
  have hb2 : 2 ≤ b := by omega
  have h1 : bAdicVal b (b ^ (k - 1)) = k - 1 := by
    have h := bAdicVal_b_pow_mul_unit hb2 (by norm_num : (0 : ℕ) < 1)
              (bAdicVal_one hb2) (k - 1)
    rwa [Nat.mul_one] at h
  refine ⟨h1, ?_⟩
  have h_sum : b ^ (k - 1) + b ^ (k - 1) = b ^ (k - 1) * 2 := by ring
  rw [h_sum]
  exact bAdicVal_b_pow_mul_unit hb2 (by norm_num : (0 : ℕ) < 2)
        (bAdicVal_two_eq_zero hb) (k - 1)

/-! ### the valuation realizes
    `DistancePairProperty` body at every color.

  Rounds 47–49 supplied distance-$b^{k-1}$ pairs at color 0, interior colors $c \in [1, k-2]$, and
  the boundary color $c = k - 1$ under the valuation
  coloring. Round 50 bundles them: for every color $c \in [0,
  k-1]$, the valuation provides an explicit witness $j$.

  This is the concrete realization of the `DistancePairProperty`
  body for the canonical mono-free coloring at every level $k \ge
  2$ (for $b \ge 3$). The valuation non-vacuously inhabits the
  DPL hypothesis — concretely showing that the matching direction's
  DPL premise is realizable, not just vacuously possible.

  The witness function:
  $j(c) = \begin{cases}
    1 & \text{if } c = 0 \\
    b^c & \text{if } 1 \le c \le k - 2 \\
    b^{k-1} & \text{if } c = k - 1
  \end{cases}$ -/

/--
  **Theorem (valuation realizes DPP body at every color).**

  For $b \ge 3$, $k \ge 2$: for every color $c < k$, there exists
  $j$ with $1 \le j$, $j + b^{k-1} \le b^k - 1$, and
  $v_b(j) = v_b(j + b^{k-1}) = c$.

  Witnesses:
  * $c = 0$: $j = 1$.
  * $c \in [1, k - 2]$: $j = b^c$.
  * $c = k - 1$: $j = b^{k-1}$.

  All three cases verified via Rounds 47–49. The valuation
  concretely supplies the `DistancePairProperty b k` body at
  every level — non-vacuous inhabitation of the DPL hypothesis.
-/
theorem bAdicVal_distance_pair_witness (b k : ℕ) (hb : 3 ≤ b) (hk : 2 ≤ k) :
    ∀ c, c < k → ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
                       bAdicVal b j = c ∧
                       bAdicVal b (j + b ^ (k - 1)) = c := by
  intro c hc
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_pkm1_pos : 1 ≤ b ^ (k - 1) := Nat.one_le_pow _ _ hb_pos
  -- b^k = b · b^(k-1).
  have h_bk_decomp : b ^ k = b * b ^ (k - 1) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq, pow_succ]
    ring
  -- Key: 2 * b^(k-1) + 1 ≤ b^k (for b ≥ 3, since b * b^(k-1) ≥ 3 * b^(k-1)).
  have h_2pkm1_lt_bk : 2 * b ^ (k - 1) + 1 ≤ b ^ k := by
    have h3 : 3 * b ^ (k - 1) ≤ b ^ k := by
      rw [h_bk_decomp]
      exact Nat.mul_le_mul_right (b ^ (k - 1)) hb
    omega
  -- Case split on the target color.
  by_cases hc0 : c = 0
  · -- Case c = 0: j = 1.
    subst hc0
    refine ⟨1, le_refl _, ?_, bAdicVal_one hb2, ?_⟩
    · omega
    · exact bAdicVal_add_pow_zero_of_unit hb2 hk (by norm_num) (bAdicVal_one hb2)
  · by_cases hck : c = k - 1
    · -- Case c = k - 1: j = b^(k-1).
      subst hck
      obtain ⟨h1, h2⟩ := bAdicVal_distance_pair_color_kminus1 (b := b) (k := k) hb
      refine ⟨b ^ (k - 1), h_pkm1_pos, ?_, h1, h2⟩
      omega
    · -- Case c ∈ [1, k - 2]: j = b^c.
      have hc_ge_1 : 1 ≤ c := by omega
      have hc_le_km2 : c ≤ k - 2 := by omega
      have h_pc_pos : 1 ≤ b ^ c := Nat.one_le_pow _ _ hb_pos
      have h_pc_le_pkm2 : b ^ c ≤ b ^ (k - 2) :=
        Nat.pow_le_pow_right hb_pos hc_le_km2
      have h_pkm2_le_pkm1 : b ^ (k - 2) ≤ b ^ (k - 1) :=
        Nat.pow_le_pow_right hb_pos (by omega)
      -- bAdicVal b (b^c) = c via Round 48.
      have h_v_pc : bAdicVal b (b ^ c) = c := by
        have h := bAdicVal_b_pow_mul_unit hb2 (by norm_num : (0 : ℕ) < 1)
                  (bAdicVal_one hb2) c
        rwa [Nat.mul_one] at h
      -- bAdicVal b (b^c + b^(k-1)) = c via Round 48's distance-pair lemma at u=1.
      have h_v_sum : bAdicVal b (b ^ c + b ^ (k - 1)) = c := by
        have h := bAdicVal_distance_pair_color_c (b := b) (k := k) (c := c) (u := 1)
                  hb2 hk hc_le_km2 (by norm_num) (bAdicVal_one hb2)
        rwa [Nat.mul_one] at h
      refine ⟨b ^ c, h_pc_pos, ?_, h_v_pc, h_v_sum⟩
      -- b^c + b^(k-1) ≤ b^k - 1
      have h_sum_le : b ^ c + b ^ (k - 1) ≤ 2 * b ^ (k - 1) := by
        have : b ^ c ≤ b ^ (k - 1) := le_trans h_pc_le_pkm2 h_pkm2_le_pkm1
        omega
      omega

/-! ### extract valuation's mono-freeness
    and validity as standalone theorems.

  `thm_lower`'s proof packages mono-freeness inline. Round 51
  extracts:

  * `bAdicVal_avoidsMono` — the valuation coloring avoids mono
    Rado solutions on EVERY domain (the proof doesn't use the
    domain bound).
  * `bAdicVal_isValidColoring` — the valuation is a valid
    $k$-coloring of $\{1, \ldots, b^k - 1\}$.

  These let `thm_lower` be re-derived as a one-liner, and let
  Round 51's capstone `dpp_body_realized` package the valuation
  cleanly with its DPP-body realization. -/

/--
  **Lemma — `bAdicVal_avoidsMono`.**

  For $b \ge 2$ and any $n$: $v_b$ avoids monochromatic Rado
  solutions on $\{1, \ldots, n\}$ — i.e., no Rado triple
  $(x, y, z)$ with positive components is monochromatic under
  $v_b$.

  Proof: ultrametric. If $(x, y, z)$ is a Rado triple with
  $v_b(x) = v_b(y) = v_b(z)$, then $x = b(z-y)$ gives $v_b(x) =
  1 + v_b(z-y)$; together with $v_b(z) = v_b(y + (z-y)) =
  v_b(z-y)$ (strict ultrametric since $v_b(z-y) < v_b(x) =
  v_b(y)$), we get $v_b(z) = v_b(x) - 1 < v_b(x)$, contradicting
  $v_b(z) = v_b(x)$.

  The proof is INDEPENDENT of the domain — the valuation coloring
  is universally mono-free against the Rado equation.
-/
theorem bAdicVal_avoidsMono {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    AvoidsMonoSolution b n (bAdicVal b) := by
  rintro ⟨x, y, z, _hxn, _hyn, _hzn, ⟨_hx, hy, _hz, heq⟩, hxy, hyz⟩
  have hb_pos : 0 < b := by omega
  have h_by_lt_bz : b * y < b * z := by linarith
  have hzgty : y < z := (Nat.mul_lt_mul_left hb_pos).mp h_by_lt_bz
  set d : ℕ := z - y with hd_def
  have hd_pos : 0 < d := Nat.sub_pos_of_lt hzgty
  have hzeq : z = y + d := by
    rw [hd_def, Nat.add_sub_cancel' (Nat.le_of_lt hzgty)]
  have hxeq : x = b * d := by
    have : b * z = b * y + b * d := by rw [hzeq]; ring
    omega
  have hvbx : bAdicVal b x = 1 + bAdicVal b d := by
    rw [hxeq]; exact bAdicVal_b_mul b d hb hd_pos
  set c : ℕ := bAdicVal b y with _hc_def
  have hvbx_c : bAdicVal b x = c := hxy
  have hc_eq : c = 1 + bAdicVal b d := by rw [← hvbx_c]; exact hvbx
  have hvbd_lt_c : bAdicVal b d < c := by omega
  have hvbyd : bAdicVal b (y + d) = bAdicVal b d :=
    bAdicVal_add_of_lt b y d hb hy hd_pos hvbd_lt_c
  have hvbz_d : bAdicVal b z = bAdicVal b d := by
    rw [hzeq]; exact hvbyd
  have hvbz_c : bAdicVal b z = c := hyz.symm
  omega

/--
  **Lemma — `bAdicVal_isValidColoring`.**

  For $b \ge 2$ and any $k$: the valuation coloring is a valid
  $k$-coloring of $\{1, \ldots, b^k - 1\}$ (its values are all
  $< k$ on that domain).

  Proof: `bAdicVal_lt_pow`.
-/
theorem bAdicVal_isValidColoring {b k : ℕ} (hb : 2 ≤ b) :
    IsValidColoring (b ^ k - 1) k (bAdicVal b) := by
  intro m hm_lb hm_ub
  have hpow_pos : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
  exact bAdicVal_lt_pow b k m hb hm_lb (by omega)

/--
  **Theorem (b-adic unique factorization).**

  Converse to Round 48 (`bAdicVal_b_pow_mul_unit`). For $b \ge 2$,
  every positive $n$ with $v_b(n) = c$ factors as $n = b^c \cdot u$
  for some b-unit $u > 0$ (i.e., $v_b(u) = 0$).

  Proof: induction on $c$.
  * $c = 0$: take $u = n$ directly.
  * $c + 1$: $v_b(n) \ge 1$ implies $b \mid n$, so $n = b m$. Then
    $v_b(m) = c$ by `bAdicVal_b_mul`, IH gives $m = b^c u$ with $u$
    a b-unit, hence $n = b m = b^{c+1} u$.

  **Significance**: the structural converse to Round 48. Together
  they give the FULL color stratification of the valuation
  coloring: color $c$ is EXACTLY $\{b^c \cdot u : v_b(u) = 0\}$.
-/
theorem bAdicVal_unit_factorization {b : ℕ} (hb : 2 ≤ b) :
    ∀ c n, 0 < n → bAdicVal b n = c →
      ∃ u, 0 < u ∧ bAdicVal b u = 0 ∧ n = b ^ c * u := by
  intro c
  induction c with
  | zero =>
    intro n hn_pos hv
    refine ⟨n, hn_pos, hv, ?_⟩
    rw [pow_zero, one_mul]
  | succ c ih =>
    intro n hn_pos hv
    -- v_b(n) = c + 1 implies b | n.
    have hn_div : b ∣ n := by
      by_contra hndvd
      have h_v_zero : bAdicVal b n = 0 := by
        conv_lhs => rw [bAdicVal]
        rw [dif_neg]
        intro ⟨_, _, hmod⟩
        exact hndvd (Nat.dvd_of_mod_eq_zero hmod)
      omega
    obtain ⟨m, hm_eq⟩ := hn_div
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp at hm_eq; omega
      · exact hm
    have hvm : bAdicVal b m = c := by
      have h_bm : bAdicVal b (b * m) = 1 + bAdicVal b m :=
        bAdicVal_b_mul b m hb hm_pos
      rw [hm_eq, h_bm] at hv
      omega
    obtain ⟨u, hu_pos, hu_val, hu_eq⟩ := ih m hm_pos hvm
    refine ⟨u, hu_pos, hu_val, ?_⟩
    rw [hm_eq, hu_eq, pow_succ]
    ring

/--
  **Theorem (iff characterization of valuation
  stratification).**

  For $b \ge 2$ and any $n > 0$, $c \ge 0$:
  $v_b(n) = c \iff \exists u > 0$ b-unit with $n = b^c \cdot u$.

  Forward direction: Round 52 (`bAdicVal_unit_factorization`).
  Reverse direction: Round 48 (`bAdicVal_b_pow_mul_unit`).

  **Significance**: the FULL characterization of the valuation
  coloring's color stratification. Color $c$ in the valuation
  coloring is precisely the set $\{b^c \cdot u : u > 0,
  v_b(u) = 0\}$ — a bijection between color classes and
  (level $\times$ b-units).
-/
theorem bAdicVal_eq_iff_factorization {b : ℕ} (hb : 2 ≤ b) {n : ℕ}
    (hn_pos : 0 < n) (c : ℕ) :
    bAdicVal b n = c ↔
    ∃ u, 0 < u ∧ bAdicVal b u = 0 ∧ n = b ^ c * u := by
  constructor
  · intro hv
    exact bAdicVal_unit_factorization hb c n hn_pos hv
  · intro ⟨u, hu_pos, hu_val, hn_eq⟩
    rw [hn_eq]
    exact bAdicVal_b_pow_mul_unit hb hu_pos hu_val c

/-! ### Derived theorem. -/

/--
  **Theorem `thm:lower` (CDW Lemma 4.1; paper restatement).**

  For all `b ≥ 2` and `k ≥ 1`, the Rado number `R_k(b)` for the
  equation `x + b·y = b·z` is at least `b^k`.

  Round 51 refactor: derived as a one-liner from
  `bAdicVal_isValidColoring` and `bAdicVal_avoidsMono`.
-/
theorem thm_lower (b k : ℕ) (hb : 2 ≤ b) (_hk : 1 ≤ k) :
    RadoNumberAtLeast b k (b ^ k) :=
  ⟨bAdicVal b, bAdicVal_isValidColoring hb, bAdicVal_avoidsMono hb _⟩

/--
  **Theorem (DPP body is realizable).**

  For $b \ge 3$, $k \ge 2$: there exists a valid mono-free
  $k$-coloring of $\{1, \ldots, b^k - 1\}$ whose every color class
  contains a distance-$b^{k-1}$ pair. Witnessed by the
  b-adic valuation coloring `bAdicVal b`.

  Composes `bAdicVal_isValidColoring`,
  `bAdicVal_avoidsMono`, and
  `bAdicVal_distance_pair_witness`.

  **Significance**: the existential form of "the DPL hypothesis
  is realizable." Confirms `DistancePairProperty b k`'s body is
  consistent with the existence of a valid mono-free coloring —
  the SAT-verified content is the UNIVERSAL quantifier over $\chi$,
  not the body's satisfiability.
-/
theorem dpp_body_realized (b k : ℕ) (hb : 3 ≤ b) (hk : 2 ≤ k) :
    ∃ χ : ℕ → ℕ,
      IsValidColoring (b ^ k - 1) k χ ∧
      AvoidsMonoSolution b (b ^ k - 1) χ ∧
      (∀ c, c < k → ∃ j, 1 ≤ j ∧ j + b ^ (k - 1) ≤ b ^ k - 1 ∧
                          χ j = c ∧ χ (j + b ^ (k - 1)) = c) :=
  ⟨bAdicVal b,
   bAdicVal_isValidColoring (by omega),
   bAdicVal_avoidsMono (by omega) _,
   bAdicVal_distance_pair_witness b k hb hk⟩

end RadoNumbers
