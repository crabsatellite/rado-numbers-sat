/-
  RadoNumbers/General/RadoLift.lean

  **The Rado Lift Lemma** (backward-direction mechanism, A6).

  If `g` is a `k`-color mono-free coloring on `{1, …, M}` for the
  equation `x + b·y = b·z`, then the lifted coloring

      χ(n) = if b ∣ n then g(n / b) else k   (fresh color)

  is a `(k+1)`-color mono-free coloring on `{1, …, b·M}`.

  Proof core.  From `x + b·y = b·z` one gets `x = b·(z − y)`, so
  `b ∣ x`; hence `χ(x)` is always an *old* color (`< k`).  A
  monochromatic triple therefore cannot have `y` or `z` painted the
  fresh color `k`, so `b ∣ y` and `b ∣ z` too.  Dividing the equation
  by `b` yields `x' + b·y' = b·z'` with `x' = x/b`, etc. — a
  monochromatic triple for `g` on `{1, …, M}`, contradicting mono-
  freeness of `g`.

  This is the FIRST GENERALIZABLE backward mechanism of the project:
  it multiplies both the range (`M → b·M`) and the color budget
  (`k → k+1`) at once, and is fully general in `b`.

  All theorems in this file are KERNEL-PURE
  (`[propext, Classical.choice, Quot.sound]`).  They do NOT depend on
  any SAT atom.  The b=3 corollary `exists_monoFreeColoring_b3_k6_729`
  is the ONLY declaration here that inherits the base-case atom
  `r5_witness_valid_sat` (via `thm_r5_243`); the lift machinery itself
  is atom-free.

  Stated in the project's `Basic.lean` convention
  (`IsValidColoring` / `AvoidsMonoSolution` / `IsRadoTriple` /
  `RadoNumberAtLeast`), to compose directly with `thm_r5_243`.
-/

import RadoNumbers.Basic
import RadoNumbers.Breakdown
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Phase A — the lifted coloring. -/

/--
  **The Rado lift of a coloring `g`.**

  `radoLiftColoring b k g n` paints `n` with the old color `g(n / b)`
  when `b ∣ n`, and with the fresh color `k` otherwise.
-/
def radoLiftColoring (b k : ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun n => if b ∣ n then g (n / b) else k

@[simp]
theorem radoLiftColoring_dvd (b k : ℕ) (g : ℕ → ℕ) {n : ℕ} (h : b ∣ n) :
    radoLiftColoring b k g n = g (n / b) := by
  unfold radoLiftColoring; simp [h]

@[simp]
theorem radoLiftColoring_not_dvd (b k : ℕ) (g : ℕ → ℕ) {n : ℕ} (h : ¬ b ∣ n) :
    radoLiftColoring b k g n = k := by
  unfold radoLiftColoring; simp [h]

/-! ### Local Nat helpers (kept explicit; no `omega`-only divisibility). -/

/--
  **Domain helper.**  A multiple of `b` in `[1, b·M]` divides down into
  `[1, M]` (for `1 ≤ b`).
-/
theorem lift_domain {b M n : ℕ} (hb : 1 ≤ b)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ b * M) (hdvd : b ∣ n) :
    1 ≤ n / b ∧ n / b ≤ M := by
  refine ⟨?_, ?_⟩
  · -- n / b ≥ 1 since b ∣ n and n ≥ 1 (so b ≤ n).
    have hble : b ≤ n := Nat.le_of_dvd (by omega) hdvd
    exact Nat.one_le_div_iff (by omega) |>.mpr hble
  · -- n / b ≤ M from n ≤ b * M  (Nat.div_le_of_le_mul : m ≤ k*n → m/k ≤ n).
    exact Nat.div_le_of_le_mul hn_ub

/--
  **Divisibility of `x`.**  From a Rado triple `x + b·y = b·z` we get
  `b ∣ x`, because `x = b·z − b·y` and both terms are multiples of `b`.
-/
theorem lift_dvd_x {b x y z : ℕ} (heq : x + b * y = b * z) : b ∣ x := by
  have hx_eq : x = b * z - b * y := by omega
  rw [hx_eq]
  exact Nat.dvd_sub (Dvd.intro z rfl) (Dvd.intro y rfl)

/--
  **Cancellation after dividing the equation by `b`.**

  If `x = b·x'`, `y = b·y'`, `z = b·z'` and `x + b·y = b·z` with
  `1 ≤ b`, then `x' + b·y' = b·z'`.
-/
theorem lift_div_cancel {b x' y' z' : ℕ} (hb : 1 ≤ b)
    (heq : b * x' + b * (b * y') = b * (b * z')) :
    x' + b * y' = b * z' := by
  have hb0 : 0 < b := hb
  have hexpand : b * (x' + b * y') = b * (b * z') := by ring_nf; ring_nf at heq; linarith
  exact Nat.eq_of_mul_eq_mul_left hb0 hexpand

/-! ### Phase B — validity of the lift. -/

/--
  **The lift of a valid `k`-coloring of `{1, …, M}` is a valid
  `(k+1)`-coloring of `{1, …, b·M}`.**

  Multiples of `b` inherit an old color `< k < k+1`; non-multiples get
  the fresh color `k < k+1`.
-/
theorem radoLiftColoring_valid
    (b k M : ℕ) (g : ℕ → ℕ)
    (hb : 1 ≤ b)
    (hg_valid : IsValidColoring M k g) :
    IsValidColoring (b * M) (k + 1) (radoLiftColoring b k g) := by
  intro n hn_lb hn_ub
  by_cases hdvd : b ∣ n
  · -- old color g(n/b) < k < k+1
    rw [radoLiftColoring_dvd b k g hdvd]
    obtain ⟨hdiv_lb, hdiv_ub⟩ := lift_domain hb hn_lb hn_ub hdvd
    have := hg_valid (n / b) hdiv_lb hdiv_ub
    omega
  · -- fresh color k < k+1
    rw [radoLiftColoring_not_dvd b k g hdvd]
    omega

/-! ### Phase C — mono-free preservation (KEY THEOREM). -/

/--
  **The lift of a mono-free coloring is mono-free.**

  Key backward-direction theorem.  If `g` avoids monochromatic
  solutions to `x + b·y = b·z` on `{1, …, M}`, then its lift avoids
  them on `{1, …, b·M}`.

  Proof.  Suppose a monochromatic triple `(x, y, z)` exists in
  `[1, b·M]`.  Then `b ∣ x` (Rado equation ⇒ `x = b·(z−y)`), so
  `χ(x) = g(x/b) < k`, i.e. `χ(x) ≠ k`.  Since `χ(y) = χ(x) ≠ k`, the
  point `y` is not painted fresh, so `b ∣ y`; likewise `b ∣ z`.
  Writing `x = b·x'`, `y = b·y'`, `z = b·z'` and cancelling `b` gives
  `x' + b·y' = b·z'`, a monochromatic triple for `g` in `[1, M]` —
  contradicting `hg_free`.
-/
theorem radoLiftColoring_avoids
    (b k M : ℕ) (g : ℕ → ℕ)
    (hb : 1 ≤ b)
    (hg_valid : IsValidColoring M k g)
    (hg_free : AvoidsMonoSolution b M g) :
    AvoidsMonoSolution b (b * M) (radoLiftColoring b k g) := by
  -- Unfold to a contradiction from an assumed mono triple.
  rintro ⟨x, y, z, hxn, hyn, hzn, ⟨hxpos, hypos, hzpos, heq⟩, hxy, hyz⟩
  -- Step 1: b ∣ x  (from the Rado equation).
  have hdvd_x : b ∣ x := lift_dvd_x heq
  -- Step 2: x divides into [1, M]; χ x = g(x/b) < k, so χ x ≠ k.
  obtain ⟨hx'_lb, hx'_ub⟩ := lift_domain hb hxpos hxn hdvd_x
  have hχx_old : radoLiftColoring b k g x = g (x / b) :=
    radoLiftColoring_dvd b k g hdvd_x
  have hχx_lt : radoLiftColoring b k g x < k := by
    rw [hχx_old]; exact hg_valid (x / b) hx'_lb hx'_ub
  -- Step 3: y is not fresh, so b ∣ y  (else χ y = k ≥ k > χ x = χ y).
  have hdvd_y : b ∣ y := by
    by_contra hndvd
    have hyk : radoLiftColoring b k g y = k := radoLiftColoring_not_dvd b k g hndvd
    -- χ x = χ y = k  ⇒  k < k, contradiction.
    have : radoLiftColoring b k g x = k := hxy.trans hyk
    omega
  -- Step 4: z is not fresh either, so b ∣ z.
  have hdvd_z : b ∣ z := by
    by_contra hndvd
    have hzk : radoLiftColoring b k g z = k := radoLiftColoring_not_dvd b k g hndvd
    -- χ x = χ y = χ z = k  ⇒  k < k, contradiction.
    have : radoLiftColoring b k g x = k := (hxy.trans hyz).trans hzk
    omega
  -- Step 5: divided coordinates land in [1, M].
  obtain ⟨hy'_lb, hy'_ub⟩ := lift_domain hb hypos hyn hdvd_y
  obtain ⟨hz'_lb, hz'_ub⟩ := lift_domain hb hzpos hzn hdvd_z
  -- Step 6: recover x = b·x', y = b·y', z = b·z'.
  obtain ⟨x', hx_eq⟩ := hdvd_x
  obtain ⟨y', hy_eq⟩ := hdvd_y
  obtain ⟨z', hz_eq⟩ := hdvd_z
  have hxd : x / b = x' := by rw [hx_eq, Nat.mul_div_cancel_left _ (by omega : 0 < b)]
  have hyd : y / b = y' := by rw [hy_eq, Nat.mul_div_cancel_left _ (by omega : 0 < b)]
  have hzd : z / b = z' := by rw [hz_eq, Nat.mul_div_cancel_left _ (by omega : 0 < b)]
  -- Step 7: divide the Rado equation by b: x' + b·y' = b·z'.
  have heq' : x' + b * y' = b * z' := by
    apply lift_div_cancel hb
    rw [← hx_eq, ← hy_eq, ← hz_eq]; exact heq
  -- Step 8: the divided triple is monochromatic for g.
  -- (Reconstruct divisibility from the witnessing equations, since the
  --  original `hdvd_*` were consumed by the `obtain`s above.)
  have h1 : radoLiftColoring b k g x = g x' := by rw [hχx_old, hxd]
  have h2 : radoLiftColoring b k g y = g y' := by
    rw [radoLiftColoring_dvd b k g (⟨y', hy_eq⟩ : b ∣ y), hyd]
  have h3 : radoLiftColoring b k g z = g z' := by
    rw [radoLiftColoring_dvd b k g (⟨z', hz_eq⟩ : b ∣ z), hzd]
  have hgxy : g x' = g y' := by rw [← h1, ← h2]; exact hxy
  have hgyz : g y' = g z' := by rw [← h2, ← h3]; exact hyz
  -- Step 9: rewrite the [1, M] domain bounds in terms of x', y', z'.
  rw [hxd] at hx'_lb hx'_ub
  rw [hyd] at hy'_lb hy'_ub
  rw [hzd] at hz'_lb hz'_ub
  -- Step 10: feed g's mono triple into hg_free — contradiction.
  exact hg_free ⟨x', y', z', hx'_ub, hy'_ub, hz'_ub,
    ⟨hx'_lb, hy'_lb, hz'_lb, heq'⟩, hgxy, hgyz⟩

/-! ### Phase D — existential lift corollary. -/

/--
  **Existential form of the Rado lift.**

  If `{1, …, M}` admits a mono-free valid `k`-coloring for
  `x + b·y = b·z`, then `{1, …, b·M}` admits a mono-free valid
  `(k+1)`-coloring.  Combines `radoLiftColoring_valid` and
  `radoLiftColoring_avoids`.
-/
theorem rado_lift_exists
    (b k M : ℕ) (hb : 1 ≤ b)
    (h : ∃ g, IsValidColoring M k g ∧ AvoidsMonoSolution b M g) :
    ∃ χ, IsValidColoring (b * M) (k + 1) χ ∧
        AvoidsMonoSolution b (b * M) χ := by
  obtain ⟨g, hg_valid, hg_free⟩ := h
  exact ⟨radoLiftColoring b k g,
    radoLiftColoring_valid b k M g hb hg_valid,
    radoLiftColoring_avoids b k M g hb hg_valid hg_free⟩

/--
  **Rado-number lower-bound transfer (lift form).**

  In the project's convention `RadoNumberAtLeast b k N` means
  `R_k(b) ≥ N`, i.e. there is a mono-free valid `k`-coloring of
  `{1, …, N − 1}`.  The lift sends a witness on `{1, …, M}`
  (`RadoNumberAtLeast b k (M+1)`) to a witness on `{1, …, b·M}`
  (`RadoNumberAtLeast b (k+1) (b·M + 1)`), i.e.

      R_k(b) > M   ⟹   R_{k+1}(b) > b·M.
-/
theorem rado_lower_bound_lift
    (b k M : ℕ) (hb : 1 ≤ b)
    (h : RadoNumberAtLeast b k (M + 1)) :
    RadoNumberAtLeast b (k + 1) (b * M + 1) := by
  -- RadoNumberAtLeast b k (M+1) unfolds with (M+1)-1 = M.
  obtain ⟨g, hg_valid, hg_free⟩ := h
  simp only [Nat.add_sub_cancel] at hg_valid hg_free
  refine ⟨radoLiftColoring b k g, ?_, ?_⟩
  · simpa [Nat.add_sub_cancel] using
      radoLiftColoring_valid b k M g hb hg_valid
  · simpa [Nat.add_sub_cancel] using
      radoLiftColoring_avoids b k M g hb hg_valid hg_free

/-! ### Phase E — b = 3 tower corollary (depends on base SAT atom). -/

/--
  **`R_6(3) > 729 = 3^6`** (existential mono-free coloring form).

  Obtained by lifting the SAT-verified base witness for `R_5(3) > 243`
  (`thm_r5_243`) with `b = 3`, `k = 5`, `M = 243`: indeed
  `3 · 243 = 729` and `5 + 1 = 6`.

  AXIOM DEPENDENCY (honest): the LIFT machinery is kernel-pure, but
  this corollary inherits the base-case atom `r5_witness_valid_sat`
  through `thm_r5_243`.  Discharging that atom is R446's job; the lift
  itself adds no new axiom.
-/
theorem exists_monoFreeColoring_b3_k6_729 :
    ∃ χ, IsValidColoring 729 6 χ ∧ AvoidsMonoSolution 3 729 χ := by
  -- thm_r5_243 : RadoNumberAtLeast 3 5 244  =  ∃ χ, valid 243 5 ∧ avoids 3 243.
  have hbase : ∃ g, IsValidColoring 243 5 g ∧ AvoidsMonoSolution 3 243 g := by
    obtain ⟨g, hv, ha⟩ := thm_r5_243
    exact ⟨g, hv, ha⟩
  -- Lift with b = 3, k = 5, M = 243.
  have hlift := rado_lift_exists 3 5 243 (by norm_num) hbase
  -- 3 * 243 = 729 and 5 + 1 = 6.
  norm_num at hlift
  exact hlift

/-! ### Phase F — the FULL b = 3 backward tower (R446).

  Iterating the lift `R_k(3) > 3^k ⟹ R_{k+1}(3) > 3·3^k = 3^{k+1}`
  from the base `R_5(3) > 243 = 3^5` (`thm_r5_243`) gives the entire
  backward direction of the threshold conjecture for `b = 3`:

      ∀ k ≥ 5,   R_k(3) > 3^k.

  This is ONE kernel-pure induction.  The lift machinery
  (`rado_lower_bound_lift`) is atom-free, so the tower inherits
  EXACTLY the single base-case atom `r5_witness_valid_sat` (via
  `thm_r5_243`) — the induction adds NO new axiom.
-/

/--
  **Power-step helper.**  `3 · 3^k = 3^(k+1)` in `ℕ`.

  The lift produces the bound `3 · 3^k`; `pow_succ` gives
  `3^(k+1) = 3^k · 3`, so we commute the product.  Kept as a small
  local lemma so the tower step is a clean rewrite.
-/
theorem three_mul_pow (k : ℕ) : 3 * 3 ^ k = 3 ^ (k + 1) := by
  rw [pow_succ]; ring

/--
  **General power-step helper** (R448).  `b · b^k = b^(k+1)` in `ℕ`.

  The general lift produces the bound `b · b^k`; `pow_succ` gives
  `b^(k+1) = b^k · b`, so we commute the product.  This is the
  arbitrary-`b` generalization of `three_mul_pow`; the b=3 backward
  tower used `three_mul_pow`, the general tower uses this.
-/
theorem mul_pow_succ_base (b k : ℕ) : b * b ^ k = b ^ (k + 1) := by
  rw [pow_succ]; ring

/--
  **The full b = 3 backward tower.**  `R_k(3) > 3^k` for every
  `k ≥ 5`, in the project's `RadoNumberAtLeast` convention
  (`RadoNumberAtLeast 3 k (3^k + 1)` means `R_k(3) ≥ 3^k + 1`, i.e.
  `R_k(3) > 3^k`).

  Proof by `Nat.le_induction` from `k = 5`:

  * **Base** `k = 5`: `thm_r5_243 : RadoNumberAtLeast 3 5 244`, and
    `3^5 + 1 = 244`.
  * **Step** `k → k+1` (`5 ≤ k`): apply `rado_lower_bound_lift`
    with `b = 3`, `M = 3^k` to the inductive hypothesis
    `RadoNumberAtLeast 3 k (3^k + 1)`, obtaining
    `RadoNumberAtLeast 3 (k+1) (3·3^k + 1)`; then rewrite
    `3·3^k = 3^(k+1)` (`three_mul_pow`).

  AXIOM DEPENDENCY (honest): inherits ONLY `r5_witness_valid_sat`
  via the base case; the lift/induction add no new axiom.
-/
theorem rado_b3_backward_tower (k : ℕ) (hk : 5 ≤ k) :
    RadoNumberAtLeast 3 k (3 ^ k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- 3^5 + 1 = 244, so the goal is exactly `thm_r5_243`.
    have h244 : (3 : ℕ) ^ 5 + 1 = 244 := by norm_num
    rw [h244]
    exact thm_r5_243
  | succ k hk ih =>
    -- Lift the inductive witness: R_k(3) > 3^k ⟹ R_{k+1}(3) > 3·3^k.
    have hstep : RadoNumberAtLeast 3 (k + 1) (3 * 3 ^ k + 1) :=
      rado_lower_bound_lift 3 k (3 ^ k) (by norm_num) ih
    -- Rewrite 3·3^k = 3^(k+1).
    rwa [three_mul_pow k] at hstep

/--
  **`R_6(3) > 729 = 3^6` via the tower interface.**  Specialization
  of `rado_b3_backward_tower` at `k = 6` (`3^6 = 729`), confirming the
  former one-off corollary `exists_monoFreeColoring_b3_k6_729` is now
  a single instance of the general tower.
-/
theorem rado_b3_k6_via_tower : RadoNumberAtLeast 3 6 (729 + 1) := by
  have h := rado_b3_backward_tower 6 (by norm_num)
  have h729 : (3 : ℕ) ^ 6 = 729 := by norm_num
  rwa [h729] at h

/-! ### Phase G — threshold-backward wrapper (R446).

  INTERFACE NOTE.  The project carries no `RadoNumber : ℕ → ℕ → ℕ`
  *function*; the Rado number is encoded only via the predicates
  `RadoNumberAtLeast` / `RadoNumberAtMost` / `IsRadoNumber`
  (`Basic.lean`).  The breakdown side of the threshold conjecture
  (`RadoThresholdConjecture`, `ThresholdDichotomy`) is therefore the
  *failure* of `R_k(3) = 3^k`, whose lower-bound half is exactly
  `RadoNumberAtLeast 3 k (3^k + 1)`.  Hence the canonical
  "`R_k(3) > 3^k`" statement in this convention is the tower itself;
  the wrapper below just rephrases it under the threshold hypothesis
  `4 < k` (equivalently `2·(3−1) < k`, the breakdown regime for
  `b = 3`).
-/

/--
  **Threshold-backward direction for `b = 3`.**  For every `k` strictly
  past the boundary `2(b−1) = 4`, the Rado number exceeds `3^k`:

      4 < k   ⟹   R_k(3) > 3^k          (i.e. `RadoNumberAtLeast 3 k (3^k + 1)`).

  Since over `ℕ` we have `4 < k ↔ 5 ≤ k`, this is `rado_b3_backward_tower`
  stated in the breakdown-regime form.  This is the lower-bound (witness)
  half of the breakdown side `¬ IsRadoNumber 3 k (3^k)` of
  `RadoThresholdConjecture` for `b = 3`.
-/
theorem threshold_backward_b3 (k : ℕ) (hk : 4 < k) :
    RadoNumberAtLeast 3 k (3 ^ k + 1) :=
  rado_b3_backward_tower k hk

/-! ### Phase H — the GENERAL backward tower (R448).

  The R446 b=3 tower is one specialization of a single arbitrary-`b`
  structural theorem.  The lift `R_k(b) > M ⟹ R_{k+1}(b) > b·M`
  (`rado_lower_bound_lift`, R445) is FULLY GENERAL in `b`, so iterating
  it from the *first-breakdown* base case `R_{2b-1}(b) > b^{2b-1}`
  (taken as a HYPOTHESIS, not discharged here) produces

      ∀ k ≥ 2b-1,   R_k(b) > b^k                 (`b ≥ 2`).

  This is the COMPLETE structural reduction of the threshold
  conjecture's backward direction: for every `b`, the entire
  `k > 2(b-1)` region collapses onto the single base case.

  KERNEL PURITY.  Because the base case enters as the hypothesis
  `hbase`, the general theorem carries NO SAT atom: it is kernel-pure
  `[propext, Classical.choice, Quot.sound]`.  The lift machinery and
  the `Nat.le_induction` add nothing.  (The b=3 *instantiation* below
  re-supplies `thm_r5_243` for `hbase`, and only THEN inherits
  `r5_witness_valid_sat`.)
-/

/--
  **The general backward tower** (R448, PRIMARY).  For every base
  `b ≥ 2`, given the first-breakdown witness
  `R_{2b-1}(b) > b^{2b-1}` (`hbase`), the bound `R_k(b) > b^k` holds
  for every `k ≥ 2b-1`.

  Proof by `Nat.le_induction` from `n₀ = 2b-1`:

  * **Base** `k = 2b-1`: `exact hbase`.
  * **Step** `k → k+1` (`2b-1 ≤ k`): apply `rado_lower_bound_lift`
    with `M = b^k` to the inductive witness `R_k(b) > b^k`, obtaining
    `R_{k+1}(b) > b·b^k`; rewrite `b·b^k = b^(k+1)`
    (`mul_pow_succ_base`).  The lift's `1 ≤ b` hypothesis is derived
    from `hb : 2 ≤ b` by `omega`.

  KERNEL-PURE: the base case is a hypothesis, so no SAT atom is
  inherited — `[propext, Classical.choice, Quot.sound]`.
-/
theorem rado_backward_tower_general
    (b k : ℕ) (hb : 2 ≤ b)
    (hbase : RadoNumberAtLeast b (2 * b - 1) (b ^ (2 * b - 1) + 1))
    (hk : 2 * b - 1 ≤ k) :
    RadoNumberAtLeast b k (b ^ k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- k = 2b-1: the goal is exactly `hbase`.
    exact hbase
  | succ k _ ih =>
    -- Lift the inductive witness: R_k(b) > b^k ⟹ R_{k+1}(b) > b·b^k.
    have hstep : RadoNumberAtLeast b (k + 1) (b * b ^ k + 1) :=
      rado_lower_bound_lift b k (b ^ k) (by omega) ih
    -- Rewrite b·b^k = b^(k+1).
    rwa [mul_pow_succ_base b k] at hstep

/--
  **Threshold-backward wrapper (general)** (R448, Phase C).  Restates
  the general tower in the threshold-regime form: for `b ≥ 2`, every
  `k` strictly past the boundary `2(b-1)` satisfies `R_k(b) > b^k`,
  given the first-breakdown base case `hbase`.

  Over `ℕ` (with `b ≥ 1`) we have `2(b-1) = 2b-2`, so
  `2(b-1) < k ↔ 2b-1 ≤ k`; `omega` discharges the index arithmetic
  (Nat subtraction handled via the `hb` bound).  We isolate the index
  fact `2b-1 ≤ k` into a pure `have` first, so `omega` only sees
  linear facts and never the `b^k` / `^` terms it cannot reason about.

  KERNEL-PURE: inherits no SAT atom (base case is a hypothesis).
-/
theorem threshold_backward_from_first_breakdown
    (b k : ℕ) (hb : 2 ≤ b)
    (hbase : RadoNumberAtLeast b (2 * b - 1) (b ^ (2 * b - 1) + 1))
    (hk : 2 * (b - 1) < k) :
    RadoNumberAtLeast b k (b ^ k + 1) := by
  -- Isolate the index arithmetic so omega never meets `b^k`.
  have hk' : 2 * b - 1 ≤ k := by omega
  exact rado_backward_tower_general b k hb hbase hk'

/--
  **b=3 instantiation of the general tower** (R448, Phase D).  Confirms
  the general theorem composes: re-deriving `R_k(3) > 3^k` for `k ≥ 5`
  by supplying the SAT base `thm_r5_243` for the general `hbase`.

  Here `2·3 - 1 = 5` and `3^(2·3-1) + 1 = 3^5 + 1 = 244`, so the
  general first-breakdown hypothesis is exactly `thm_r5_243`
  (after a `norm_num` numeral reduction of the index/power).

  This does NOT replace the direct R446 `rado_b3_backward_tower`; it
  is a confirmation that the general structural theorem specializes.

  AXIOM DEPENDENCY: inherits ONLY `r5_witness_valid_sat` (via the base
  case `thm_r5_243`), exactly like the direct b=3 tower.
-/
theorem rado_b3_backward_tower_from_general (k : ℕ) (hk : 5 ≤ k) :
    RadoNumberAtLeast 3 k (3 ^ k + 1) := by
  -- Supply the SAT base for the general first-breakdown hypothesis.
  have hbase : RadoNumberAtLeast 3 (2 * 3 - 1) (3 ^ (2 * 3 - 1) + 1) := by
    show RadoNumberAtLeast 3 5 244
    exact thm_r5_243
  -- 2·3 - 1 = 5 ≤ k, so the general tower applies.
  exact rado_backward_tower_general 3 k (by norm_num) hbase (by omega)

end RadoNumbers
