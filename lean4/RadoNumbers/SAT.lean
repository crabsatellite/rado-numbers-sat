/-
  RadoNumbers/SAT.lean

  Lemma `lem:keypair` (Distance Pair Lemma; SAT-verified) and
  Theorem `thm:sat` (independent verification of $R_3(b) = b^3$ for
  $b \in \{3, \ldots, 10\}$ and $R_4(b) = b^4$ for $b \in \{3, 4, 5\}$).
  Companion to Li 2026 "On Rado Numbers for $x + by = bz$".

  The Distance Pair Lemma is the paper's identified structural
  mechanism for the $b^k$ pattern when $k \le 4$.  Each color class
  must contain a pair at distance $b^{k-1}$; combined with the
  element $b^k$ (which is $b \cdot b^{k-1}$, so $\chi(b^k) = c$
  forbids distance $b^{k-1}$ in color $c$), this produces a Rado
  triple $(b^k, j, j + b^{k-1})$.

  Encoding:

  * `lem_keypair_sat` — Cat 2 SAT-verified atom (paper's named
    Distance Pair Lemma; SAT-verified for the cases in Table
    `table:sat`).
  * `thm_sat` — derived theorem yielding $R_k(b) = b^k$ for the
    $(b, k)$ pairs covered by `lem_keypair_sat`.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import RadoNumbers.DPLStructure
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Cat 2 atomic — Distance Pair Lemma (SAT-verified). -/

/--
  **Lemma `lem:keypair` (Distance Pair Lemma; Cat 2 SAT-verified
  atom).**

  For the $(b, k)$ pairs SAT-verified in Li 2026 Table
  `table:sat` — namely

  * $k = 3$, $b \in \{3, 4, 5, 6, 7, 8, 9, 10\}$;
  * $k = 4$, $b \in \{3, 4, 5\}$ —

  in any valid $k$-coloring $\chi$ of $\{1, \ldots, b^k - 1\}$
  avoiding monochromatic solutions to $x + b·y = b·z$, every color
  class $C_c = \chi^{-1}(c)$ contains a pair $(j, j + b^{k-1})$ for
  some $j \in \{1, \ldots, b^{k-1}\}$.

  The hypothesis `hbk` encodes EXACTLY the SAT-verified set: this
  axiom asserts nothing about unverified pairs (e.g. $b = 11$,
  $k = 3$; $b = 6$, $k = 4$; any $k = 2$ — the $k = 2$ case is
  instead a kernel-pure theorem `lem_keypair_at_k2`).

  *Justification:* SAT verification (Li 2026, Lemma `lem:keypair`
  and Table `table:sat`).  Separate SAT check for each color
  $c \in \{0, \ldots, k-1\}$, all UNSAT under CaDiCaL 1.5.3.
  The largest instance ($b = 5, k = 4, n = 624$) involves
  $2496$ variables; the smallest verified ($b = 3, k = 3, n = 26$)
  has $78$.

  *Status:* `gapOpen` Cat 2 SAT-verified.
-/
axiom lem_keypair_sat (b k : ℕ)
    (hbk : (k = 3 ∧ 3 ≤ b ∧ b ≤ 10) ∨ (k = 4 ∧ 3 ≤ b ∧ b ≤ 5))
    (χ : ℕ → ℕ)
    (hValid : IsValidColoring (b ^ k - 1) k χ)
    (hAvoid : AvoidsMonoSolution b (b ^ k - 1) χ) :
    ∀ c, c < k →
      ∃ j, 1 ≤ j ∧ j ≤ b ^ (k - 1) ∧
           χ j = c ∧ χ (j + b ^ (k - 1)) = c

/-! ### Derived theorem `thm:sat`. -/

/--
  **Theorem `thm:sat` (independent verification; cf.
  CDW Table 10).**

  For the $(b, k)$ pairs SAT-verified by the Distance Pair Lemma
  `lem_keypair_sat` (paper Table `table:sat`) — namely

  * $k = 3$, $b \in \{3, 4, 5, 6, 7, 8, 9, 10\}$;
  * $k = 4$, $b \in \{3, 4, 5\}$ —

  $R_k(b) = b^k$.  The hypothesis `hbk` encodes exactly this set.

  Lower bound: `thm_lower`.  Upper bound: every valid $k$-coloring
  $\chi$ of $\{1, \ldots, b^k\}$ either (a) already produces a
  monochromatic solution on $\{1, \ldots, b^k - 1\}$, or (b)
  avoids one there; in case (b), `lem_keypair_sat` applied to
  color $\chi(b^k)$ yields $j \in \{1, \ldots, b^{k-1}\}$ with
  $\chi(j) = \chi(j + b^{k-1}) = \chi(b^k)$, and the triple
  $(b^k, j, j + b^{k-1})$ satisfies $b^k + b \cdot j = b \cdot
  (j + b^{k-1})$.
-/
theorem thm_sat (b k : ℕ)
    (hbk : (k = 3 ∧ 3 ≤ b ∧ b ≤ 10) ∨ (k = 4 ∧ 3 ≤ b ∧ b ≤ 5)) :
    IsRadoNumber b k (b ^ k) := by
  -- Recover the numeric bounds 3 ≤ b, 2 ≤ k ≤ 4 from the verified set.
  have hb : 3 ≤ b := by rcases hbk with ⟨_, hb, _⟩ | ⟨_, hb, _⟩ <;> exact hb
  have hk2 : 2 ≤ k := by rcases hbk with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  have hk4 : k ≤ 4 := by rcases hbk with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  refine ⟨?_, ?_⟩
  · exact thm_lower b k (by linarith) (by linarith)
  · intro χ hValid
    have hb_pos : 0 < b := by linarith
    have hk_pos : 0 < k := by linarith
    have hb_pow_pos : 0 < b ^ k := Nat.pow_pos hb_pos
    -- The restriction to {1, …, b^k - 1} is also a valid k-coloring.
    have hValid' : IsValidColoring (b ^ k - 1) k χ := fun m hm_lb hm_ub =>
      hValid m hm_lb (by omega)
    by_cases hAvoid : AvoidsMonoSolution b (b ^ k - 1) χ
    · -- Apply Distance Pair Lemma at color c* := χ(b^k).
      have hChi_bk_lt : χ (b ^ k) < k := hValid (b ^ k) hb_pow_pos (le_refl _)
      obtain ⟨j, hj_lb, hj_ub, hχj, hχj'⟩ :=
        lem_keypair_sat b k hbk χ hValid' hAvoid (χ (b ^ k)) hChi_bk_lt
      -- d := b^(k-1); key identity: d * b = b^k.
      have hd_pos : 0 < b ^ (k - 1) := Nat.pow_pos hb_pos
      have hd_lt : b ^ (k - 1) * b = b ^ k := by
        rw [← pow_succ]
        congr 1
        omega
      have hd_le_bk : b ^ (k - 1) ≤ b ^ k := by
        have : b ^ (k - 1) ≤ b ^ (k - 1) * b := Nat.le_mul_of_pos_right _ hb_pos
        linarith [hd_lt]
      have hj_le_bk : j ≤ b ^ k := le_trans hj_ub hd_le_bk
      have hjd_le_bk : j + b ^ (k - 1) ≤ b ^ k := by
        -- j ≤ b^(k-1) and 2 * b^(k-1) ≤ b * b^(k-1) = b^k since b ≥ 3 ≥ 2.
        have h2d : 2 * b ^ (k - 1) ≤ b * b ^ (k - 1) :=
          Nat.mul_le_mul_right (b ^ (k - 1)) (by linarith)
        have h2dle : 2 * b ^ (k - 1) ≤ b ^ k := by
          rw [Nat.mul_comm b (b ^ (k - 1))] at h2d
          linarith [hd_lt]
        linarith
      -- Mono triple (b^k, j, j + b^(k-1)).
      refine ⟨b ^ k, j, j + b ^ (k - 1), le_refl _, hj_le_bk, hjd_le_bk, ?_, ?_, ?_⟩
      · refine ⟨hb_pow_pos, by linarith, by linarith, ?_⟩
        -- b^k + b * j = b * (j + b^(k-1))
        have h1 : b * (j + b ^ (k - 1)) = b * j + b ^ (k - 1) * b := by ring
        linarith [hd_lt, h1]
      · rw [hχj]
      · rw [hχj, hχj']
    · -- Already a mono on smaller domain; lift.
      have hMono : HasMonoSolution b (b ^ k - 1) χ := by
        by_contra h
        exact hAvoid h
      obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
      refine ⟨x, y, z, ?_, ?_, ?_, hRT, hxy, hyz⟩
      · exact le_trans hxn (Nat.sub_le _ _)
      · exact le_trans hyn (Nat.sub_le _ _)
      · exact le_trans hzn (Nat.sub_le _ _)

/-! ### Round 41 (2026-05-15) — connecting the DPL architecture to
    the paper's SAT axiom.

  `lem_keypair_sat` is essentially `DistancePairProperty` (the
  paper's `lem:keypair` as a SAT-verified atom).  The conclusions
  are identical *except* for the upper bound on $j$:

  * `lem_keypair_sat`: $j \le b^{k-1}$.
  * `DistancePairProperty`: $j + b^{k-1} \le b^k - 1$.

  For $b \ge 3$, $2 \le k$, these are compatible: $j \le b^{k-1}$
  and $3 \cdot b^{k-1} \le b^k$ together give $j + b^{k-1} \le
  2 b^{k-1} \le b^k - b^{k-1} \le b^k - 1$.

  Round 41 closes the connection:
  * `dpl_property_from_keypair_sat`: bridge from
    `lem_keypair_sat` to `DistancePairProperty b k` for the
    SAT-verified range.
  * `thm_sat_via_dpl_route`: re-derives `thm_sat` through
    `dpl_implies_rado_upper` (Round 10), confirming that my DPL
    abstraction is exactly the paper's mechanism.

  This validates the DPL architecture end-to-end against the
  paper's actual SAT axiom — the architecture is not isolated, it
  composes with the paper's stated mechanism. -/

/--
  **Round 41 Lemma — `DistancePairProperty` from
  `lem_keypair_sat`.**

  For the $(b, k)$ pairs SAT-verified by `lem_keypair_sat`
  ($k = 3$, $b \in \{3, \ldots, 10\}$; $k = 4$,
  $b \in \{3, 4, 5\}$ — encoded by `hbk`), the paper's
  SAT-verified `lem_keypair_sat` implies `DistancePairProperty
  b k`: the bound $j \le b^{k-1}$ from `lem_keypair_sat` is
  converted to the $j + b^{k-1} \le b^k - 1$ form required by
  `DistancePairProperty`, via $3 \cdot b^{k-1} \le b \cdot
  b^{k-1} = b^k$ for $b \ge 3$.
-/
theorem dpl_property_from_keypair_sat (b k : ℕ)
    (hbk : (k = 3 ∧ 3 ≤ b ∧ b ≤ 10) ∨ (k = 4 ∧ 3 ≤ b ∧ b ≤ 5)) :
    DistancePairProperty b k := by
  -- Recover the numeric bounds 3 ≤ b, 2 ≤ k from the verified set.
  have hb : 3 ≤ b := by rcases hbk with ⟨_, hb, _⟩ | ⟨_, hb, _⟩ <;> exact hb
  have hk2 : 2 ≤ k := by rcases hbk with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  intro χ hValid hAvoid c hc
  obtain ⟨j, hj_lb, hj_ub, hχj, hχjd⟩ :=
    lem_keypair_sat b k hbk χ hValid hAvoid c hc
  refine ⟨j, hj_lb, ?_, hχj, hχjd⟩
  -- j + b^(k-1) ≤ b^k - 1, from j ≤ b^(k-1) and 3 * b^(k-1) ≤ b^k.
  have hb_pow_pos : 1 ≤ b ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hd_eq : b ^ k = b ^ (k - 1) * b := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq, pow_succ]
  have h_three_d_le : 3 * b ^ (k - 1) ≤ b ^ k := by
    have h1 : 3 * b ^ (k - 1) ≤ b * b ^ (k - 1) :=
      Nat.mul_le_mul_right (b ^ (k - 1)) hb
    have h2 : b * b ^ (k - 1) = b ^ k := by rw [hd_eq]; ring
    linarith
  omega

/--
  **Round 41 Theorem — `thm_sat_via_dpl_route`: $R_k(b) = b^k$ via
  the DPL architecture.**

  For the SAT-verified set ($k = 3$, $b \in \{3, \ldots, 10\}$;
  $k = 4$, $b \in \{3, 4, 5\}$ — encoded by `hbk`), re-derives
  `thm_sat` by composing `dpl_property_from_keypair_sat` with
  `dpl_implies_rado_upper` (Round 10).  Same axiom dependency as
  the direct `thm_sat` (only `lem_keypair_sat`), different proof
  routing — confirms that my Round-10 DPL abstraction is exactly
  the paper's mechanism.
-/
theorem thm_sat_via_dpl_route (b k : ℕ)
    (hbk : (k = 3 ∧ 3 ≤ b ∧ b ≤ 10) ∨ (k = 4 ∧ 3 ≤ b ∧ b ≤ 5)) :
    IsRadoNumber b k (b ^ k) := by
  -- Recover the numeric bounds 3 ≤ b, 2 ≤ k from the verified set.
  have hb : 3 ≤ b := by rcases hbk with ⟨_, hb, _⟩ | ⟨_, hb, _⟩ <;> exact hb
  have hk2 : 2 ≤ k := by rcases hbk with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  exact ⟨thm_lower b k (by linarith) (by linarith),
   dpl_implies_rado_upper b k (by linarith) (by linarith)
     (dpl_property_from_keypair_sat b k hbk)⟩

end RadoNumbers
