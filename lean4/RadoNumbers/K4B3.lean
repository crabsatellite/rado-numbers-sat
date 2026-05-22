/-
  RadoNumbers/K4B3.lean

  Definition `def:gstar`, Proposition `prop:gstar-tree`, Lemma
  `lem:gstartree` (Combined-$G^*$-Tree Lemma; SAT-verified), and
  Theorem `thm:k4b3` ($R_4(3) = 81$). Companion to Li 2026
  "On Rado Numbers for $x + by = bz$".

  The boundary case $b = 3, k = 4$ of the threshold conjecture
  $k \le 2(b-1)$ at $b = 3$. The upper bound $R_4(3) \le 81$ has
  a fully analytic structural reduction (a self-loop step at the
  triple $(81, 54, 81)$ combined with the case analysis over the
  tree-shaped obstruction graph $G^* = G_{27} \cup G_{\mathrm{ext}}$)
  and a single SAT-verified key lemma (Combined-$G^*$-Tree Lemma).

  Encoding:

  * `G27`, `Gext`, `Gstar` — concrete definitions of the edge sets
    as `Finset (ℕ × ℕ)`.
  * `prop_gstar_tree` — paper-novel structural proposition (Cat 3
    working assumption pending full Lean derivation); analytic
    proof in paper Section "The Boundary Case $R_4(3) = 81$".
  * `lem_gstartree` — Cat 2 SAT-verified atom (paper's SAT
    verification with DRAT certificate and MUS lower bound 947).
  * `thm_k4b3` — derived theorem combining `thm_lower` (lower
    bound) with the self-loop step and `lem_gstartree`.
-/

import RadoNumbers.Basic
import RadoNumbers.LowerBound
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace RadoNumbers

/-! ### Definition `def:gstar` — the graph $G^*$. -/

/-- Type-A edges $G_{27} = \{(y, y + 27) : 1 \le y \le 53\}$. -/
def G27 : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 53).image (fun y => (y, y + 27))

/-- Type-B edges $G_{\mathrm{ext}} = \{(3d, 81 - d) : 1 \le d \le 26\}$. -/
def Gext : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 26).image (fun d => (3 * d, 81 - d))

/-- The graph $G^* = G_{27} \cup G_{\mathrm{ext}}$ on vertices
    $\{1, \ldots, 80\}$. -/
def Gstar : Finset (ℕ × ℕ) := G27 ∪ Gext

/-! ### Proposition `prop:gstar-tree` — derived structural lemmas.

  Paper Proposition `prop:gstar-tree` records four structural facts
  about $G^*$ which the paper proves analytically: $|G_{27}| = 53$,
  $|G_{\mathrm{ext}}| = 26$, $G_{27} \cap G_{\mathrm{ext}} =
  \emptyset$, $|G^*| = 79 = |V| - 1$, and connectedness (hence the
  tree property). Our Lean proof of `thm_k4b3` does NOT consume
  the tree property: it uses only `lem_gstartree` (Cat 2 SAT) plus
  the explicit `G27_mem_iff` / `Gext_mem_iff` / `Gstar_mem_iff`
  unfoldings of the `Finset` definitions. Per the anti-pattern
  catalogue §4 #7 ("Phantom downstream user"), we therefore do not
  axiomatize `prop_gstar_tree`; the structural facts are
  paper-narrative content backed by the explicit `Finset`
  constructions in this file (any user who needs cardinality /
  disjointness can derive them via Mathlib `Finset.card_image_*`
  + paper's disjointness argument $|81 - 4d| \ne 27$ for $d \in
  \{1, \ldots, 26\}$, $4d \in \{54, 108\}$ impossible). -/

/-! ### Lemma `lem:gstartree` — Cat 2 SAT-verified. -/

/--
  **Lemma `lem:gstartree` (Combined-$G^*$-Tree Lemma; Cat 2
  SAT-verified atom).**

  In any valid 4-coloring $\chi : \{1, \ldots, 80\} \to
  \{0, 1, 2, 3\}$ avoiding monochromatic solutions to
  $x + 3·y = 3·z$, every color class $C_c = \chi^{-1}(c)$
  contains at least one monochromatic edge of $G^*$.

  *Justification:* SAT-verification (Li 2026, Lemma
  `lem:gstartree` and §6.1). Four SAT instances over $4 \cdot 80
  = 320$ Boolean variables, each verified UNSAT by CaDiCaL 1.5.3
  in under one second per color, with DRAT-certifiable proofs and
  a MUS lower bound of $947$ of $1729$ candidate Rado triples
  (deletion-based MUS shrinking).

  *Status:* `gapOpen` Cat 2 SAT-verified.
-/
axiom lem_gstartree (χ : ℕ → ℕ)
    (hValid : IsValidColoring 80 4 χ)
    (hAvoid : AvoidsMonoSolution 3 80 χ) :
    ∀ c, c < 4 →
      ∃ u v, (u, v) ∈ Gstar ∧ χ u = c ∧ χ v = c

/-! ### Auxiliary unfolding lemmas. -/

/-- Every element of `G27` has the explicit Type-A form. -/
lemma G27_mem_iff {p : ℕ × ℕ} :
    p ∈ G27 ↔ ∃ y, 1 ≤ y ∧ y ≤ 53 ∧ p = (y, y + 27) := by
  simp only [G27, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; exact ⟨y, h1, h2, rfl⟩
  · rintro ⟨y, h1, h2, rfl⟩; exact ⟨y, ⟨h1, h2⟩, rfl⟩

/-- Every element of `Gext` has the explicit Type-B form. -/
lemma Gext_mem_iff {p : ℕ × ℕ} :
    p ∈ Gext ↔ ∃ d, 1 ≤ d ∧ d ≤ 26 ∧ p = (3 * d, 81 - d) := by
  simp only [Gext, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨d, ⟨h1, h2⟩, rfl⟩; exact ⟨d, h1, h2, rfl⟩
  · rintro ⟨d, h1, h2, rfl⟩; exact ⟨d, ⟨h1, h2⟩, rfl⟩

/-- Every element of `Gstar` is in `G27` or `Gext`. -/
lemma Gstar_mem_iff {p : ℕ × ℕ} :
    p ∈ Gstar ↔ p ∈ G27 ∨ p ∈ Gext := by
  simp [Gstar, Finset.mem_union]

/-! ### Theorem `thm:k4b3`. -/

/--
  **Theorem `thm:k4b3`.** $R_4(3) = 81$.

  Lower bound: from `thm_lower` at $b = 3, k = 4$ (note
  $3^4 = 81$). Upper bound: proof by contradiction via
  self-loop step and `lem_gstartree`.

  Self-loop step: $81 + 3 · 54 = 243 = 3 · 81$, so the triple
  $(81, 54, 81)$ satisfies $x + 3·y = 3·z$ with $x = z = 81$.
  Thus $\chi(54) \ne \chi(81)$.

  Combined-$G^*$-Tree step: by `lem_gstartree` applied to color
  $c^* := \chi(81)$, there exists a monochromatic edge $(u, v)
  \in G^*$ with $\chi(u) = \chi(v) = c^*$.

  Case (a) edge in $G_{27}$: $(u, v) = (y, y + 27)$; the triple
  $(81, y, y + 27)$ satisfies $81 + 3y = 3(y + 27)$, mono.

  Case (b) edge in $G_{\mathrm{ext}}$: $(u, v) = (3d, 81 - d)$;
  the triple $(3d, 81 - d, 81)$ satisfies $3d + 3(81 - d) = 243
  = 3 · 81$, mono.
-/
theorem thm_k4b3 : IsRadoNumber 3 4 81 := by
  refine ⟨?_, ?_⟩
  · -- Lower bound.
    have h := thm_lower 3 4 (by norm_num) (by norm_num)
    have : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [← this]
    exact h
  · -- Upper bound.
    intro χ hValid
    -- The restriction to {1, …, 80} is also valid.
    have hValid_80 : IsValidColoring 80 4 χ := fun m hm_lb hm_ub =>
      hValid m hm_lb (by omega)
    -- Either χ already has a mono on {1, …, 80}, or it avoids one.
    by_cases hAvoid : AvoidsMonoSolution 3 80 χ
    · -- Pos: apply lem_gstartree at color χ(81).
      have hChi81_lt : χ 81 < 4 := hValid 81 (by norm_num) (le_refl _)
      obtain ⟨u, v, huv_in, huc, hvc⟩ :=
        lem_gstartree χ hValid_80 hAvoid (χ 81) hChi81_lt
      rcases Gstar_mem_iff.mp huv_in with hG27 | hGext
      · -- Case (a): edge in G_27.
        obtain ⟨y, hy_lb, hy_ub, hpair⟩ := G27_mem_iff.mp hG27
        rw [Prod.mk.injEq] at hpair
        obtain ⟨hu_eq, hv_eq⟩ := hpair
        rw [hu_eq] at huc
        rw [hv_eq] at hvc
        -- huc : χ y = χ 81, hvc : χ (y + 27) = χ 81
        refine ⟨81, y, y + 27, le_refl _, by linarith, by linarith, ?_, ?_, ?_⟩
        · refine ⟨by norm_num, by linarith, by linarith, ?_⟩
          ring
        · exact huc.symm
        · exact huc.trans hvc.symm
      · -- Case (b): edge in G_ext.
        obtain ⟨d, hd_lb, hd_ub, hpair⟩ := Gext_mem_iff.mp hGext
        rw [Prod.mk.injEq] at hpair
        obtain ⟨hu_eq, hv_eq⟩ := hpair
        rw [hu_eq] at huc
        rw [hv_eq] at hvc
        have h3d_le : 3 * d ≤ 80 := by
          have : 3 * d ≤ 3 * 26 := Nat.mul_le_mul_left 3 hd_ub
          linarith
        have h81md_le : 81 - d ≤ 80 := by omega
        -- Mono triple (3d, 81 - d, 81).
        refine ⟨3 * d, 81 - d, 81, by linarith, by linarith, le_refl _, ?_, ?_, ?_⟩
        · refine ⟨Nat.mul_pos (by norm_num) hd_lb, by omega, by norm_num, ?_⟩
          -- 3*d + 3*(81 - d) = 3 * 81
          omega
        · exact huc.trans hvc.symm
        · exact hvc
    · -- Neg: already a mono on {1, …, 80}; lift to {1, …, 81}.
      have hMono : HasMonoSolution 3 80 χ := by
        by_contra h
        exact hAvoid h
      obtain ⟨x, y, z, hxn, hyn, hzn, hRT, hxy, hyz⟩ := hMono
      refine ⟨x, y, z, by linarith, by linarith, by linarith, hRT, hxy, hyz⟩

end RadoNumbers
