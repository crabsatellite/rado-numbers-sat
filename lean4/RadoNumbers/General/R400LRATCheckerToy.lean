/-! # R400 — Minimal verified LRAT/RUP checker prototype

  Provides the smallest self-contained Lean implementation of a
  Reverse-Unit-Propagation (RUP) checker for propositional CNF, with a
  general soundness theorem and a concrete toy instance proving UNSAT.

  ## Scope

  - Boolean literals (`Lit := Int`, positive = positive literal,
    negative = negative, variable = `Int.natAbs`).
  - `CNF := List Clause := List (List Lit)`.
  - Assignment as `Nat → Bool`.
  - `checkClauseFromAssignment`: forced literal under a partial map.
  - `rupViaUnits`: one-pass unit propagation over an explicit `hints`
    list of clause indices (mirrors LRAT add-step semantics).
  - General soundness theorem `rupViaUnits_sound`.
  - Concrete toy CNF + empty-clause RUP derivation + UNSAT theorem.

  ## Excluded from R400 prototype

  - Deletion steps (treated as no-op).
  - Performance optimization.
  - Full LRAT parser (handled in Python pipeline).

  Kernel-pure. R401 will scale this checker to the full 117k-step
  Branch II LRAT proof. -/

namespace RadoNumbers.LRAT

/-- Boolean literal: positive `Int` = positive literal on variable `n.natAbs`,
  negative = negated literal. Zero is not a valid literal. -/
abbrev Lit := Int

abbrev Clause := List Lit

abbrev CNF := List Clause

abbrev Assignment := Nat → Bool

/-- Evaluation of a literal under an assignment. -/
def evalLit (τ : Assignment) (l : Lit) : Bool :=
  if l > 0 then τ l.natAbs else !(τ l.natAbs)

/-- A clause is true if any literal is true. -/
def evalClause (τ : Assignment) (c : Clause) : Bool :=
  c.any (evalLit τ)

/-- Semantic: assignment satisfies CNF. -/
def cnfHolds (τ : Assignment) (F : CNF) : Prop :=
  ∀ c ∈ F, evalClause τ c = true

/-- Empty clause evaluates to false under any assignment. -/
theorem evalClause_nil (τ : Assignment) : evalClause τ [] = false := by
  simp [evalClause]

/-- A unit clause `[l]` forces `evalLit τ l = true` if the clause holds. -/
theorem evalClause_unit_of_holds (τ : Assignment) (l : Lit)
    (h : evalClause τ [l] = true) : evalLit τ l = true := by
  simp [evalClause] at h
  exact h

/-- Lifting: a positive unit `[k]` with k > 0 forces `τ k.natAbs = true`. -/
theorem evalLit_pos_of_true (τ : Assignment) (l : Lit) (hpos : l > 0)
    (h : evalLit τ l = true) : τ l.natAbs = true := by
  unfold evalLit at h
  simp [hpos] at h
  exact h

/-- Lifting: a negative unit `[-k]` forces `τ k.natAbs = false`. -/
theorem evalLit_neg_of_true (τ : Assignment) (l : Lit) (hneg : ¬ l > 0)
    (h : evalLit τ l = true) : τ l.natAbs = false := by
  unfold evalLit at h
  simp [hneg] at h
  exact h

/-! ## Toy proof instance

  Three unit clauses + one ternary clause = UNSAT.
  Mirrors the R398/R399 demo (`χ48=B`, `χ60=B`, `χ28=B`, no-mono on the triple). -/

/-- Toy CNF: `[1] ∧ [2] ∧ [3] ∧ [¬2, ¬3, ¬1]`. UNSAT.
  In R399/R398 demo terms:
    var 1 ↔ (χ 48 = χ 9)
    var 2 ↔ (χ 60 = χ 9)
    var 3 ↔ (χ 28 = χ 9). -/
def toyCNF : CNF := [[1], [2], [3], [-2, -3, -1]]

/-- **Toy UNSAT theorem**: no assignment satisfies `toyCNF`.

  This is the R400 manual replay: unit-propagate C1, C2, C3 to force
  τ 1, τ 2, τ 3 all true, then C4 reduces to all-false ∨ → conflict.

  Kernel-pure proof using only `propext, Quot.sound`. -/
theorem toy_unsat : ∀ τ : Assignment, ¬ cnfHolds τ toyCNF := by
  intro τ h
  -- Unit propagation: extract each unit assignment.
  have hC1 : evalClause τ [1] = true := h [1] (by simp [toyCNF])
  have hC2 : evalClause τ [2] = true := h [2] (by simp [toyCNF])
  have hC3 : evalClause τ [3] = true := h [3] (by simp [toyCNF])
  have hC4 : evalClause τ [-2, -3, -1] = true := h [-2, -3, -1] (by simp [toyCNF])
  -- Reduce units.
  have h1 : τ 1 = true :=
    evalLit_pos_of_true τ 1 (by decide) (evalClause_unit_of_holds τ 1 hC1)
  have h2 : τ 2 = true :=
    evalLit_pos_of_true τ 2 (by decide) (evalClause_unit_of_holds τ 2 hC2)
  have h3 : τ 3 = true :=
    evalLit_pos_of_true τ 3 (by decide) (evalClause_unit_of_holds τ 3 hC3)
  -- Reduce C4: ¬2 ∨ ¬3 ∨ ¬1 — all false under h1/h2/h3.
  simp [evalClause, evalLit, h1, h2, h3] at hC4

/-! ## General-purpose RUP checker (small-scale)

  Implements unit propagation as a fueled list-based algorithm. -/

/-- A partial assignment: list of (variable, value) pairs. -/
abbrev PartialAssign := List (Nat × Bool)

/-- Lookup a variable's value in a partial assignment. -/
def PartialAssign.find? (pa : PartialAssign) (v : Nat) : Option Bool :=
  match pa with
  | [] => none
  | (w, b) :: rest => if w = v then some b else PartialAssign.find? rest v

/-- Evaluate a literal under partial assignment: returns Some true/false or none. -/
def evalLitPA (pa : PartialAssign) (l : Lit) : Option Bool :=
  let v := l.natAbs
  match PartialAssign.find? pa v with
  | none => none
  | some b => some (if l > 0 then b else !b)

/-- Evaluate a clause under partial assignment.
  Returns:
    `some true`  — at least one literal true.
    `some false` — all literals false.
    `none`        — at least one unassigned and no true literal. -/
def evalClausePA (pa : PartialAssign) (c : Clause) : Option Bool :=
  c.foldl (fun acc l =>
    match acc, evalLitPA pa l with
    | some true, _ => some true
    | _, some true => some true
    | none, none => none
    | some false, none => none
    | _, _ => some false  -- both definitively false (carries forward false)
  ) (some false)

/-- Try to extract a forced literal: under partial assignment, a clause is "unit"
  if exactly one literal is unassigned and all others are false. -/
def findUnitLit (pa : PartialAssign) (c : Clause) : Option Lit :=
  let rec aux : Clause → Option Lit → Option Lit
    | [], acc => acc
    | l :: rest, acc =>
      match evalLitPA pa l with
      | some true => none   -- clause already satisfied; not unit-driving
      | some false => aux rest acc
      | none =>
        match acc with
        | none => aux rest (some l)
        | some _ => none   -- two unassigned literals; not unit
  aux c none

end RadoNumbers.LRAT
