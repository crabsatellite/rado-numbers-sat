import RadoNumbers.General.R401RUPChecker

/-! # R402 — LRAT add-step checker with soundness theorem

  Lifts the R401 RUP trust kernel to single LRAT add steps via the
  **trace-based fallback** (R402 spec Part 4). Each unit propagation
  is an explicit `UnitJustification (lit, clauseId)`.

  ## Trust kernel chain

    R401.evalClause_false_of_conflict
        ↓
    R402.applyUnit_TrailHolds
        ↓
    R402.applyUnits_TrailHolds
        ↓
    R402.checkRUPTrace_sound
        ↓
    R402.checkAddStep_sound
-/

namespace RadoNumbers.RUPChecker

/-! ## Clause database -/

structure ClauseEntry where
  id : Nat
  clause : Clause
deriving Repr, DecidableEq

abbrev ClauseDB := List ClauseEntry

def dbHolds (τ : Assignment) (db : ClauseDB) : Prop :=
  ∀ e ∈ db, evalClause τ e.clause = true

def lookupClause : ClauseDB → Nat → Option Clause
  | [], _ => none
  | e :: rest, n => if e.id = n then some e.clause else lookupClause rest n

theorem lookupClause_mem (db : ClauseDB) (id : Nat) (c : Clause)
    (h : lookupClause db id = some c) :
    ∃ e ∈ db, e.clause = c := by
  induction db with
  | nil => simp [lookupClause] at h
  | cons hd tl ih =>
    unfold lookupClause at h
    by_cases hid : hd.id = id
    · simp [hid] at h
      exact ⟨hd, List.mem_cons_self, h⟩
    · simp [hid] at h
      obtain ⟨e, he, hclause⟩ := ih h
      exact ⟨e, List.mem_cons_of_mem _ he, hclause⟩

theorem lookupClause_sound
    (db : ClauseDB) (id : Nat) (c : Clause)
    (h : lookupClause db id = some c)
    (τ : Assignment) (hdb : dbHolds τ db) :
    evalClause τ c = true := by
  obtain ⟨e, he, hclause⟩ := lookupClause_mem db id c h
  have := hdb e he
  rw [hclause] at this
  exact this

/-! ## Unit justification and trace -/

structure UnitJustification where
  lit : Lit
  clauseId : Nat
deriving Repr

structure RUPTrace where
  units : List UnitJustification
  conflictClauseId : Nat
deriving Repr

structure LRATAddStep where
  id : Nat
  clause : Clause
  trace : RUPTrace
deriving Repr

/-! ## Trace checker — clean Bool composition -/

/-- Bool predicate: every literal in `c` (except possibly `l`) has its
  negation in `trail`. -/
def allOthersNegated (l : Lit) (trail : List Lit) (c : Clause) : Bool :=
  c.all (fun l' => decide (l' = l) || decide (negLit l' ∈ trail))

/-- Verify one unit-propagation step. -/
def applyUnit (db : ClauseDB) (trail : List Lit) (u : UnitJustification) :
    Option (List Lit) :=
  match lookupClause db u.clauseId with
  | none => none
  | some c =>
    if decide (u.lit ∈ c) && allOthersNegated u.lit trail c then
      some (u.lit :: trail)
    else
      none

def applyUnits : ClauseDB → List Lit → List UnitJustification → Option (List Lit)
  | _, trail, [] => some trail
  | db, trail, u :: rest =>
    match applyUnit db trail u with
    | none => none
    | some trail' => applyUnits db trail' rest

def checkRUPTrace (db : ClauseDB) (target : Clause) (tr : RUPTrace) : Bool :=
  let init := negateClauseLits target
  match applyUnits db init tr.units with
  | none => false
  | some finalTrail =>
    match lookupClause db tr.conflictClauseId with
    | none => false
    | some c => clauseConflict finalTrail c

def checkAddStep (db : ClauseDB) (s : LRATAddStep) : Bool :=
  checkRUPTrace db s.clause s.trace

/-! ## Soundness backbone -/

/-- If a clause is satisfied and all literals except `l` are false in
  the trail, then `l` is true under τ. -/
theorem evalLit_of_unit_in_satisfied_clause
    (τ : Assignment) (trail : List Lit) (c : Clause) (l : Lit)
    (hTH : TrailHolds τ trail)
    (hSat : evalClause τ c = true)
    (hOther : allOthersNegated l trail c = true) :
    evalLit τ l = true := by
  -- From hSat: ∃ x ∈ c, evalLit τ x = true.
  have hany : c.any (evalLit τ) = true := hSat
  obtain ⟨x, hx_mem, hx_eval⟩ := List.any_eq_true.mp hany
  -- From hOther applied to x.
  have hxcheck :
      (decide (x = l) || decide (negLit x ∈ trail)) = true :=
    List.all_eq_true.mp hOther x hx_mem
  -- Case split on which disjunct holds.
  cases hxl : decide (x = l)
  · -- decide (x = l) = false, so decide (negLit x ∈ trail) must be true.
    have hin : negLit x ∈ trail := by
      simp [hxl] at hxcheck
      exact hxcheck
    have hneg_true : evalLit τ (negLit x) = true := hTH (negLit x) hin
    rw [evalLit_negLit τ x] at hneg_true
    rw [hx_eval] at hneg_true
    exact absurd hneg_true (by decide)
  · -- decide (x = l) = true, so x = l.
    have heq : x = l := of_decide_eq_true hxl
    rw [← heq]
    exact hx_eval

/-- `applyUnit` preserves trail consistency under τ. -/
theorem applyUnit_TrailHolds
    (db : ClauseDB) (trail : List Lit) (u : UnitJustification)
    (trail' : List Lit) (h : applyUnit db trail u = some trail')
    (τ : Assignment) (hTH : TrailHolds τ trail) (hdb : dbHolds τ db) :
    TrailHolds τ trail' := by
  unfold applyUnit at h
  cases hLook : lookupClause db u.clauseId with
  | none =>
    simp only [hLook] at h
    exact absurd h (by simp)
  | some c =>
    simp only [hLook] at h
    -- h : (if decide (u.lit ∈ c) && allOthersNegated u.lit trail c then some (u.lit :: trail) else none) = some trail'
    by_cases hCheck : (decide (u.lit ∈ c) && allOthersNegated u.lit trail c) = true
    · -- Check passed
      simp only [hCheck, if_true] at h
      -- h : some (u.lit :: trail) = some trail'
      have htrail_eq : trail' = u.lit :: trail := by
        have := Option.some.injEq (u.lit :: trail) trail' |>.mp h
        exact this.symm
      rw [htrail_eq]
      -- Extract allOthersNegated from hCheck.
      have hall : allOthersNegated u.lit trail c = true := by
        cases hb : allOthersNegated u.lit trail c
        · rw [hb] at hCheck; simp at hCheck
        · rfl
      have hc_sat : evalClause τ c = true :=
        lookupClause_sound db u.clauseId c hLook τ hdb
      have hLit_eval : evalLit τ u.lit = true :=
        evalLit_of_unit_in_satisfied_clause τ trail c u.lit hTH hc_sat hall
      intro lit hlit
      rcases List.mem_cons.mp hlit with rfl | hlit
      · exact hLit_eval
      · exact hTH lit hlit
    · -- Check failed
      have hCheck_false :
          (decide (u.lit ∈ c) && allOthersNegated u.lit trail c) = false := by
        cases hb : (decide (u.lit ∈ c) && allOthersNegated u.lit trail c)
        · rfl
        · exfalso; exact hCheck hb
      simp only [hCheck_false, if_false] at h
      exact absurd h (by simp)

/-- `applyUnits` preserves trail consistency. -/
theorem applyUnits_TrailHolds
    (db : ClauseDB) (us : List UnitJustification) (τ : Assignment)
    (hdb : dbHolds τ db) :
    ∀ trail trail',
      applyUnits db trail us = some trail' →
      TrailHolds τ trail →
      TrailHolds τ trail' := by
  induction us with
  | nil =>
    intro trail trail' h hTH
    unfold applyUnits at h
    cases h
    exact hTH
  | cons u rest ih =>
    intro trail trail' h hTH
    unfold applyUnits at h
    cases hApply : applyUnit db trail u with
    | none =>
      simp only [hApply] at h
      exact absurd h (by simp)
    | some trail1 =>
      simp only [hApply] at h
      have hTH1 : TrailHolds τ trail1 :=
        applyUnit_TrailHolds db trail u trail1 hApply τ hTH hdb
      exact ih trail1 trail' h hTH1

/-- Negated target clause forms a τ-consistent trail when target is false under τ. -/
theorem TrailHolds_negateClauseLits
    (τ : Assignment) (target : Clause)
    (hTarget : evalClause τ target = false) :
    TrailHolds τ (negateClauseLits target) := by
  intro lit hlit
  unfold negateClauseLits at hlit
  obtain ⟨l, hl_mem, hl_eq⟩ := List.mem_map.mp hlit
  rw [← hl_eq]
  have hl_false : evalLit τ l = false :=
    (evalClause_eq_false_iff_all_lits_false τ target).mp hTarget l hl_mem
  rw [evalLit_negLit τ l, hl_false]
  rfl

/-- **`checkRUPTrace_sound`**: target clause forced in any model of db. -/
theorem checkRUPTrace_sound
    (db : ClauseDB) (target : Clause) (tr : RUPTrace)
    (h : checkRUPTrace db target tr = true)
    (τ : Assignment) (hdb : dbHolds τ db) :
    evalClause τ target = true := by
  cases hTarget : evalClause τ target
  · -- False case: derive contradiction.
    exfalso
    have hTH_init : TrailHolds τ (negateClauseLits target) :=
      TrailHolds_negateClauseLits τ target hTarget
    unfold checkRUPTrace at h
    cases hApply : applyUnits db (negateClauseLits target) tr.units with
    | none =>
      simp only [hApply] at h
      exact absurd h (by simp)
    | some finalTrail =>
      simp only [hApply] at h
      have hTH_final : TrailHolds τ finalTrail :=
        applyUnits_TrailHolds db tr.units τ hdb
          (negateClauseLits target) finalTrail hApply hTH_init
      cases hConflict_look : lookupClause db tr.conflictClauseId with
      | none =>
        simp only [hConflict_look] at h
        exact absurd h (by simp)
      | some cc =>
        simp only [hConflict_look] at h
        have hcc_sat : evalClause τ cc = true :=
          lookupClause_sound db tr.conflictClauseId cc hConflict_look τ hdb
        have hcc_false : evalClause τ cc = false :=
          evalClause_false_of_conflict τ finalTrail cc hTH_final h
        rw [hcc_sat] at hcc_false
        exact Bool.noConfusion hcc_false
  · rfl

/-- **`checkAddStep_sound`**: top-level soundness for one LRAT add step. -/
theorem checkAddStep_sound
    (db : ClauseDB) (s : LRATAddStep)
    (h : checkAddStep db s = true)
    (τ : Assignment) (hdb : dbHolds τ db) :
    evalClause τ s.clause = true :=
  checkRUPTrace_sound db s.clause s.trace h τ hdb

/-! ## Toy add-step verification -/

def toyDB : ClauseDB := [
  ⟨1, [(1, true)]⟩,
  ⟨2, [(2, true)]⟩,
  ⟨3, [(3, true)]⟩,
  ⟨4, [(2, false), (3, false), (1, false)]⟩
]

def toyAddEmpty : LRATAddStep := {
  id := 5
  clause := []
  trace := {
    units := [
      ⟨(1, true), 1⟩,
      ⟨(2, true), 2⟩,
      ⟨(3, true), 3⟩
    ]
    conflictClauseId := 4
  }
}

theorem r402_toy_add_check :
    checkAddStep toyDB toyAddEmpty = true := by decide

theorem r402_toy_add_sound :
    ∀ τ, dbHolds τ toyDB → evalClause τ toyAddEmpty.clause = true :=
  fun τ hdb => checkAddStep_sound toyDB toyAddEmpty r402_toy_add_check τ hdb

theorem r402_toy_unsat_via_add_step :
    ¬ ∃ τ, dbHolds τ toyDB := by
  intro ⟨τ, hdb⟩
  have h : evalClause τ [] = true := r402_toy_add_sound τ hdb
  simp [evalClause] at h

end RadoNumbers.RUPChecker
