import RadoNumbers.General.R402LRATAddStep

/-! # R403 — Multi-step LRAT proof replay with soundness theorem

  Lifts the R402 single-add-step checker to **proof-sequence replay**:
  given an initial clause database and a list of LRAT add steps, verify
  that each step's derived clause is RUP-entailed by the current DB,
  extending the DB after each step.

  If the final database contains the empty clause, the original DB is UNSAT.

  ## Trust chain (continued from R402)

    R402.checkAddStep_sound
        ↓
    R403.dbHolds_addClauseEntry  (extend DB preserves satisfaction)
        ↓
    R403.checkProof_sound        (replay all steps preserves satisfaction)
        ↓
    R403.checkProof_unsat_of_empty  (empty clause in final DB ⇒ UNSAT)
-/

namespace RadoNumbers.RUPChecker

/-! ## DB extension and replay -/

/-- Add a new derived clause to the database. -/
def addClauseEntry (db : ClauseDB) (s : LRATAddStep) : ClauseDB :=
  ⟨s.id, s.clause⟩ :: db

/-- Sequential proof replay: check each add step against current DB,
  extending DB on success. Returns `false` if any step fails. -/
def checkProof : ClauseDB → List LRATAddStep → Bool
  | _, [] => true
  | db, s :: ss =>
    if checkAddStep db s then
      checkProof (addClauseEntry db s) ss
    else
      false

/-- Final clause database after replaying all steps (regardless of check result). -/
def replayDB : ClauseDB → List LRATAddStep → ClauseDB
  | db, [] => db
  | db, s :: ss => replayDB (addClauseEntry db s) ss

/-! ## Soundness backbone -/

/-- Adding a satisfied derived clause preserves DB satisfaction. -/
theorem dbHolds_addClauseEntry
    (τ : Assignment) (db : ClauseDB) (s : LRATAddStep)
    (hdb : dbHolds τ db)
    (hnew : evalClause τ s.clause = true) :
    dbHolds τ (addClauseEntry db s) := by
  intro e he
  unfold addClauseEntry at he
  rcases List.mem_cons.mp he with rfl | he
  · exact hnew
  · exact hdb e he

/-- **`checkProof_sound`**: replay preserves DB satisfaction.

  If the proof checks and τ satisfies the initial DB, then τ satisfies
  the final replayed DB (every derived clause is also satisfied). -/
theorem checkProof_sound
    (db : ClauseDB) (steps : List LRATAddStep)
    (hcheck : checkProof db steps = true)
    (τ : Assignment) (hdb : dbHolds τ db) :
    dbHolds τ (replayDB db steps) := by
  induction steps generalizing db with
  | nil =>
    unfold replayDB
    exact hdb
  | cons s ss ih =>
    unfold checkProof at hcheck
    by_cases hstep : checkAddStep db s = true
    · -- step passed
      simp only [hstep, if_true] at hcheck
      have hnew : evalClause τ s.clause = true :=
        checkAddStep_sound db s hstep τ hdb
      have hdb' : dbHolds τ (addClauseEntry db s) :=
        dbHolds_addClauseEntry τ db s hdb hnew
      unfold replayDB
      exact ih (addClauseEntry db s) hcheck hdb'
    · -- step failed
      have hstep_false : checkAddStep db s = false := by
        cases h : checkAddStep db s
        · rfl
        · exfalso; exact hstep h
      simp only [hstep_false, if_false] at hcheck
      exact absurd hcheck (by simp)

/-- The empty clause evaluates to false under any assignment. -/
theorem evalClause_empty_false (τ : Assignment) : evalClause τ [] = false := by
  rfl

/-- **`checkProof_unsat_of_empty`**: if the proof checks and the final
  DB contains the empty clause, then the initial DB is UNSAT. -/
theorem checkProof_unsat_of_empty
    (db : ClauseDB) (steps : List LRATAddStep)
    (hcheck : checkProof db steps = true)
    (hempty : ∃ id, ClauseEntry.mk id [] ∈ replayDB db steps) :
    ¬ ∃ τ, dbHolds τ db := by
  intro ⟨τ, hτ⟩
  have hfinal : dbHolds τ (replayDB db steps) :=
    checkProof_sound db steps hcheck τ hτ
  rcases hempty with ⟨id, hid⟩
  have hEmpty : evalClause τ [] = true := by
    have := hfinal ⟨id, []⟩ hid
    exact this
  rw [evalClause_empty_false] at hEmpty
  exact Bool.noConfusion hEmpty

/-! ## Toy multi-step verification -/

/-- Toy proof: single add step deriving empty clause. -/
def toyProof : List LRATAddStep := [toyAddEmpty]

theorem r403_toy_checkProof :
    checkProof toyDB toyProof = true := by decide

/-- The empty clause is in the final replayed DB. -/
theorem r403_toy_empty_mem :
    ∃ id, ClauseEntry.mk id [] ∈ replayDB toyDB toyProof := by
  refine ⟨5, ?_⟩
  decide

/-- **R403 milestone**: toy UNSAT via multi-step replay. -/
theorem r403_toy_replay_unsat :
    ¬ ∃ τ, dbHolds τ toyDB :=
  checkProof_unsat_of_empty toyDB toyProof
    r403_toy_checkProof r403_toy_empty_mem

end RadoNumbers.RUPChecker
