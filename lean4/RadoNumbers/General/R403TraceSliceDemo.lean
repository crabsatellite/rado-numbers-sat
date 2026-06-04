import RadoNumbers.General.R403LRATProofReplay

/-! # R403 Trace Slice Demo

  Auto-generated tiny Lean slice of the symbolic Branch II LRAT proof.
  Demonstrates that the R402/R403 trace-based checker can mechanically
  process generated traces.

  Slice size and processing time configurable via R403_emit_trace_slice_lean.py
  `--max-steps` flag.
-/

namespace RadoNumbers.RUPChecker

/-- Initial DB slice (first 3 clauses). -/
def sliceInitDB : ClauseDB := [
  ⟨592, [(9, false), (5, false), (9, false)]⟩,
  ⟨593, [(10, false), (6, false), (10, false)]⟩,
  ⟨594, [(11, false), (7, false), (11, false)]⟩
]

/-- Generated proof slice. -/
def sliceSteps : List LRATAddStep := [
  {
    id := 7824
    clause := [(9, false), (5, false)]
    trace := {
      units := []
      conflictClauseId := 592
    }
  },
  {
    id := 7825
    clause := [(10, false), (6, false)]
    trace := {
      units := []
      conflictClauseId := 593
    }
  },
  {
    id := 7826
    clause := [(11, false), (7, false)]
    trace := {
      units := []
      conflictClauseId := 594
    }
  }
]

/-- Slice check passes. -/
theorem r403_slice_check :
    checkProof sliceInitDB sliceSteps = true := by native_decide

end RadoNumbers.RUPChecker
