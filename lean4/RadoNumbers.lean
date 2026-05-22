/-
  RadoNumbers.lean

  Root module.  Machine-checked formalization of the lower bound, four
  upper-bound theorems, the SAT-verified independent-verification
  theorem, the $b^k$ pattern breakdown, and the threshold conjecture of:

    Li, Alex Chengyu. "On Rado Numbers for $x + by = bz$: The $b^k$
                       Pattern and a Threshold Conjecture." 2026.

  Submodules:
    RadoNumbers/Basic.lean         Definitions (b-adic valuation,
                                   IsRadoTriple, valid k-coloring,
                                   AvoidsMonoSolution)
    RadoNumbers/LowerBound.lean    Theorem `thm:lower` ($R_k(b) \ge b^k$)
    RadoNumbers/K2.lean            Lemma `lem:compress2` (Color
                                   Compression) + Theorem `thm:k2`
                                   ($R_2(b) = b^2$)
    RadoNumbers/K3B3.lean          Lemma `lem:k3b3pair` (SAT) +
                                   Theorem `thm:k3b3` ($R_3(3) = 27$)
    RadoNumbers/K4B3.lean          Definition `def:gstar` + Proposition
                                   `prop:gstar-tree` (analytic) +
                                   Lemma `lem:gstartree` (SAT) +
                                   Theorem `thm:k4b3` ($R_4(3) = 81$)
    RadoNumbers/SAT.lean           Lemma `lem:keypair` (Distance Pair;
                                   SAT) + Theorem `thm:sat` (independent
                                   verification of $R_3(b) = b^3$ for
                                   $b \in \{4,\ldots,10\}$ and
                                   $R_4(b) = b^4$ for $b \in \{3,4,5\}$)
    RadoNumbers/Breakdown.lean     Theorem `thm:r5` ($R_5(3) > 243$ via
                                   constructive witness coloring)
    RadoNumbers/Threshold.lean     Conjecture `conj:threshold`
                                   ($R_k(b) = b^k \iff k \le 2(b-1)$)

  Soundness audit:
    RadoNumbers/AxiomAudit.lean — prints axiom dependencies of every
    paper-level theorem.  Expected: Lean kernel (`propext`,
    `Classical.choice`, `Quot.sound`) plus the explicitly declared
    Cat 2 (b-adic-valuation bridges, SAT-verified lemmas, witness-
    coloring validity) and Cat 3 (paper-novel atomic stipulations)
    axioms.

  Gap ledger:
    RadoNumbers/Ledger.lean — typed record of every atomic axiom,
    every Cat 3 carrier / structural equation, and every closed
    top-level result.  Three orthogonal classifications per entry:
      * 6-tier status: gapOpen / gapPartial / gapBlocked / gapDeadEnd /
        gapClosed / gapClosedConditional
      * 4-input-category: cat1Mathlib / cat2External / cat3PaperNovel /
        notInput
      * Cat 3 sub-type: carrier / hypothesisPredicate /
        structuralEquation / workingAssumption / conditionalHypothesis /
        phenomenologicalConjecture / notCat3
    Plus a `conditionalOn` list of `Hyp_*` broken-link predicate names
    for any `gapClosedConditional` entries (currently empty for all
    entries; see v6 §12 broken-link discipline).  Canonical
    attack-history record.
-/

import RadoNumbers.Basic
import RadoNumbers.Foundational
import RadoNumbers.LowerBound
import RadoNumbers.K2
import RadoNumbers.K3General
import RadoNumbers.DPLStructure
import RadoNumbers.K3B3
import RadoNumbers.K4B3
import RadoNumbers.SAT
import RadoNumbers.Breakdown
import RadoNumbers.Threshold
import RadoNumbers.Pillar3Structural
import RadoNumbers.General.PartitionRegular
import RadoNumbers.General.BAdicEquation
import RadoNumbers.General.BasicResults
import RadoNumbers.General.ColumnsCondition
import RadoNumbers.General.Bridge
import RadoNumbers.General.ThresholdConjecture
import RadoNumbers.General.K3CompressionAnalytic
import RadoNumbers.General.K3B4MultiplesCounting
import RadoNumbers.General.K3B4PairAgreement
import RadoNumbers.General.RadoLift
