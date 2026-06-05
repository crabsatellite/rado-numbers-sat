/-
  RadoNumbers/AxiomAudit.lean


  Prints the axiom dependency list for every paper-level theorem.

  Trust policy.  Every `axiom` declaration in the project falls
  into exactly one of three categories (per
  `feedback_gap_ledger_in_lean4` ATOMIC MINIMAL UNITS
  interpretation):

    Cat 1 — Mathlib-derivable: claim closes via Mathlib + kernel.
            Must be encoded as `theorem`, not `axiom`.  Project
            has no Cat 1 axioms.  The b-adic valuation properties
            COULD be Cat 1 (Mathlib has `multiplicity` and
            `padicValNat`) but the connection to the recursive
            `bAdicVal` of `Basic.lean` is non-trivial and
            currently encoded as Cat 2 textbook citation.

    Cat 2 — External published (textbook / peer-reviewed paper /
            paper's own SAT-verified computational evidence):
            opaque-carrier-bound atomic axiom + precise citation.

    Cat 3 — Paper-novel: workingAssumption (Color Compression
            Lemma; awaiting in-Lean derivation),
            structuralEquation (Proposition `prop:gstar-tree`),
            or phenomenologicalConjecture (Threshold Conjecture).

  Plus the Lean kernel axioms (`propext`, `Classical.choice`,
  `Quot.sound`), provided by Lean / Mathlib core.

  Constraints.  No (E) custom-scaffolding axioms.  No composite
  axioms bundling multiple independent textbook results or hybrid
  Cat 2 + Cat 3 steps.

  Inventory by category — CURRENT STATE after Round 18
  (2026-05-15).  Live counts: `lake env lean
  RadoNumbers/Ledger.lean`.

  **Major progress Rounds 14-18**: 6 former axioms ANALYTICALLY
  CLOSED (converted to derived theorems):
    - `lem_compress2` (Round 14, minimal-deviation argument)
    - `thm_k2_b2` (Round 15, explicit case analysis)
    - `bAdicVal_b_mul`, `bAdicVal_lt_pow`, `bAdicVal_add_of_lt`
      (Rounds 16-17, recursive-definition unfolding + induction)
    - `thm_k3b3_upper_sat` (Round 18, derived via `cascade_step`)
  Plus the phantom `lem_k3b3pair_sat` REMOVED (Pattern 7).

  As a result, `thm_lower` and `thm_k2` are FULLY KERNEL-PURE
  (`[propext, Classical.choice, Quot.sound]` only — zero axioms).

    Cat 2 propositional axioms remaining (5; SAT-verified):
      lem_compress3_general — compression hypothesis for k=3,
                           b ∈ {3,...,10} (cascade-step input)
      lem_gstartree      — Combined-G*-Tree Lemma
      lem_keypair_sat    — Distance Pair Lemma
      r5_witness_valid_sat — explicit 243-entry witness validity
      r5_296_sat         — R_5(3) > 296 (incremental SAT)

    No Cat 3 (paper-novel) axioms remain: `thm_k3b3` was
    de-axiomatized in Round 246 via the b-adic-equation route.

    (`threshold_conjecture_statement` is a `def : Prop`, NOT an
    axiom — the threshold conjecture is stated, never asserted.)

    NOTE: Paper Proposition `prop:gstar-tree` removed Round 9 per
    anti-pattern §4 #7; `lem_k3b3pair_sat` removed Round 18 same
    pattern.

  Per-axiom citations live in the corresponding `axiom` docstring
  in the source file.  Round-history lives in
  `gap_*.attackHistory` fields inside `RadoNumbers.Ledger`.

  **GENERAL Mathlib-style framework (RadoNumbers/General/)**: defines
  `LinearEquation`, `IsKPartitionRegular`, `IsRadoNumber`, etc. for
  arbitrary linear equations over ℤ, building toward eventual Mathlib
  Rado's theorem.  All project theorems for `bAdicEquation b` (b-adic
  Rado equation x + b·y - b·z = 0) bridged through `Bridge.lean`:
    - Unconditional kernel-pure: R_1(b)=b, R_2(b)=b^2 (universal),
      R_2(2)=4, R_2(3)=9 (direct), R_2(4..10) (corollaries), all
      breakdown R_k(2)>2^k for k ∈ {3..8}.
    - Cat 2 SAT axiom dependent: R_3(3)=27 (+lem_compress3_general),
      R_4(3)=81 (+lem_gstartree), R_k(b)=b^k for the SAT-verified set
      (k=3, 3 ≤ b ≤ 10; k=4, 3 ≤ b ≤ 5) (+lem_keypair_sat),
      R_5(3)>243 (+r5_witness_valid_sat), R_5(3)>296 (+r5_296_sat).
    - CONDITIONAL kernel-pure capstone:
      isRadoNumber_bAdicEquation_threshold_conditional (R_k(b)=b^k for
      b ≥ 3, k ≥ 2 modulo CompressionHyp/OmittedPairHyp per level).
    - PILLAR 3 reduction:
      hasMonoSolution_bAdicEquation_three_27_under_localShift_constant
      reduces R_3(3) ≤ 27 to IsLocalShiftConstant on mono-free 3-colorings.
    - Threshold conjecture statements: ThresholdConjecture (upper bound)
      and ThresholdDichotomy (both directions) as Prop (not axioms).

  Per-theorem axiom dependency profile (verified by
  `#print axioms` below):

    * FULLY KERNEL-PURE ([propext, Classical.choice, Quot.sound]):
        thm_lower, thm_k2, thm_k3b3
        (thm_k3b3 de-axiomatized in Round 246)

    * Lean kernel + SAT (G*-tree):
        thm_k4b3
        (depends on: lem_gstartree)

    * Lean kernel + Distance Pair SAT:
        thm_sat
        (depends on: lem_keypair_sat)

    * Lean kernel + r5 witness validity SAT:
        thm_r5_243
        (depends on: r5_witness_valid_sat)

    * Lean kernel + r5 296 SAT:
        thm_r5_296
        (depends on: r5_296_sat)

  Cascade infrastructure (Rounds 9-13), all fully kernel-pure:
    dpl_pigeonhole, dpl_class_bound, dpl_implies_rado_upper,
    dpl_implies_isRadoNumber, multiples_subcoloring_valid,
    relabel_omitted_color, cascade_step, thm_k1.

  DPL cascade architecture (Rounds 21-33), all fully kernel-pure
  (no project axioms anywhere in these derivations):
    dpl_property_k2, thm_k2_via_dpl, dpl_lift_distance_pair,
    pow_sub_one_div, multiples_subcoloring_valid_at_pow,
    dpl_recursion_nonomitted, dpl_recursion_conditional,
    dpl_omitted_pair_of_count, dpl_cascade,
    thm_threshold_conditional, compression_hyp_k2,
    omitted_pair_hyp_k2, thm_k2_via_cascade,
    rado_triple_fst_multiple, rado_triple_fst_not_omitted,
    rado_triple_characterization, mono_solution_characterization.
  The conditional threshold capstone `thm_threshold_conditional`
  derives R_k(b) = b^k for all k ≥ 2 with ZERO project axioms,
  isolating the entire remaining content into the two per-level
  hypothesis families CompressionHyp / OmittedPairHyp.

  Any axiom outside the inventory above is a RED FLAG —
  investigate.

  Usage:
    lake exe cache get
    lake env lean RadoNumbers/AxiomAudit.lean
-/

import RadoNumbers

-- Lower-bound theorem (FULLY KERNEL-PURE).
#print axioms RadoNumbers.thm_lower

-- Upper-bound theorems.
#print axioms RadoNumbers.thm_k2          -- FULLY KERNEL-PURE
#print axioms RadoNumbers.thm_k3b3        -- FULLY KERNEL-PURE (Round 246)
#print axioms RadoNumbers.thm_k4b3        -- + lem_gstartree
#print axioms RadoNumbers.thm_sat         -- + lem_keypair_sat
#print axioms RadoNumbers.thm_r5_243      -- + r5_witness_valid_sat
#print axioms RadoNumbers.thm_r5_296      -- + r5_296_sat

-- Cascade infrastructure (FULLY KERNEL-PURE).
#print axioms RadoNumbers.thm_k1
#print axioms RadoNumbers.cascade_step
#print axioms RadoNumbers.multiples_subcoloring_valid
#print axioms RadoNumbers.dpl_implies_rado_upper
#print axioms RadoNumbers.dpl_pigeonhole
#print axioms RadoNumbers.dpl_class_bound
#print axioms RadoNumbers.dpl_implies_isRadoNumber
#print axioms RadoNumbers.relabel_omitted_color

-- b-adic valuation bridges (now theorems, FULLY KERNEL-PURE).
#print axioms RadoNumbers.bAdicVal_b_mul
#print axioms RadoNumbers.bAdicVal_lt_pow
#print axioms RadoNumbers.bAdicVal_add_of_lt

-- Color Compression Lemma (now a theorem, FULLY KERNEL-PURE).
#print axioms RadoNumbers.lem_compress2

-- DPL cascade architecture (Rounds 21-33, all FULLY KERNEL-PURE).
-- The matching direction of the threshold conjecture, reduced to
-- the CompressionHyp / OmittedPairHyp families with no project
-- axioms in the derivation chain.
#print axioms RadoNumbers.dpl_property_k2
#print axioms RadoNumbers.thm_k2_via_dpl
#print axioms RadoNumbers.dpl_lift_distance_pair
#print axioms RadoNumbers.pow_sub_one_div
#print axioms RadoNumbers.multiples_subcoloring_valid_at_pow
#print axioms RadoNumbers.dpl_recursion_nonomitted
#print axioms RadoNumbers.dpl_recursion_conditional
#print axioms RadoNumbers.dpl_omitted_pair_of_count
#print axioms RadoNumbers.dpl_cascade
#print axioms RadoNumbers.thm_threshold_conditional
#print axioms RadoNumbers.compression_hyp_k2
#print axioms RadoNumbers.omitted_pair_hyp_k2
#print axioms RadoNumbers.thm_k2_via_cascade
#print axioms RadoNumbers.rado_triple_fst_multiple
#print axioms RadoNumbers.rado_triple_fst_not_omitted
#print axioms RadoNumbers.rado_triple_characterization
#print axioms RadoNumbers.mono_solution_characterization
#print axioms RadoNumbers.color_b_avoids_consecutive
#print axioms RadoNumbers.color_b_card_bound
#print axioms RadoNumbers.chi_pred_multiple_ne
#print axioms RadoNumbers.chi_succ_multiple_ne
#print axioms RadoNumbers.thm_cascade_matching
#print axioms RadoNumbers.thm_threshold_via_cascade
#print axioms RadoNumbers.cascade_compression_hyp_k2
#print axioms RadoNumbers.cascade_compression_hyp_k3  -- + lem_compress3_general
#print axioms RadoNumbers.thm_k3_via_cascade_matching -- + lem_compress3_general
#print axioms RadoNumbers.cascade_compression_hyp_k4_b3 -- + lem_gstartree
#print axioms RadoNumbers.thm_k4b3_via_cascade_matching -- + lem_compress3_general, lem_gstartree
#print axioms RadoNumbers.dpl_property_from_keypair_sat -- + lem_keypair_sat
#print axioms RadoNumbers.thm_sat_via_dpl_route          -- + lem_keypair_sat
#print axioms RadoNumbers.cascade_compression_iff_upper_bound
#print axioms RadoNumbers.bAdicVal_one
#print axioms RadoNumbers.bAdicVal_b_value
#print axioms RadoNumbers.bAdicVal_multiples_omit_zero
#print axioms RadoNumbers.bAdicVal_one_plus_pow_eq_zero
#print axioms RadoNumbers.bAdicVal_distance_pair_color_zero
#print axioms RadoNumbers.cascade_compression_fails_at_breakdown -- + lem_gstartree, r5_witness_valid_sat
#print axioms RadoNumbers.cascade_compression_fails_of_breakdown
#print axioms RadoNumbers.bAdicVal_add_pow_zero_of_unit

-- R438 (2026-05-21) — analytic k=3 compression attack.
-- MultiplesOmitColorK3 / K3MultiplesThreeColorImpossible are
-- `def : Prop` (stated, not asserted) — no axioms to check.
-- The proved theorems below MUST be kernel-pure.
#print axioms RadoNumbers.multiples_omit_color_k3_iff      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.rounds_1_7_constraint_bundle     -- FULLY KERNEL-PURE

-- R440 (2026-05-22) — b=4 Candidate I' diagnostic + analytic bundle.
-- MultiplesSubColoringPopulationB4 is `def : Prop` (R440 verdict: Stop C
-- on direct kernel-pure proof; SAT-verified TRUE at b=4 via the
-- stronger statement that the only multiples-partition is (12, 3, 0)).
-- The proved theorems below MUST be kernel-pure.
#print axioms RadoNumbers.b4_multiples_local_self_loop_bundle          -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_multiples_local_self_loop_bundle_numeric  -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_six_forced_disagreements                  -- FULLY KERNEL-PURE
#print axioms RadoNumbers.multiples_subcoloring_population_b4_def_eq   -- FULLY KERNEL-PURE

-- R441 (2026-05-22) — b=4 pair-agreement at n=32 diagnostic + analytic
-- bundle.  Chi8EqChi12K3B4_at32 is `def : Prop` (R441 verdict: Stop C
-- on direct kernel-pure proof; SAT-verified TRUE at n=32 via Phase A
-- with best MUS = 76 distinct Rado triples — exceeds the ~50 triple
-- compactness threshold).  The proved theorems below MUST be kernel-pure.
#print axioms RadoNumbers.b4_n32_self_loop_bundle                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_16_ne_chi_12                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_20_ne_chi_16                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_32_ne_chi_24                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_30_ne_chi_24                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_F2_16_4_8_not_mono                    -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_F2_32_4_12_not_mono                   -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_F2_32_8_16_not_mono                   -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_F2_32_12_20_not_mono                  -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_12_ne_chi_9                       -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_20_ne_chi_15                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.b4_n32_chi_28_ne_chi_21                      -- FULLY KERNEL-PURE
#print axioms RadoNumbers.chi8_eq_chi12_k3_b4_at32_def_eq               -- FULLY KERNEL-PURE
#print axioms RadoNumbers.bAdicVal_b_pow_mul_unit
#print axioms RadoNumbers.bAdicVal_distance_pair_color_c
#print axioms RadoNumbers.bAdicVal_two_eq_zero
#print axioms RadoNumbers.bAdicVal_distance_pair_color_kminus1
#print axioms RadoNumbers.bAdicVal_distance_pair_witness
#print axioms RadoNumbers.bAdicVal_avoidsMono
#print axioms RadoNumbers.bAdicVal_isValidColoring
#print axioms RadoNumbers.dpp_body_realized
#print axioms RadoNumbers.bAdicVal_unit_factorization
#print axioms RadoNumbers.bAdicVal_eq_iff_factorization
#print axioms RadoNumbers.lem_keypair_at_k2  -- NO SAT, kernel-pure analytic
#print axioms RadoNumbers.multiples_color_no_self_distance
#print axioms RadoNumbers.multiples_color_no_dist_m_of_b_sq_m
#print axioms RadoNumbers.A_c_no_consec_at_b3_k3
#print axioms RadoNumbers.A_c_no_dist_2_at_b3_k3
#print axioms RadoNumbers.AP5_no_partition  -- depends on NO axioms
#print axioms RadoNumbers.AP5_avoidance_contradiction
#print axioms RadoNumbers.compression_3_3_6_1_1_distribution_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_6_12_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_AP_1_4_7_10_13_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_6_15_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_AP_general_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_12_15_21_24_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_6_12_15_21_24_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_corner_A1_3_6_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_6_21_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_6_12_15_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_6_15_24_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_12_21_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_6_24_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_3_12_15_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_with_12_15_21_color_0_infeasible
#print axioms RadoNumbers.compression_3_3_corner_A2_at_6_infeasible
#print axioms RadoNumbers.compression_3_3_broader_dispatch
#print axioms RadoNumbers.compression_3_3_corner_A2_at_12_infeasible
#print axioms RadoNumbers.compression_3_3_corner_A2_at_15_infeasible
#print axioms RadoNumbers.compression_3_3_corner_A2_at_24_infeasible
#print axioms RadoNumbers.compression_3_3_corner_A2_at_21_infeasible
#print axioms RadoNumbers.compression_3_3_corner_dispatch
#print axioms RadoNumbers.compression_3_3_5_2_1_master
#print axioms RadoNumbers.compression_3_3_corner_4_3_1_A1_3_6_7_A2_8_infeasible
#print axioms RadoNumbers.compression_3_3_4_2_2_A2_3_6_infeasible
#print axioms RadoNumbers.compression_3_3_4_2_2_A2_3_24_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_2_A2_9_18_A1_3_12_21_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_1_A1_3_9_12_A2_18_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_2_A2_3_6_A1_9_12_18_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_1_A1_6_9_15_A2_18_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_2_A2_9_18_A1_3_6_24_infeasible
#print axioms RadoNumbers.compression_3_3_4_2_2_A1_3_9_A2_12_18_infeasible
#print axioms RadoNumbers.compression_3_3_6_1_1_A1_6_A2_12_infeasible
-- Round 92 universal structural lemmas.
#print axioms RadoNumbers.rado_self_loop_chi_9_ne_chi_6
#print axioms RadoNumbers.rado_self_loop_chi_18_ne_chi_12
#print axioms RadoNumbers.rado_self_loop_chi_15_ne_chi_10
#print axioms RadoNumbers.rado_self_loop_chi_12_ne_chi_8
#print axioms RadoNumbers.rado_self_loop_chi_21_ne_chi_14
#print axioms RadoNumbers.rado_self_loop_chi_24_ne_chi_16
-- Round 93 generic universal self-loop lemma.
#print axioms RadoNumbers.rado_self_loop_universal
-- Round 94 complementary universal self-loop.
#print axioms RadoNumbers.rado_self_loop_complementary
#print axioms RadoNumbers.rado_triple_distinct_colors
-- Round 95 chained universal triples.
#print axioms RadoNumbers.rado_self_loop_chain_6k_9k
#print axioms RadoNumbers.rado_self_loop_chain_8k_12k
-- Round 96 applied constraints at k=3, k=4.
#print axioms RadoNumbers.rado_k3_chain_universal
#print axioms RadoNumbers.rado_k4_chain_universal
-- Round 97 Foundational.lean universal lemmas for arbitrary b.
#print axioms RadoNumbers.self_loop_eq_left
#print axioms RadoNumbers.self_loop_eq_right
#print axioms RadoNumbers.self_loop_pair_constraint
#print axioms RadoNumbers.self_loop_b3_eq_left
#print axioms RadoNumbers.self_loop_b3_eq_right
#print axioms RadoNumbers.distance_pair_forbidden
#print axioms RadoNumbers.b3_triple_pair_distinct
#print axioms RadoNumbers.isRadoTriple_iff_canonical
#print axioms RadoNumbers.rado_triple_not_all_eq
#print axioms RadoNumbers.b3_universal_self_loops
#print axioms RadoNumbers.b3_universal_complementary_self_loops
#print axioms RadoNumbers.color_class_rado_free
#print axioms RadoNumbers.color_forced_right
#print axioms RadoNumbers.color_forced_left
#print axioms RadoNumbers.color_forced_multiple
-- Round 101 VALUATION COLORING SATURATION.
#print axioms RadoNumbers.valuation_coloring_saturates
#print axioms RadoNumbers.valuation_coloring_not_avoids_at_b_pow_k
#print axioms RadoNumbers.rado_triple_2bm_constraint
#print axioms RadoNumbers.valuation_witnesses_boundary
#print axioms RadoNumbers.subcoloring_at_multiples
#print axioms RadoNumbers.iterated_subcoloring_mono_free
-- Round 109 UNIQUENESS theorem.
#print axioms RadoNumbers.b3_k2_uniqueness
-- Round 110 b=4, k=2 multiples-agree.
#print axioms RadoNumbers.b4_k2_multiples_agree
-- Round 111 b=5, k=2 multiples-agree.
#print axioms RadoNumbers.b5_k2_multiples_agree
-- Round 112 R_2(3) = 9 via uniqueness + saturation (analytic closure).
#print axioms RadoNumbers.R2_3_upper_via_uniqueness
#print axioms RadoNumbers.R2_3_eq_9
-- Round 113 R_2(4) = 16 via uniqueness + saturation (analytic closure).
#print axioms RadoNumbers.R2_4_upper_via_uniqueness
#print axioms RadoNumbers.R2_4_eq_16
-- Round 114 R_2(5) = 25 via uniqueness + saturation (analytic closure).
#print axioms RadoNumbers.R2_5_upper_via_uniqueness
#print axioms RadoNumbers.R2_5_eq_25
-- Round 115 universal χ(2b) = χ(b) for k=2 (independent of b).
#print axioms RadoNumbers.k2_chi_2b_eq_chi_b
-- Round 116 universal χ((b-1)b) = χ(b) for k=2 (independent of b).
#print axioms RadoNumbers.k2_chi_bm1_b_eq_chi_b
-- Round 117 UNIVERSAL R_2(b) = b^2 for b ≥ 3 via blueprint.
#print axioms RadoNumbers.R2_b_upper_via_uniqueness
#print axioms RadoNumbers.R2_b_eq_b_sq
-- Round 118 FULLY UNIVERSAL R_2(b) = b^2 for b ≥ 2 via blueprint.
#print axioms RadoNumbers.R2_b_eq_b_sq_all
-- Round 119 BREAKDOWN at (b,k)=(2,3): R_3(2) > 8 via explicit 3-coloring.
#print axioms RadoNumbers.r3_2_witness_valid
#print axioms RadoNumbers.r3_2_witness_avoids
#print axioms RadoNumbers.thm_r3_2_breakdown
-- Round 120 BREAKDOWN at (b,k)=(2,4): R_4(2) > 16 via explicit 4-coloring.
#print axioms RadoNumbers.r4_2_witness_valid
#print axioms RadoNumbers.r4_2_witness_avoids
#print axioms RadoNumbers.thm_r4_2_breakdown
-- Round 121 BREAKDOWN at (b,k)=(2,5): R_5(2) > 32 via explicit 5-coloring.
#print axioms RadoNumbers.r5_2_witness_valid
#print axioms RadoNumbers.r5_2_witness_avoids
#print axioms RadoNumbers.thm_r5_2_breakdown
-- Round 122 BREAKDOWN at (b,k)=(2,6): R_6(2) > 64 via explicit 6-coloring.
#print axioms RadoNumbers.r6_2_witness_valid
#print axioms RadoNumbers.r6_2_witness_avoids
#print axioms RadoNumbers.thm_r6_2_breakdown
-- Round 123 BREAKDOWN at (b,k)=(2,7): R_7(2) > 128 via explicit 7-coloring.
#print axioms RadoNumbers.r7_2_witness_valid
#print axioms RadoNumbers.r7_2_witness_avoids
#print axioms RadoNumbers.thm_r7_2_breakdown
-- Round 124 BREAKDOWN at (b,k)=(2,8): R_8(2) > 256 via explicit 8-coloring.
#print axioms RadoNumbers.r8_2_witness_valid
#print axioms RadoNumbers.r8_2_witness_avoids
#print axioms RadoNumbers.thm_r8_2_breakdown
-- Round 126 STRONGER R_3(2) > 9 via non-block-and-echo 3-coloring.
#print axioms RadoNumbers.r3_2_witness_strong_valid
#print axioms RadoNumbers.r3_2_witness_strong_avoids
#print axioms RadoNumbers.thm_r3_2_breakdown_strong
#print axioms RadoNumbers.threshold_b2_k3_breaks_strong
-- Round 127 ABSTRACT block-and-echo recursive definition (universal scaffold).
#print axioms RadoNumbers.blockEchoWitness
#print axioms RadoNumbers.blockEchoWitness_3_eq
-- Round 128 MULTIPLICATIVE-SHIFT framework (algebraic-dynamical lens).
#print axioms RadoNumbers.HasMultShift
#print axioms RadoNumbers.valuationColoring
#print axioms RadoNumbers.valuationColoring_has_shift_one
#print axioms RadoNumbers.c_zero_excluded_b3_k2
-- Round 129 c=0 exclusion at (b, k) = (4, 2).
#print axioms RadoNumbers.c_zero_excluded_b4_k2
-- Round 130 UNIVERSAL c=0 exclusion at k=2, b ≥ 4.
#print axioms RadoNumbers.c_zero_excluded_k2_universal
-- Round 131 UNIFIED c=0 exclusion at k=2, b ≥ 3 (combines b=3 and b ≥ 4 cases).
#print axioms RadoNumbers.c_zero_excluded_k2_b_ge_3
-- Round 132 FIRST k=3 result: c=0 exclusion at (3, 3), Case A (χ(2) = χ(4)).
#print axioms RadoNumbers.c_zero_excluded_b3_k3_caseA
-- Round 133 k=3 Case B at (3, 3) with χ(2)=1, χ(4)=2: both sub-cases excluded.
#print axioms RadoNumbers.c_zero_excluded_b3_k3_caseB_12
-- Round 134 k=3 Case B at (3, 3) with χ(2)=2, χ(4)=1: both sub-cases excluded.
#print axioms RadoNumbers.c_zero_excluded_b3_k3_caseB_21
-- Round 135 FULL c=0 exclusion at (3, 3) — combines Rounds 132/133/134.
#print axioms RadoNumbers.c_zero_excluded_b3_k3
-- Round 136 saturation under HasMultShift c=1: triple (27, 1, 10) mono.
#print axioms RadoNumbers.shift_c_one_saturates_at_27
-- Round 137 saturation under HasMultShift c=2: symmetric to c=1.
#print axioms RadoNumbers.shift_c_two_saturates_at_27
-- Round 138 CONDITIONAL R_3(3) ≤ 27 under structural-uniqueness hypotheses.
#print axioms RadoNumbers.R_3_3_le_27_conditional
-- Round 139 STRUCTURAL: under HasMultShift c=1 + χ(1)=0, χ(2)=2 leads to contradiction.
#print axioms RadoNumbers.shift_c_one_forces_chi_2_zero
-- Round 140 STRUCTURAL: under HasMultShift c=1 + χ(1)=χ(2)=0, χ(4)=2 leads to contradiction.
#print axioms RadoNumbers.shift_c_one_forces_chi_4_zero
-- Round 141 STRUCTURAL: under HasMultShift c=1 + χ(1)=χ(2)=χ(4)=0, χ(5)=2 leads to contradiction.
#print axioms RadoNumbers.shift_c_one_forces_chi_5_zero
-- Round 142 STRUCTURAL: χ(7)=0 forced (under chi(1..5 reps)=0).
#print axioms RadoNumbers.shift_c_one_forces_chi_7_zero
-- Round 143 STRUCTURAL: χ(8)=0 forced (under chi(1..7 reps)=0).
#print axioms RadoNumbers.shift_c_one_forces_chi_8_zero
-- Round 144 MAJOR: R_3(3) ≤ 27 under HasMultShift c=1 + χ(1)=0.
-- Combines Rounds 139-143 + chi(10) impossibility cascade.
-- First analytic closure of R_3(3) ≤ 27 modulo only HasMultShift existence (Pillar 3).
#print axioms RadoNumbers.R_3_3_le_27_under_shift_c_one
-- Round 145 c=2 case via color permutation swap (1 ↔ 2).
#print axioms RadoNumbers.R_3_3_le_27_under_shift_c_two
#print axioms RadoNumbers.swapColors_12_injective
#print axioms RadoNumbers.swap_converts_shift_2_to_1
-- Round 146 UNIFIED: R_3(3) ≤ 27 under HasMultShift (any c) + χ(1)=0.
-- Combines Rounds 135, 144, 145. Last theorem before Pillar 3.
#print axioms RadoNumbers.R_3_3_le_27_under_HasMultShift

-- ============================================================
-- STRUCTURAL PIVOT: replace case enumeration with structural lemmas in
-- Pillar3Structural.lean.
-- ============================================================
-- Structural framework: localShift_3 χ m = unique c ∈ {0,1,2} with chi(3m) = (chi(m)+c) mod 3.
#print axioms RadoNumbers.localShift_3_spec
#print axioms RadoNumbers.localShift_3_lt_3
#print axioms RadoNumbers.self_loop_chi_2m_ne_chi_3m
#print axioms RadoNumbers.hasMultShift_iff_localShift_constant
#print axioms RadoNumbers.localShift_3_at_one
#print axioms RadoNumbers.hasMultShift_unique
-- Reduces R_3(3) ≤ 27 to proving IsLocalShiftConstant for any mono-free chi.
#print axioms RadoNumbers.IsLocalShiftConstant
#print axioms RadoNumbers.R_3_3_le_27_under_localShift_constant

-- ============================================================
-- GENERAL Rado partition regularity infrastructure (long-term Mathlib).
-- Definitions for arbitrary linear equations over ℤ (not specific to x+by=bz).
-- Foundation for eventual Rado theorem formalization.
-- ============================================================
#print axioms RadoNumbers.General.LinearEquation.eval
-- EVAL LINEARITY (foundational structural lemma for ANY LinearEquation).
#print axioms RadoNumbers.General.LinearEquation.eval_const_mul
#print axioms RadoNumbers.General.LinearEquation.isSolution_const_mul
#print axioms RadoNumbers.General.LinearEquation.isPositiveSolution_const_mul
-- EVAL ADDITIVITY (the other linearity property + solution closure).
#print axioms RadoNumbers.General.LinearEquation.eval_add
#print axioms RadoNumbers.General.LinearEquation.isSolution_add
#print axioms RadoNumbers.General.IsKColoring
#print axioms RadoNumbers.General.HasMonoSolution
#print axioms RadoNumbers.General.IsKPartitionRegular
#print axioms RadoNumbers.General.IsRadoNumber
#print axioms RadoNumbers.General.isRadoNumber_unique
-- Specific b-adic equation: x + b·y - b·z = 0.
#print axioms RadoNumbers.General.bAdicEquation
#print axioms RadoNumbers.General.radoEq_3
#print axioms RadoNumbers.General.radoEq_3_coeffs
#print axioms RadoNumbers.General.eval_radoEq_3
#print axioms RadoNumbers.General.eval_bAdicEquation
-- Canonical positive solution (b, 1, 2) for bAdicEquation b.
#print axioms RadoNumbers.General.bAdicEquation_hasPositiveSolution
#print axioms RadoNumbers.General.bAdicEquation_exists_positive_solution
-- Schur equation = bAdicEquation 1 = (x + y - z = 0).
#print axioms RadoNumbers.General.schurEquation
#print axioms RadoNumbers.General.schurEquation_hasPositiveSolution
#print axioms RadoNumbers.General.schurEquation_numVars
#print axioms RadoNumbers.General.eval_schurEquation
-- bAdicVal in General/: foundation for valuation coloring lower bound.
#print axioms RadoNumbers.General.bAdicVal
#print axioms RadoNumbers.General.bAdicVal_zero
#print axioms RadoNumbers.General.bAdicVal_lt_two
#print axioms RadoNumbers.General.bAdicVal_not_dvd
#print axioms RadoNumbers.General.bAdicVal_step
#print axioms RadoNumbers.General.bAdicVal_b_mul
#print axioms RadoNumbers.General.bAdicVal_b_pow
#print axioms RadoNumbers.General.bAdicVal_one
#print axioms RadoNumbers.General.bAdicVal_b_value
#print axioms RadoNumbers.General.b_pow_dvd_of_bAdicVal_ge
#print axioms RadoNumbers.General.bAdicVal_lt_pow
-- VALUATION COLORING in General/ (canonical mono-free k-coloring).
#print axioms RadoNumbers.General.valuationColoring
#print axioms RadoNumbers.General.valuationColoring_lt
#print axioms RadoNumbers.General.isKColoring_valuationColoring
#print axioms RadoNumbers.General.valuationColoring_eq_bAdicVal
#print axioms RadoNumbers.General.bAdicVal_ge_of_b_pow_dvd
#print axioms RadoNumbers.General.bAdicVal_sub_ge
-- VALUATION COLORING MONO-FREE: kernel-pure lower bound foundation!
#print axioms RadoNumbers.General.valuationColoring_mono_free
-- KERNEL-PURE LOWER BOUND R_k(b) ≥ b^k from scratch (eliminates project bridge!).
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one_from_scratch
-- THRESHOLD EQUIVALENCE from scratch: R_k(b) = b^k iff IsKPartitionRegularAt at b^k.
#print axioms RadoNumbers.General.isRadoNumber_iff_isKPartitionRegularAt_from_scratch
-- R_3(3) = 27 reduction FROM SCRATCH (replaces project-bridge version).
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_iff_pillar3_from_scratch
-- R_3(3) = 27 from hypotheses FROM SCRATCH (sharpest kernel-pure open statement).
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_from_hypotheses_from_scratch
-- Bridge: general HasMonoSolution ↔ project HasMonoSolution.
#print axioms RadoNumbers.General.hasMonoSolution_bAdicEquation_to_project
#print axioms RadoNumbers.General.hasMonoSolution_bAdicEquation_from_project
#print axioms RadoNumbers.General.hasMonoSolution_bAdicEquation_iff

-- ColumnsCondition (single-equation Rado's condition; full theorem TBD).
#print axioms RadoNumbers.General.HasZeroSumSubset
#print axioms RadoNumbers.General.ColumnsCondition
#print axioms RadoNumbers.General.bAdicEquation_columnsCondition
#print axioms RadoNumbers.General.radoEq_3_columnsCondition
-- Basic results: trivial directions of Rado-type theorems.
#print axioms RadoNumbers.General.isKPartitionRegularAt_one_of_hasPosSolution
#print axioms RadoNumbers.General.isKPartitionRegularAt_mono
#print axioms RadoNumbers.General.isKPartitionRegular_iff_eventually
#print axioms RadoNumbers.General.isRadoNumber_of_bounds
#print axioms RadoNumbers.General.isKPartitionRegular_hasPosSolution
-- Monotonicity in k + trivial b-adic lower bound (no valuation theory).
#print axioms RadoNumbers.General.isKPartitionRegularAt_mono_colors
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_at_b_minus_one
-- IsKPartitionRegular k-monotonicity + HasMono N-monotonicity + R_k ≤ R_{k+1}.
#print axioms RadoNumbers.General.isKPartitionRegular_mono_colors
#print axioms RadoNumbers.General.hasMonoSolution_mono
#print axioms RadoNumbers.General.isRadoNumber_le_succ_colors
-- MULTIPLES SUB-COLORING: GENERAL for ANY LinearEquation (kernel-pure).
#print axioms RadoNumbers.General.multiples_subcoloring_mono_free
#print axioms RadoNumbers.General.bAdicEquation_isPositiveSolution_scale
#print axioms RadoNumbers.General.bAdicEquation_multiples_subcoloring_mono_free
#print axioms RadoNumbers.General.isKColoring_multiples_subcoloring
-- SELF-LOOP STRUCTURAL CONSTRAINT: chi((b-1)·m) ≠ chi(b·m) for mono-free chi.
#print axioms RadoNumbers.General.bAdicEquation_self_loop_chi_diff
-- CANONICAL-TRIPLE CONSTRAINT (general form) + conditional alternation.
#print axioms RadoNumbers.General.bAdicEquation_canonical_triple_constraint
#print axioms RadoNumbers.General.bAdicEquation_canonical_triple_conditional_alternation
-- b=3 specialization: chi(2m) ≠ chi(3m) for m ∈ [1, n/3] + base case chi(2) ≠ chi(3).
#print axioms RadoNumbers.General.bAdicEquation_3_self_loop_chain
#print axioms RadoNumbers.General.bAdicEquation_3_base_chi_constraint
-- Pillar 3 building blocks: (3, 1, 2) triple constraints.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_1_2_3_not_all_equal
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_ne_zero_when_chi_1_2_eq_zero
-- First-3 multiples-of-3 structural constraints.
#print axioms RadoNumbers.General.bAdicEquation_3_not_all_same_at_3_6_9
#print axioms RadoNumbers.General.bAdicEquation_3_not_all_chi_1_at_3_6_9
#print axioms RadoNumbers.General.bAdicEquation_3_not_all_same_at_9_15_18
#print axioms RadoNumbers.General.bAdicEquation_3_not_all_same_at_3j_6j_9j
-- Conditional chi determination via canonical-triple constraint.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_6_ne_when_chi_2_4_eq
#print axioms RadoNumbers.General.bAdicEquation_3_chi_12_ne_when_chi_4_8_eq
#print axioms RadoNumbers.General.bAdicEquation_chi_bm_ne_when_chi_m_2m_eq
-- General Rado constraint convenient forms.
#print axioms RadoNumbers.General.bAdicEquation_chi_yd_ne_when_chi_bd_y_eq
#print axioms RadoNumbers.General.bAdicEquation_chi_bd_ne_when_chi_y_yd_eq
-- WLOG sub-case structure: trichotomy for (chi(1), chi(2), chi(3)) under chi(1) = 0.
#print axioms RadoNumbers.General.mono_free_3_coloring_chi_1_zero_sub_cases
-- Multi-value forcing: chi(1) = chi(2) = chi(4) = 0 forces {chi(6), chi(9)} = {1, 2}.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_6_9_forced_when_chi_1_2_4_eq_zero
#print axioms RadoNumbers.General.bAdicEquation_3_chi_5_7_forced_when_chi_3_6_eq_1
-- Multiples-of-3 nonzero forcings via pair equalities.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3d_ne_when_chi_y_yd_eq
#print axioms RadoNumbers.General.bAdicEquation_3_chi_12_ne_zero_when_chi_1_5_eq_zero
#print axioms RadoNumbers.General.bAdicEquation_3_chi_15_ne_zero_when_chi_1_6_eq_zero
#print axioms RadoNumbers.General.bAdicEquation_3_chi_18_ne_zero_when_chi_1_7_eq_zero
-- GENERAL chi-forcing principle: chi(y) = 0 → chi(3·(y-1)) ≠ 0 (under chi(1) = 0).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_y_minus_1_ne_zero_when_chi_y_eq_zero
-- MOST GENERAL chi-forcing: chi(y) = chi(y') → chi(3·(y'-y)) ≠ chi(y).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_diff_ne_when_chi_y_y'_eq
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_diff_ne_zero_when_chi_y_y'_eq_zero
-- SUB-CASE A.1 7-fold partial closure: 7 of 8 multiples-of-3 ≠ 0 (chi(24) excluded).
#print axioms RadoNumbers.General.bAdicEquation_3_partial_pillar3_A1
#print axioms RadoNumbers.General.bAdicEquation_3_full_pillar3_A1_with_chi_10_eq_zero
#print axioms RadoNumbers.General.bAdicEquation_3_full_pillar3_A1_with_chi_13_eq_zero
#print axioms RadoNumbers.General.bAdicEquation_3_full_pillar3_A1_with_chi_16_eq_zero
-- UNIFIED disjunctive sub-case A.1 closure.
#print axioms RadoNumbers.General.bAdicEquation_3_full_pillar3_A1_unified
-- Second self-loop family (x = y form): chi(b·m) ≠ chi((b+1)·m).
#print axioms RadoNumbers.General.bAdicEquation_self_loop_xy_chi_diff
#print axioms RadoNumbers.General.bAdicEquation_3_self_loop_xy_chain
-- CompressionHyp 3 2 DERIVED FROM SCRATCH using structural lemmas (kernel-pure).
#print axioms RadoNumbers.General.compressionHyp_3_2_from_scratch
-- GENERAL 2-parameter Rado triple constraint (max-generality structural lemma).
#print axioms RadoNumbers.General.bAdicEquation_general_rado_constraint
-- COLOR CLASS definitions (Finset-based, for pigeonhole arguments).
#print axioms RadoNumbers.General.colorClass
#print axioms RadoNumbers.General.colorClass_subset
#print axioms RadoNumbers.General.mem_colorClass
-- COLOR CLASS PIGEONHOLE: sum = n + pigeonhole (basic + ceiling form).
#print axioms RadoNumbers.General.sum_colorClass_card
#print axioms RadoNumbers.General.colorClass_pigeonhole
#print axioms RadoNumbers.General.colorClass_pigeonhole_ceil
-- BUNDLED multiples sub-coloring: combined IsKColoring + mono-free.
#print axioms RadoNumbers.General.multiples_subcoloring_bundled
-- ITERATED MULTIPLES SUB-COLORING: foundational cascade recursion.
#print axioms RadoNumbers.General.multiples_subcoloring_mono_free_iter
#print axioms RadoNumbers.General.bAdicEquation_iter_multiples_subcoloring
-- CASCADE STEP general bridge: connects multiples sub-coloring to partition regularity.
#print axioms RadoNumbers.General.cascade_step_general
#print axioms RadoNumbers.General.cascade_step_contrapositive
-- WLOG normalization via swap permutation: chi(1) = 0 by color permutation.
#print axioms RadoNumbers.General.swap_perm
#print axioms RadoNumbers.General.swap_perm_injective
#print axioms RadoNumbers.General.swap_perm_lt
#print axioms RadoNumbers.General.swap_perm_left
#print axioms RadoNumbers.General.WLOG_chi_one_eq_zero
-- Second-level self-loop: chi((b-1)·b·m) ≠ chi(b·b·m) via multiples sub-coloring.
#print axioms RadoNumbers.General.bAdicEquation_second_level_self_loop
-- R_2(2) ≤ 4 DERIVED FROM SCRATCH in General/ (no project bridge, kernel-pure).
#print axioms RadoNumbers.General.isKPartitionRegularAt_bAdicEquation_2_2_4_from_scratch
-- R_2(3) ≤ 9 DERIVED FROM SCRATCH in General/ (no project bridge, kernel-pure).
#print axioms RadoNumbers.General.isKPartitionRegularAt_bAdicEquation_3_2_9_from_scratch
-- R_2(4) ≤ 16 DERIVED FROM SCRATCH in General/ (validates pattern at b=4).
#print axioms RadoNumbers.General.isKPartitionRegularAt_bAdicEquation_4_2_16_from_scratch
-- COLOR PERMUTATION INVARIANCE: WLOG infrastructure for mono-free colorings.
#print axioms RadoNumbers.General.hasMonoSolution_comp_inj
#print axioms RadoNumbers.General.hasMonoSolution_comp_equiv
#print axioms RadoNumbers.General.isKColoring_comp
#print axioms RadoNumbers.General.mono_free_coloring_comp_inj
-- Bridge: project lower bound → general "not partition regular at N-1".
#print axioms RadoNumbers.General.isValidColoring_eq_isKColoring
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_of_radoNumberAtLeast
-- Full equivalence: general IsKPartitionRegularAt ↔ project "no mono-free coloring".
#print axioms RadoNumbers.General.isKPartitionRegularAt_bAdicEquation_iff
-- GENERAL LOWER BOUND: R_b(k) ≥ b^k for any b≥2, k≥1 (via valuation coloring).
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_at_pow_minus_one
-- Specific corollary: R_3(3) ≥ 27 in general framework.
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_radoEq_3_at_26
-- R_3(3) = 27 reduces to upper bound (Pillar 3) alone, lower bound already done.
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_iff_pillar3
-- CONDITIONAL FINAL: assuming Pillar 3, R_3(3) = 27 exactly.
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_from_pillar3
-- Concrete instance: R_1(b) = b for b ≥ 2 (UNCONDITIONAL).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_one
-- Concrete instance: R_2(2) = 4 (b=2, k=2 threshold conjecture verified).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_two
-- Concrete instance: R_2(3) = 9 (b=3, k=2 threshold conjecture verified).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_three
-- Bridge: general IsRadoNumber → project IsRadoNumber.
#print axioms RadoNumbers.General.radoNumberAtMost_iff_isKPartitionRegularAt
#print axioms RadoNumbers.General.isRadoNumber_project_of_general
-- PROJECT-LEVEL Rado number corollaries (R_1(b) = b, R_2(2) = 4, R_2(3) = 9).
#print axioms RadoNumbers.General.isRadoNumber_project_one
#print axioms RadoNumbers.General.isRadoNumber_project_two_two
#print axioms RadoNumbers.General.isRadoNumber_project_two_three
-- REVERSE BRIDGE: project IsRadoNumber → general IsRadoNumber.
#print axioms RadoNumbers.General.isRadoNumber_general_of_project
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_iff_project
-- UNIVERSAL R_2(b) = b^2 in general framework (via bridge from project).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_universal
-- R_3(3) = 27 in general framework (conditional on lem_compress3_general).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_three
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_three_27
-- R_4(3) = 81 in general framework (conditional on lem_gstartree).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_four_three
-- R_1(3) = 3 (specialization of R_1(b) = b).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_one
-- SAT-verified R_k(b) = b^k for the verified set (k=3, 3 ≤ b ≤ 10;
-- k=4, 3 ≤ b ≤ 5) (depends on lem_keypair_sat).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_sat_range
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_four
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_five
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_four_four
-- BREAKDOWN: R_k(2) > 2^k for k ∈ {3..8} in general framework.
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_three_at_eight
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_four_at_sixteen
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_five_at_thirtytwo
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_six_at_sixtyfour
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_seven_at_onetwoeight
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_eight_at_twofivesix
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_two_three_at_nine
-- Breakdown at b=3: R_5(3) > 243 (lem_keypair_sat / r5_witness_valid_sat)
--                    R_5(3) > 296 (r5_296_sat).
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_three_five_at_243
#print axioms RadoNumbers.General.not_isKPartitionRegularAt_bAdicEquation_three_five_at_296
-- Threshold DICHOTOMY statement (Prop) + dichotomy → conjecture implication.
#print axioms RadoNumbers.General.ThresholdDichotomy
#print axioms RadoNumbers.General.thresholdConjecture_of_dichotomy
-- THRESHOLD CONJECTURE PROVEN UNCONDITIONALLY FOR k ≤ 2 (kernel-pure).
#print axioms RadoNumbers.General.thresholdConjecture_holds_for_k_le_2
-- R_3(3) = 27 from ThresholdDichotomy (convenient corollary).
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_from_dichotomy
-- Cascade compression iff R_k(b) ≤ b^k (modulo R_{k-1}(b) ≤ b^{k-1}).
#print axioms RadoNumbers.General.cascadeCompression_iff_isKPartitionRegularAt
-- Per-level k=2 cascade hypotheses CLOSED UNCONDITIONALLY (kernel-pure).
#print axioms RadoNumbers.General.compressionHyp_unconditional_k2
#print axioms RadoNumbers.General.omittedPairHyp_unconditional_k2
#print axioms RadoNumbers.General.compressionAndOmittedPair_k2
-- R_2(b) = b^2 via CASCADE route (end-to-end demonstration of architecture).
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_via_cascade
-- R_3(3) = 27 KERNEL-PURE conditional on CompressionHyp 3 3 + OmittedPairHyp 3 3.
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_three_27_from_hypotheses
-- CONDITIONAL THRESHOLD: R_k(b) = b^k conditional on CompressionHyp/OmittedPairHyp.
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_threshold_conditional
-- PILLAR 3 reduction: HasMonoSolution from IsLocalShiftConstant + chi(1)=0.
#print axioms RadoNumbers.General.hasMonoSolution_bAdicEquation_three_27_under_localShift_constant
-- Mono-free structural constraint: canonical triple (b·m, m, 2m).
#print axioms RadoNumbers.General.chi_constraint_canonical_triple_of_no_mono
-- Explicit k=2 corollaries: R_2(4) = 16, R_2(5) = 25, R_2(10) = 100.
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_four
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_five
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_two_ten
-- Explicit k=3 corollaries: R_3(6) = 216, R_3(7) = 343, R_3(10) = 1000.
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_six
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_seven
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_three_ten
-- THRESHOLD CONJECTURE statement (real math, not := True trick).
#print axioms RadoNumbers.General.ThresholdConjecture
#print axioms RadoNumbers.General.isRadoNumber_radoEq_3_27_from_thresholdConjecture
#print axioms RadoNumbers.General.thresholdConjecture_3_3_iff_pillar3
#print axioms RadoNumbers.compression_3_3_4_2_2_A1_3_12_A2_9_18_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_1_A1_3_6_9_A2_18_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_1_A1_3_9_15_A2_18_infeasible
-- Round 109 (R406): 7+1+1 distribution, color-0 majority, both sub-cases + master.
#print axioms RadoNumbers.compression_3_3_7_1_1_case_0major_9eq1_18eq2
#print axioms RadoNumbers.compression_3_3_7_1_1_case_0major_9eq2_18eq1
#print axioms RadoNumbers.compression_3_3_7_1_1_color0_majority_infeasible
-- Round 109 (R407): parametric core lemma + color-1/color-2/any-majority wrappers.
#print axioms RadoNumbers.compression_3_3_7_1_1_majority_core_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_color1_majority_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_color2_majority_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_any_majority_infeasible
-- Round 110 (R408): structural pair-omission closure for 7+1+1 (any (p, q)).
#print axioms RadoNumbers.compression_3_3_7_1_1_omission_pair_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_pair_omission_structural_infeasible
-- Round 111 (R409): cardinality lift — extraction lemma + card7 infeasibility + color wrappers.
#print axioms RadoNumbers.layer3_card7_filter_exists_two_omitted
#print axioms RadoNumbers.compression_3_3_7_1_1_card7_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_color0_card7_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_color1_card7_infeasible
#print axioms RadoNumbers.compression_3_3_7_1_1_color2_card7_infeasible
-- Round 112 (R410): partition-shape audit + 6+2+1 partial closure (χ(18) = majority case).
#print axioms RadoNumbers.compression_3_3_card6_chi18_eq_majority_infeasible
-- Round 113 (R411): 6+2+1 cardinality closure — χ(9), χ(27) anchors + dispatcher.
#print axioms RadoNumbers.compression_3_3_card6_chi9_eq_majority_infeasible
#print axioms RadoNumbers.compression_3_3_card6_chi27_eq_majority_infeasible
#print axioms RadoNumbers.compression_3_3_card6_anchor_at_9_18_27_infeasible
-- Round 114 (R412): 6+2+1 off-layer survivor closure (A + B + dispatcher).
#print axioms RadoNumbers.compression_3_3_6_2_1_survivorA_infeasible
#print axioms RadoNumbers.compression_3_3_6_2_1_survivorB_infeasible
#print axioms RadoNumbers.compression_3_3_6_2_1_survivors_infeasible
-- Round 115 (R413): 6+2+1 cardinality master + color wrappers.
#print axioms RadoNumbers.compression_3_3_6_2_1_card6_infeasible
#print axioms RadoNumbers.compression_3_3_6_2_1_color0_card6_infeasible
#print axioms RadoNumbers.compression_3_3_6_2_1_color1_card6_infeasible
#print axioms RadoNumbers.compression_3_3_6_2_1_color2_card6_infeasible
-- Round 115β (R415β): 5+3+1 survivor closures (4 + dispatcher).
#print axioms RadoNumbers.compression_3_3_5_3_1_survivorA_infeasible
#print axioms RadoNumbers.compression_3_3_5_3_1_survivorB_infeasible
#print axioms RadoNumbers.compression_3_3_5_3_1_survivorC_infeasible
#print axioms RadoNumbers.compression_3_3_5_3_1_survivorD_infeasible
#print axioms RadoNumbers.compression_3_3_5_3_1_survivors_infeasible
-- Round 115γ (R415γ): 4+4+1 survivor closures (4 + dispatcher).
#print axioms RadoNumbers.compression_3_3_4_4_1_survivorA_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_survivorB_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_survivorC_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_survivorD_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_survivors_infeasible
-- Round 116δ (R416δ): shared layer cardinality helpers (layer3, layerCount + card1/card2 extract).
#print axioms RadoNumbers.layer3_card1_extract
#print axioms RadoNumbers.layer3_card2_extract
-- Round 117δ (R417δ): extended cardinality extracts (card3, card4, card5 complement).
#print axioms RadoNumbers.layer3_card3_extract
#print axioms RadoNumbers.layer3_card4_extract
#print axioms RadoNumbers.layer3_card5_complement_extract
-- Round 118α (R418α): generic helper for χ(18) = c with layerCount c = 5.
#print axioms RadoNumbers.layer3_card5_chi18_eq_color_infeasible
-- Round 119δ (R419δ): layer3 color bound helpers.
#print axioms RadoNumbers.layer3_chi_lt_3
#print axioms RadoNumbers.layer3_color_lt_3_of_card_pos
-- Round 120 (R420): layer3_card3_classify uniqueness helper.
#print axioms RadoNumbers.layer3_card3_classify
-- Round 121 (R421): layer3_card3_two_known_force_third completion helper +
-- 5+3+1 singleton-18 pattern dispatch master.
#print axioms RadoNumbers.layer3_card3_two_known_force_third
#print axioms RadoNumbers.compression_3_3_5_3_1_singleton18_pattern_dispatch
-- Round 122 (R422): 5+3+1 singleton p≠18 closure + cardinality master.
#print axioms RadoNumbers.compression_3_3_5_3_1_singleton_not18_infeasible
#print axioms RadoNumbers.compression_3_3_5_3_1_card_distribution_infeasible
-- Round 123 (R423): 4+4+1 card4_classify helper + cardinality master.
#print axioms RadoNumbers.layer3_card4_classify
#print axioms RadoNumbers.compression_3_3_4_4_1_singleton18_pattern_dispatch_main
#print axioms RadoNumbers.compression_3_3_4_4_1_singleton18_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_4_4_1_singleton_not18_infeasible_main
#print axioms RadoNumbers.compression_3_3_4_4_1_singleton_not18_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_card_distribution_infeasible
-- Round 124α (R424α): 5+2+2 cardinality-aware survivor dispatcher wrapper.
#print axioms RadoNumbers.compression_3_3_5_2_2_pattern_dispatch_infeasible
-- Round 125 (R425): 5+2+2 χ(18) = c0 kill (Part 1 of 5+2+2 cardinality master).
-- Parts 2-4 closed by R426 (swap-aware dispatcher + helper) and R427 (χ(18)=c1/c2 dispatchers + master).
#print axioms RadoNumbers.compression_3_3_5_2_2_chi18_eq_c0_infeasible
-- Round 126 (R426): 5+2+2 swap-aware pattern dispatcher + layer3_card2_classify helper.
#print axioms RadoNumbers.layer3_card2_classify
#print axioms RadoNumbers.compression_3_3_5_2_2_pattern_dispatch_or_swap_infeasible
-- Round 127 (R427): 5+2+2 χ(18)=c1 and c2 dispatch + cardinality master.
#print axioms RadoNumbers.compression_3_3_5_2_2_chi18_eq_c1_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_5_2_2_chi18_eq_c2_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_5_2_2_card_distribution_infeasible
-- Round 128 (R428): 3+3+3 survivor-level infrastructure (13 survivors + dispatcher + S₃ test).
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor1_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor2_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor3_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor4_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor5_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor6_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor7_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor8_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor9_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor10_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor11_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor12_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor13_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivor1_swap01_infeasible
#print axioms RadoNumbers.compression_3_3_3_3_3_survivors_infeasible
-- Round 129 (R429): 3+3+3 cardinality master, χ(18) = c₀ sub-tree, Phase 1.
-- KILL helper for the (χ(3) ≠ c₀, χ(6) ≠ c₀) case.  Remaining phases
-- (case_3_6, case_3_not6, case_not3_6, master) deferred to R430+.
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_c0_case_not3_not6
-- Round 130 (R430): 3+3+3 cardinality master, χ(18) = c₀ sub-tree, case (3, 6).
-- KILL helper for the (χ(3) = c₀, χ(6) = c₀) case via 20-leaf dispatch:
-- 8 self-loop leaves + 6 R428 survivor dispatches + 6 layer-internal mono leaves.
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_c0_case_3_6
-- Round 130 (R430): 3+3+3 cardinality master, χ(18) = c₀ sub-tree, case (3, ¬6).
-- KILL helper for the (χ(3) = c₀, χ(6) ≠ c₀) case via 4-leaf outer split on
-- (χ(15) = c₀, χ(21) = c₀): 2 cardinality-kill leaves + S11 sub-tree
-- (c₀ = {3, 15, 18}) + S12/S13 sub-tree (c₀ = {3, 18, 21}).  Closures via
-- R428 survivor dispatch (S11/S12/S13 identity + swap) with appropriate
-- (c₁ ↔ c₂) permutations and layer-internal mono triples
-- {(9, 6, 9), (9, 9, 12), (9, 21, 24), (9, 24, 27)}.
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_c0_case_3_not6
-- Round 130 (R430): 3+3+3 cardinality master, χ(18) = c₀ sub-tree,
-- case (¬3, 6) with c₀ = {6, 15, 18} sub-helper.  Locks c₀ via classify,
-- then 14-leaf dispatch over χ(9), χ(12), χ(3), χ(21), χ(24): 2 self-loop
-- (9, 9, 12) leaves + 6 R428 survivor dispatches (S5/S6/S9 × {swap, 3-cycle})
-- + 6 layer-internal mono leaves (T9 = (27, 12, 21), T14 = (9, 21, 24),
-- T16 = (9, 24, 27)).
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_c0_case_not3_6_c0_eq_6_15_18
-- Round 130 (R430): 3+3+3 cardinality master, χ(18) = c₀ sub-tree,
-- case (¬3, 6) with c₀ = {6, 18, 21} sub-helper.  Locks c₀ via classify,
-- then 16-leaf dispatch over χ(9), χ(12), χ(15), χ(24), χ(27): 2 self-loop
-- (9, 9, 12) leaves + 8 R428 survivor dispatches (S4/S7/S8/S10 × {swap, 3-cycle})
-- + 2 layer-internal mono leaves (T3 = (27, 3, 12), T16 = (9, 24, 27))
-- + 4 cardinality-kill leaves (all-c₁ or all-c₂ over {9 or 12, 15, 24, 27}).
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_c0_case_not3_6_c0_eq_6_18_21
-- Round 130 (R430): 3+3+3 cardinality master, χ(18) = c₀ pattern dispatch.
-- Combines the five case helpers above (case_not3_not6 / case_3_6 / case_3_not6 /
-- case_not3_6_c0_eq_6_15_18 / case_not3_6_c0_eq_6_18_21) via case-split on
-- (χ(3) =?= c₀, χ(6) =?= c₀, χ(15) =?= c₀, χ(21) =?= c₀).  In the (¬3, 6)
-- sub-tree, derives χ(9) ≠ c₀ from the (9, 6, 9) self-loop and closes the
-- (¬15, ¬21) and (15, 21) sub-branches via cardinality kill against
-- hCard0 = 3.
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_eq_c0_pattern_dispatch
-- Round 131 (R431): 3+3+3 cardinality master.  Two thin S₃ swap wrappers
-- (chi18_eq_c1, chi18_eq_c2) forwarding to R430's chi18_eq_c0 dispatch via
-- (c₀ ↔ c₁) and (c₀ ↔ c₂) substitutions, plus the top-level master via
-- χ(18) trichotomy.  This completes the 3+3+3 partition-shape closure.
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_eq_c1_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_3_3_3_chi18_eq_c2_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_3_3_3_card_distribution_infeasible
-- Round 133 (R433): 4+3+2 survivor theorem batch (56 survivor closures).
-- Each survivor closes via propagation chain + final mono_3.  Per-position color
-- derivations use `chi_in_3colors` trichotomy + `rcases` (instead of omega, which
-- scales O(N²) on hypothesis count and triggered Lean elaboration pathology in
-- the initial draft).
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor01_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor02_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor03_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor04_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor05_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor06_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor07_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor08_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor09_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor10_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor11_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor12_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor13_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor14_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor15_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor16_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor17_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor18_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor19_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor20_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor21_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor22_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor23_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor24_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor25_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor26_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor27_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor28_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor29_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor30_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor31_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor32_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor33_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor34_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor35_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor36_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor37_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor38_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor39_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor40_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor41_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor42_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor43_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor44_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor45_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor46_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor47_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor48_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor49_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor50_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor51_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor52_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor53_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor54_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor55_infeasible
#print axioms RadoNumbers.compression_3_3_4_3_2_survivor56_infeasible
-- Round 134 (R434): 4+3+2 survivor dispatcher (56-way disjunction → dispatch).
#print axioms RadoNumbers.compression_3_3_4_3_2_survivors_infeasible
-- Round 135 (R435): 4+3+2 cardinality master + 3 chi(18)-branch helpers.
#print axioms RadoNumbers.compression_3_3_4_3_2_chi18_eq_c0_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_4_3_2_chi18_eq_c1_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_4_3_2_chi18_eq_c2_pattern_dispatch
#print axioms RadoNumbers.compression_3_3_4_3_2_card_distribution_infeasible
-- Round 136 (R436): unified layer3 partition closure (Targets A/B/C).
-- Integrates the 7 shape masters (R409 + R413 + R422 + R423 + R427 + R431 + R435)
-- into a single kernel-pure theorem `compression_3_3_layer3_infeasible`.
#print axioms RadoNumbers.layer3_count_vector_ordered_classify
#print axioms RadoNumbers.layer3_count_sum_of_three_colors
#print axioms RadoNumbers.compression_3_3_layer3_infeasible
-- Round 116α/β (R416α/β): partial cardinality-aware survivor dispatchers (5+3+1, 4+4+1).
#print axioms RadoNumbers.compression_3_3_5_3_1_card_at_18_via_pattern_infeasible
#print axioms RadoNumbers.compression_3_3_4_4_1_card_at_18_via_pattern_infeasible
-- Round 115δ (R415δ): 5+2+2 survivor closures (12 + dispatcher).
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorA_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorB_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorC_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorD_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorE_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorF_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorG_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorH_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorI_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorJ_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorK_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivorL_infeasible
#print axioms RadoNumbers.compression_3_3_5_2_2_survivors_infeasible

-- Conjecture-supporting verified instances.
#print axioms RadoNumbers.threshold_b3_k4_boundary
#print axioms RadoNumbers.threshold_b3_k5_breaks
#print axioms RadoNumbers.threshold_b3_k5_breaks_strong
#print axioms RadoNumbers.threshold_k2
-- Rounds 119-124: breakdown direction at (b, k) = (2, k) for k ∈ {3,4,5,6,7,8}.
#print axioms RadoNumbers.threshold_b2_k3_breaks
#print axioms RadoNumbers.threshold_b2_k4_breaks
#print axioms RadoNumbers.threshold_b2_k5_breaks
#print axioms RadoNumbers.threshold_b2_k6_breaks
#print axioms RadoNumbers.threshold_b2_k7_breaks
#print axioms RadoNumbers.threshold_b2_k8_breaks
-- Round 125: cumulative b=2 breakdown summary across k ∈ {3..8}.
#print axioms RadoNumbers.b2_breakdown_cumulative

-- Rounds 200-208: structural attack on CompressionHyp 3 3 toward kernel-pure
-- closure. Each new lemma should depend only on {propext, Classical.choice, Quot.sound}.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_6_ne_chi_9
#print axioms RadoNumbers.General.bAdicEquation_3_chi_9_ne_chi_12
#print axioms RadoNumbers.General.bAdicEquation_3_chi_12_ne_chi_18
#print axioms RadoNumbers.General.bAdicEquation_3_chi_12_ne_chi_16
#print axioms RadoNumbers.General.bAdicEquation_3_five_chain_distinct
#print axioms RadoNumbers.General.bAdicEquation_3_chi_18_in_6_9_when_distinct
#print axioms RadoNumbers.General.bAdicEquation_3_chi_16_in_6_9_when_distinct
#print axioms RadoNumbers.General.bAdicEquation_3_rado_6_16_18
#print axioms RadoNumbers.General.bAdicEquation_3_no_chi_16_18_both_eq_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_16_18_eq_chi_9_when_16_eq_18
#print axioms RadoNumbers.General.bAdicEquation_3_chi_24_eq_chi_12_when_16_18_distinct
#print axioms RadoNumbers.General.bAdicEquation_3_chi_8_eq_9_in_sub4
#print axioms RadoNumbers.General.bAdicEquation_3_sub4_caseB_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_sub4_caseA_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_sub4_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_chi_19_impossible_in_sub4_caseA_AI

-- Rounds 209-213: sub-cases 2, 3, and the bundled '(6,9,12) all distinct'
-- branch closure (kernel-pure milestone).
#print axioms RadoNumbers.General.bAdicEquation_3_sub3_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_sub2_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_no_chi_6_9_12_all_distinct

-- Rounds 215-217: case Y (chi(6) = chi(12)) foundational toolkit, and the
-- MAIN result chi_6_eq_chi_12_in_monoFree (forces case Y for any mono-free chi).
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_ne_chi_6_bundle
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_24_eq_chi_6_when_chi_16_18_distinct
#print axioms RadoNumbers.General.bAdicEquation_3_chi_6_eq_chi_12_in_monoFree

-- Rounds 218-222: case Y main cascade + dichotomy + UNIFIED Branch (II) chi(10) = chi(24).
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_16_eq_18_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_10_eq_chi_24_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_2_ne_chi_24_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_2_eq_chi_18_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_8_eq_chi_24_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_chi_22_ne_chi_18_when_chi_24_ne_6
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_branch_II_skeleton

-- Round 230-231: FIRST FULL Branch (II) sub-case closure: II-V.
#print axioms RadoNumbers.General.bAdicEquation_3_branch_II_V_15_eq_18_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_branch_II_V_15_eq_6_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_branch_II_V_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_branch_II_W_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_case_Y_branch_II_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_chi_24_eq_chi_6_in_monoFree

-- Round 234-236: monoFree structure bundle + Branch (I) split + conditional R_3(3) closure.
#print axioms RadoNumbers.General.bAdicEquation_3_monoFree_structure
#print axioms RadoNumbers.General.bAdicEquation_3_no_monoFree_assuming_branch_I

-- Round 237 (§72): chi(27) Rado constraint infrastructure for n >= 27.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_ne_chi_18_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_rado_27_y_yp9_mono
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_ne_chi_9_when_chi_9_eq_chi_18
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_15_not_both_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_21_not_both_eq_chi_12
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_24_not_both_eq_chi_15
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_12_not_both_eq_chi_3
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_10_not_both_eq_chi_1
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_11_not_both_eq_chi_2
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_13_not_both_eq_chi_4
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_14_not_both_eq_chi_5
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_16_not_both_eq_chi_7
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_17_not_both_eq_chi_8

-- Round 237 (§73-§75): chi(15)/chi(3)/chi(21) propagation lemmas in Branch I.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_11_ne_chi_6_when_chi_15_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_17_ne_chi_12_when_chi_15_eq_chi_12
#print axioms RadoNumbers.General.bAdicEquation_3_chi_19_ne_chi_24_when_chi_15_eq_chi_24
#print axioms RadoNumbers.General.bAdicEquation_3_chi_1_ne_chi_6_when_chi_15_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_15_eq_A_forces_odd_ne_A
#print axioms RadoNumbers.General.bAdicEquation_3_chi_5_ne_chi_6_when_chi_3_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_11_ne_chi_12_when_chi_3_eq_chi_12
#print axioms RadoNumbers.General.bAdicEquation_3_chi_23_ne_chi_24_when_chi_3_eq_chi_24
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_eq_A_forces_odd_ne_A
#print axioms RadoNumbers.General.bAdicEquation_3_chi_13_ne_chi_6_when_chi_21_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_19_ne_chi_12_when_chi_21_eq_chi_12
#print axioms RadoNumbers.General.bAdicEquation_3_chi_21_eq_A_forces_odd_ne_A

-- Round 237 (§76-§77): Branch I-W conditional scaffold + Branch I-V key forcings.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_9_eq_chi_18_in_monoFree_from_branch_I_W_closure
#print axioms RadoNumbers.General.bAdicEquation_3_chi_15_ne_chi_9_when_chi_9_eq_chi_18
#print axioms RadoNumbers.General.bAdicEquation_3_chi_21_ne_chi_9_when_chi_9_eq_chi_18
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_chi_10_not_both_eq_chi_9
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_15_21_ne_chi_9

-- Round 238 (§79): MAJOR — χ(15) = χ(6) FORCED in Branch I-V.
-- Discharges 1 of 4 sub-obligations toward kernel-pure CompressionHyp 3 3.
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_20_eq_chi_9
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_10_eq_chi_9
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_14_eq_chi_15
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_21_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_chi_13_eq_chi_15
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_mono_15_8_13
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_15
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_9
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_V_case_chi_3_eq_chi_6
#print axioms RadoNumbers.General.bAdicEquation_3_chi_15_eq_chi_6_when_chi_9_eq_chi_18

-- Round 239 (§80): MAJOR — χ(21) = χ(6) FORCED in Branch I-V at n ≥ 27.
-- Discharges 2nd of 4 sub-obligations. Uses §72 mono triple (27, 8, 17).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_21_eq_chi_6_when_chi_9_eq_chi_18

-- Round 240 (§81): MAJOR — χ(3) = χ(6) FORCED in Branch I-V at n ≥ 27.
-- COMPLETES Branch I-V multiples-of-3 cascade. Two sub-cases each closing via
-- different mono triples: (27, 8, 17) for chi(3)=chi(9), (27, 5, 14) for chi(3)=3rd.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_eq_chi_9_in_branch_I_V_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_third_in_branch_I_V_contradiction
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_eq_chi_6_when_chi_9_eq_chi_18

-- Round 241 (§82): Branch I-W Case χ(15) = χ(18) closure (sub-lemma toward Branch I-W).
-- 4 sub-cases each closing via different mono triples: (6,11,13), (6,11,13), (3,20,21), (9,2,5).
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_W_chi_15_eq_chi_18_contradiction

-- Round 242 (§83): Branch I-W Case χ(15) = χ(9) closure (2/3 of Branch I-W).
-- 4 terminal branches via mono triples / third_color_eq contradiction:
--   χ(11)=χ(18), χ(21)=χ(18): mono (21,11,18).
--   χ(11)=χ(18), χ(21)=χ(6): third_color_eq gives χ(17)=χ(18) contradicting χ(17)≠χ(18).
--   χ(11)=χ(6), χ(3)=χ(9): mono (3,14,15).
--   χ(11)=χ(6), χ(3)=χ(18): mono (21,17,24).
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_W_chi_15_eq_chi_9_contradiction

-- Round 243 (§84): Branch I-W Case χ(15) = χ(6) closure (3/3, FINAL Branch I-W case).
-- 2 sub-cases on χ(20):
--   χ(20)=χ(9): cascade chi(11)=C, chi(17)=B; mono (9,17,20).
--   χ(20)=χ(18): cascade chi(14)=B, chi(11)=C, chi(17)=B; mono (9,14,17).
-- After this, Branch I-W has 0 cases remaining. Ready for trichotomy assembly.
#print axioms RadoNumbers.General.bAdicEquation_3_branch_I_W_chi_15_eq_chi_6_contradiction

-- Round 244 (§85): **HEADLINE** trichotomy assembly: χ(9) = χ(18) FORCED.
-- Branch I-W master theorem. Combines R241/242/243 via third_color_eq trichotomy on χ(15).
-- After this: Branch I-W is dead. Combined with R238/239/240 (Branch I-V), enables
-- CompressionHyp 3 3 derivation (next round) and removal of lem_compress3_b3 axiom.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_9_eq_chi_18_in_monoFree

-- Round 245 (§86-§87, Bridge §55): **R_3(3) = 27 KERNEL-PURE**.
-- §86: bAdicEquation_3_no_mono_free_at_27 — vacuous no mono-free at n ≥ 27.
-- §87: bAdicEquation_3_compression_at_27_kernel_pure — vacuous compression form for cascade_step.
-- Bridge §55: thm_k3b3_upper_kernel_pure + thm_k3b3_kernel_pure — final R_3(3) = 27 derivation
-- without using lem_compress3_general axiom (replaces axiom-based thm_k3b3 path).
#print axioms RadoNumbers.General.bAdicEquation_3_no_mono_free_at_27
#print axioms RadoNumbers.General.bAdicEquation_3_compression_at_27_kernel_pure
#print axioms RadoNumbers.General.thm_k3b3_upper_kernel_pure
#print axioms RadoNumbers.General.thm_k3b3_kernel_pure

-- Round 247 (Bridge §56-§57): **PARAMETERIZED UPPER-BOUND SCHEMA** for ThresholdConjecture.
-- Extracts the reusable abstraction: ∀ (b, k), kernel-pure no_mono_free_at_bpow ⇒ R_k(b) = b^k.
-- Combines kernel-pure valuation lower bound (general) with the no-mono-free upper bound
-- to produce IsRadoNumber (bAdicEquation b) k (b^k) for any (b, k).
-- Regression check: recovers R_3(3) = 27 via the schema.
#print axioms RadoNumbers.General.isKPartitionRegularAt_bpow_of_no_mono_free
#print axioms RadoNumbers.General.isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow
#print axioms RadoNumbers.General.thm_k3b3_via_general_no_mono_free_schema
#print axioms RadoNumbers.General.thm_k3b3_project_via_general_no_mono_free_schema

-- Round 248 (§88-§89): **(b = 4, k = 3) backbone self-loops** + structural exploration.
-- First migration of R247 schema to b = 4. Backbone theorems instantiate parameterized
-- bAdicEquation_self_loop_chi_diff at b = 4, m ∈ {3, 4, 8, 12, 16}.
-- §89 identifies candidate first master forcing triple (χ(9), χ(12), χ(16)) as the b=4
-- analogue of b=3's (χ(6), χ(9), χ(12)).
#print axioms RadoNumbers.General.bAdicEquation_4_chi_12_ne_chi_16_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_4_chi_24_ne_chi_32_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_4_chi_36_ne_chi_48_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_4_chi_48_ne_chi_64_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_4_chi_9_ne_chi_12_in_monoFree

-- Round 249 (§90): partial closure of b=4 candidate master forcing.
-- Subcase: (χ(9), χ(12), χ(16)) all distinct + χ(8)=χ(9) + χ(4)=χ(12) → False.
-- Cascade ends in MONO triple (16, 7, 11). Validates the (16,7,11) closer pattern
-- as the b=4 analogue of b=3's (6,11,13)-style mono closers.
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_12

-- Round 250 (§90-§91): pressure-test of b=4 master forcing at n = 16.
-- Trivial subcase: chi(8) = chi(9) ∧ chi(4) = chi(9) → mono (4, 8, 9). All three
-- positions have color = χ(9). Direct single-triple closure, no cascade needed.
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_9_4_eq_9
-- §91 NEGATIVE FINDING: chi(8)=chi(9) ∧ chi(4)=chi(16) subcase admits a mono-free
-- 3-coloring at n=16 (explicit witness, all 54 Rado triples verified). The full
-- candidate master forcing `bAdicEquation_4_no_chi_9_12_16_all_distinct` is FALSE
-- at n=16. R251 target: lift to n ≥ 63 (= 4^3 - 1) OR adopt different forcing.

-- Round 251 (§92): R250 SURVIVING WITNESS BRANCH dies at n ≥ 20 (not n=64).
-- THRESHOLD COLLAPSE THEOREM: under chi(8)=chi(9) ∧ chi(4)=chi(16) +
-- (chi(9), chi(12), chi(16)) pairwise distinct, mono-free coloring at n ≥ 20
-- is impossible. 6 Rado triples + 1 self-loop + 2 third_color_eq.
-- Terminal triple: (16, 16, 20) — "anchor self-rado" at d=b=4, m=4.
-- IMPLICATION: the (chi(9), chi(12), chi(16)) candidate IS the b=4 first
-- master forcing — it just needs n ≥ 20 (not the conservative n=63 estimate).
#print axioms RadoNumbers.General.bAdicEquation_4_R250_witness_branch_no_extend_to_20
-- Trivial n=64 corollary (immediate from n=20 case, since 64 ≥ 20):
#print axioms RadoNumbers.General.bAdicEquation_4_R250_witness_branch_no_extend_to_64

-- Round 252 (§93): b=4 all-distinct branch χ(8) = χ(12), χ(4) = χ(9) CLOSED at n ≥ 20.
-- Trichotomy on χ(8) of `bAdicEquation_4_no_chi_9_12_16_all_distinct`:
-- - χ(8) = χ(9):  CLOSED (R249/R250/R251)
-- - χ(8) = χ(12): this round closes ONLY the χ(4) = χ(9) (= A) subcase at n ≥ 20.
-- - χ(8) = χ(16): OPEN.
-- §93 cascade: 9 forced positions + terminal mono (16, 6, 10).
-- Terminal pattern: NEW — "C-anchored color match" (16, y, y+4) at (y, y+4) = (6, 10),
-- distinct from R249 (16, 7, 11) and R251 (16, 16, 20).
-- The χ(4) ∈ {χ(12), χ(16)} subcases admit explicit n=20 witnesses (documented in §93).
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9
-- Trivial n=64 corollary (immediate from n=20 case):
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_12_4_eq_9_at_64

-- Round 253 (§94): b=4 all-distinct branch χ(8) = χ(16), trichotomy on χ(4).
-- - χ(4) = χ(9):  CLOSED at n ≥ 20 via NEW terminal (4, 3, 4) "anchor self-equality".
--   Cascade: 6 forced positions (χ(20)=B, χ(10)=B, χ(5)=C, χ(7)=A, χ(6)=B, χ(3)=A)
--   forces χ(3) = χ(4) = A → mono via (4, 3, 4) which requires χ(3) = χ(4).
-- - χ(4) = χ(16): TRIVIAL at n ≥ 16 via single triple (16, 4, 8) where all three = C.
-- - χ(4) = χ(12): admits n=20 witness (documented in §94); OPEN at n ≥ 64
--   pending thm_k2 + scale-by-4 infrastructure (R254 target).
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_16
-- Trivial n=64 corollary of subcase_8_eq_16_4_eq_9 (immediate from n=20 case):
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct_subcase_8_eq_16_4_eq_9_at_64

-- Round 254 (§95 in Bridge.lean): SCALE-BY-4 BRIDGE for residual cells.
-- Type B reusable infrastructure: under the layer-compression hypothesis hLayer
-- (chi(4d) in {chi(12), chi(16)} for d in [1, 16]), apply RadoNumbers.thm_k2
-- (R(4, 2) = 16) to the scale-by-4 sub-coloring + lift via const_mul to derive
-- mono at level 64, contradicting hNoMono. KERNEL-PURE; depends transitively
-- on RadoNumbers.thm_k2 (which itself is kernel-pure for b >= 3, depends on
-- compress2_lemma_b for general b >= 3 path).
#print axioms RadoNumbers.General.scale4_two_color_subcoloring_lifts_mono_solution
-- Alias of above with the user-requested theorem name:
#print axioms RadoNumbers.General.bAdicEquation_4_multiples_of_4_two_color_reduction_in_residual_cells

-- Round 255 (§96): residual cell (1) layer compression - clean prefix toward d=5.
-- Under residual cell (1) hypotheses (chi(4) = chi(8) = chi(12)) + the contrarian
-- assumption chi(20) = chi(9), force chi(14), chi(10), chi(15), chi(11) values
-- via 8 Rado triples + 1 self-loop + 4 third_color_eq. Deliverable B
-- (strongest contiguous prefix of the §96 §95 cascade). KERNEL-PURE.
-- Full d=5 closure (chi(20) != chi(9)) requires extending to chi(40) contradiction
-- at n >= 40, which needs case split on chi(13) and 6+ additional cascade steps.
-- R256+ target.
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_forces_chi14_10_15_11

-- Round 256 (§97): residual cell (1) cascade prefix Steps 5-10 - no χ(13) split.
-- Given R255 prefix (chi(14)=C, chi(10)=A, chi(15)=C, chi(11)=A) under
-- residual cell (1) + chi(20)=chi(9), force chi(5)=C, chi(6)=C, chi(2)=A,
-- chi(7)=C, chi(3)=A, chi(1)=A. 12 Rado triples + 1 self-loop + 6 third_color_eq.
-- After R255+R256: forced positions are {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
-- 14, 15, 16, 20}. Remaining unknown set: {13, 17, 18, 19}.
-- The full d=5 closure (chi(40) contradiction at n >= 40) requires R257+
-- case split on chi(13) ∈ {chi(9), chi(16)} and cascade through chi(24/28/32/36/40).
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_forces_chi5_6_2_7_3_1

-- Round 257 (§98): residual cell (1), Case chi(13) = chi(9) forces chi(18), chi(19).
-- Begins the chi(13) case split (chi(13) != chi(12) from R256 setup; chi(13) ∈
-- {chi(9), chi(16)}). The Case chi(13) = chi(9) is cleaner: forces chi(18) =
-- chi(12) (via (20, 13, 18) + (16, 14, 18)) and chi(19) = chi(9) (via (16, 15, 19)
-- + (4, 18, 19)). 4 Rado triples + 2 third_color_eq. NO chi(17) dependency.
-- After R257 in this branch: forced positions {1..16, 18, 19, 20}, unforced
-- = {chi(17)}. R258+ pushes to high positions for chi(40) contradiction.
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi9_forces_chi18_19

-- Round 258 (§99): residual cell (1), Case chi(13) = chi(9) high-position
-- cascade to chi(40) MONO. 12 cascade steps + terminal mono (4, 39, 40).
-- KEY TRIPLE: (32, 4, 12) — uses chi(4) = chi(12) (residual cell) to force
-- chi(32) ≠ chi(12). Forced positions added: chi(24)=C, chi(21)=A, chi(28)=B,
-- chi(25)=C, chi(29)=A, chi(30)=A, chi(31)=A, chi(32)=A, chi(35)=C, chi(39)=B,
-- chi(36)=C, chi(40)=B. Terminal mono (4, 39, 40): chi(4)=chi(39)=chi(40)=B.
-- CLOSES the Case chi(13) = chi(9) layer-compression d=5 contradiction.
-- Note: chi(32) = A (NOT B as §95 witness conjectured); the surprise is that
-- (32, 4, 12) Rado triple uses residual cell chi(4) = chi(12) directly.
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi9_high_positions

-- Round 259 (§100): residual cell (1), Case chi(13) = chi(16) branch closure.
-- MAJOR DISCOVERY: a 4-step cascade (32, 4, 12) + (32, 7, 15) + third_color_eq
-- + (32, 1, 9) closes the contradiction WITHOUT using chi(13) hypothesis at all.
-- This means the chi(13) case split (R257 / R258 / R259) was UNNECESSARY for
-- hLayer d=5 closure. R258's 12-step cascade was over-engineered; the actual
-- minimal proof needs only n ≥ 32 (not n ≥ 40) and 3 Rado triples + 1 mono.
-- Combined R255 + R256 + R259 prove: residual cell (1) + chi(20) = chi(9) ⟹
-- False at n ≥ 32 (and a fortiori at n ≥ 40), closing hLayer d=5 for cell (1).
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_case_chi13_eq_chi16_forces_False

-- Round 260 (§101): hLayer d=5 extraction for residual cell (1).
-- Three composed theorems:
-- 1. `..._forces_False_short` — composes R255 + R256 internally + inlines R259
--    cascade. NO chi(13) hypothesis. n ≥ 32.
-- 2. `..._chi20_ne_chi9` — contrapositive: chi(20) ≠ chi(9). Directly feeds R254.
-- 3. `..._layer_compression_d5` — trichotomy form: chi(20) = chi(12) ∨ chi(20)
--    = chi(16). This IS the hLayer d=5 fact for cell (1) consumed by R254 bridge.
-- R258 SUBSUMED: this short proof closes the same contradiction in 4 steps
-- (vs R258's 12 steps), at n ≥ 32 (vs R258's n ≥ 40).
#print axioms RadoNumbers.General.residual_cell_1_chi20_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi20_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d5

-- Round 261 (§102): hLayer d=6 extraction for residual cell (1).
-- 6-step cascade closing at n ≥ 24 under chi(24) = chi(9):
-- Step 1: chi(15) = C  (via (24, 9, 15) + (12, 12, 15))
-- Step 2: chi(11) = A  (via (16, 11, 15) + (12, 8, 11))
-- Step 3: chi(5) = C   (via (24, 5, 11) + (4, 4, 5))
-- Step 4: chi(1) = A   (via (16, 1, 5) + (12, 1, 4))
-- Step 5: chi(7) = C   (via (24, 1, 7) + (4, 7, 8))
-- Step 6: chi(3) excluded from {A, B, C} via (24, 3, 9) + (4, 3, 4) + (16, 3, 7)
--         + third_color_eq → chi(3) = chi(16). Contradicts chi(3) ≠ chi(16). ⊥
-- Three composed theorems (analogous to R260):
-- 1. `..._chi24_eq_chi9_forces_False_short` — direct contradiction, n ≥ 24.
-- 2. `..._chi24_ne_chi9` — contrapositive.
-- 3. `..._layer_compression_d6` — trichotomy form, feeds R254.
#print axioms RadoNumbers.General.residual_cell_1_chi24_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi24_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d6

-- Round 262 (§103): hLayer d=7 extraction for residual cell (1).
-- 7-step cascade + terminal mono (32, 9, 17) closing at n ≥ 32.
-- Step 0: chi(20) = chi(12) (calls R260 + (16, 16, 20))
-- Step 1: chi(2) = chi(16)  ((8, 2, 4) + (28, 2, 9))
-- Step 2: chi(6) = chi(9)   ((8, 6, 8) self-loop + (16, 2, 6))
-- Step 3: chi(13) = chi(16) ((4, 12, 13) + (28, 6, 13))
-- Step 4: chi(17) = chi(9)  ((16, 13, 17) + (20, 12, 17))
-- Step 5: chi(10) = chi(16) ((8, 8, 10) + (28, 10, 17))
-- Step 6: chi(32) = chi(9)  ((32, 4, 12) + (32, 2, 10))
-- Terminal: (32, 9, 17) — chi(32) = chi(9) = chi(17) = A. MONO!
-- Three composed theorems (analogous to R260/R261):
-- 1. `..._chi28_eq_chi9_forces_False_short` — direct contradiction, n ≥ 32.
-- 2. `..._chi28_ne_chi9` — contrapositive.
-- 3. `..._layer_compression_d7` — trichotomy form, feeds R254.
#print axioms RadoNumbers.General.residual_cell_1_chi28_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi28_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d7

-- Round 263 (§104): hLayer d=8 extraction for residual cell (1).
-- Case split on chi(13) ∈ {chi(9), chi(16)} (since chi(13) ≠ chi(12) always).
-- - Case chi(13) = chi(16): forces chi(17) = chi(9), mono via (32, 9, 17).
-- - Case chi(13) ≠ chi(16): chi(13) = chi(9), cascade chi(5) = chi(16),
--   chi(1) = chi(9), mono via (32, 1, 9).
-- Uses R260 internally for chi(20) = chi(12) preamble.
-- Three composed theorems (analogous to R260/R261/R262):
-- 1. `..._chi32_eq_chi9_forces_False_short` — direct contradiction, n ≥ 32.
-- 2. `..._chi32_ne_chi9` — contrapositive.
-- 3. `..._layer_compression_d8` — trichotomy form, feeds R254.
#print axioms RadoNumbers.General.residual_cell_1_chi32_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi32_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d8

-- Round 264 (§105): hLayer d=9 extraction for residual cell (1).
-- KEY INSIGHT: under cell (1) + R261 (chi(24) ∈ {B,C}) + R263 (chi(32) ∈ {B,C}),
-- both chi(24) and chi(32) are FORCED unconditionally:
--   chi(32) ≠ B from (32, 4, 12) + R263 → chi(32) = C.
--   chi(24) ≠ C from self-loop m=8 + chi(32) = C → chi(24) = B.
-- 9-step main cascade + terminal mono (32, 2, 10), NO CASE SPLIT.
-- Three composed theorems (analogous to R260-R263):
-- 1. `..._chi36_eq_chi9_forces_False_short` — direct contradiction, n ≥ 36.
-- 2. `..._chi36_ne_chi9` — contrapositive.
-- 3. `..._layer_compression_d9` — trichotomy form, feeds R254.
#print axioms RadoNumbers.General.residual_cell_1_chi36_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi36_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d9

-- Round 265 (§106): hLayer d=10 extraction for residual cell (1).
-- Sharpened preamble: chi(20) = B, chi(32) = C, chi(28) = B (using R260/R262/R263
-- + (16, 16, 20)/(32, 4, 12)/(16, 28, 32)). 8-step main cascade under chi(40) = A
-- + no-color-left terminal on chi(23). NO CASE SPLIT. Terminal: chi(23) ∉ {A, B, C}
-- via (40, 13, 23) + (12, 20, 23) + (16, 19, 23) → third_color_eq contradiction.
#print axioms RadoNumbers.General.residual_cell_1_chi40_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi40_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d10

-- Round 266 (§107): hLayer d=11 extraction for residual cell (1).
-- Sharpened preamble: chi(20) = B, chi(32) = C, chi(28) = B, chi(24) = B
-- (using R260/R261/R262/R263 + (16, 16, 20)/(32, 4, 12)/(16, 28, 32)/self-loop m=8).
-- 13-step main cascade under chi(44) = A. Terminal: concrete mono triple (32, 2, 10)
-- with chi(32) = chi(2) = chi(10) = chi(16). Same terminal as R264.
#print axioms RadoNumbers.General.residual_cell_1_chi44_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi44_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d11

-- Round 267 (§108): hLayer d=12 extraction for residual cell (1).
-- Sharpened preamble: chi(20) = B, chi(32) = C, chi(24) = B (using R260/R261/R263
-- + (16, 16, 20)/(32, 4, 12)/self-loop m=8). 5-step main cascade under chi(48) = A.
-- Surprise compression: (48, 9, 21) couples A anchors chi(48)/chi(9) in one step.
-- Terminal: concrete mono triple (32, 5, 13) with chi(32) = chi(5) = chi(13) = chi(16).
#print axioms RadoNumbers.General.residual_cell_1_chi48_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi48_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d12

-- Round 268 (§109): hLayer d=13 extraction for residual cell (1).
-- Sharpened preamble: chi(20)=B, chi(32)=C, chi(28)=B, chi(24)=B (using R260..R263).
-- 5-step cascade under chi(52)=A. Alternating A/C propagation through (52,9,22),
-- (32,22,30), (52,17,30), (16,22,26), (52,13,26). Terminal: simplest possible
-- mono triple (16, 13, 17) with chi(16) = chi(13) = chi(17) = chi(16).
#print axioms RadoNumbers.General.residual_cell_1_chi52_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi52_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d13

-- Round 269 (§110): hLayer d=14 extraction for residual cell (1).
-- 3-anchor sharpened preamble: chi(20)=B, chi(32)=C, chi(28)=B (drops chi(24)).
-- 5-step cascade under chi(56)=A. B-exclusions use d=3 jumps via (12,20,23)
-- and (12,28,31), and d=7 via (28,20,27). Terminal: (16, 13, 17) all C.
#print axioms RadoNumbers.General.residual_cell_1_chi56_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi56_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d14

-- Round 270 (§111): hLayer d=15 extraction for residual cell (1).
-- Extended 6-anchor preamble: chi(32)=C, chi(28)=B, chi(24)=B, chi(36)=B, chi(40)=B,
-- chi(45)=C (last conditional on chi(60)=A via self-loop m=15 + (36,36,45)).
-- 4-step cascade: chi(41)=A, chi(26)=C, chi(34)=A, chi(49)=A.
-- Terminal: (60, 34, 49) directly uses d=15 anchor, all three positions = A.
-- Newly discovered unconditional anchors: chi(36)=B (via (16,32,36) + R264),
-- chi(40)=B (via (32,32,40) + R265).
#print axioms RadoNumbers.General.residual_cell_1_chi60_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi60_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d15

-- Round 271 (§112): hLayer d=16 extraction for residual cell (1).
-- COMPLETES the cell (1) hLayer table — all 16 layers (d=1..16) closed.
-- 4-anchor preamble: chi(20)=B, chi(32)=C, chi(24)=B, chi(36)=B.
-- 4-step cascade under chi(64)=A: chi(25)=C, chi(17)=A, chi(33)=C, chi(21)=A.
-- Terminal: no-color-left on chi(37) via (64,21,37) + (4,36,37) + (16,33,37).
-- Bonus sharpening: chi(64) = chi(12) via self-loop m=12 + self-loop m=16 chain.
#print axioms RadoNumbers.General.residual_cell_1_chi64_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_1_chi64_ne_chi9
#print axioms RadoNumbers.General.residual_cell_1_layer_compression_d16
#print axioms RadoNumbers.General.residual_cell_1_chi64_eq_chi12

-- Round 272 (§113): Full hLayer assembly for residual cell (1).
-- Integrates all 16 d-layer compression theorems (d=1..4 base + d=5..16 cascades)
-- into the exact hLayer shape required by R254 scale-by-4 bridge.
-- Then applies scale4_two_color_subcoloring_lifts_mono_solution to derive False
-- directly from cell (1) hypotheses. COMPLETES residual cell (1) closure.
#print axioms RadoNumbers.General.residual_cell_1_full_layer_compression
#print axioms RadoNumbers.General.residual_cell_1_closed_by_scale4_bridge

-- Round 273 (§114): hLayer d=5 extraction for residual cell (2).
-- Cell (2) hypotheses: chi(8)=chi(12) (B-pair) and chi(4)=chi(16) (C-pair).
-- 3-step cascade under chi(20)=A: chi(5)=A, chi(10)=C, chi(14)=A.
-- Terminal: (20, 9, 14) mono with all three = A. Significantly shorter than
-- cell (1) because cell (2)'s chi(4)=C anchor provides direct C-exclusion via (4,4,5).
#print axioms RadoNumbers.General.residual_cell_2_chi20_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi20_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d5

-- Round 274 (§115): hLayer d=6 extraction for residual cell (2).
-- 2-step cascade + no-color-left terminal on chi(15).
-- S1: chi(5) = A (UNCONDITIONAL, via (12,5,8) and (4,4,5))
-- S2: chi(11) = C (via (24,5,11) and (12,8,11))
-- Terminal: chi(15) excluded from A,B,C via (24,9,15)+(12,12,15)+(16,11,15).
#print axioms RadoNumbers.General.residual_cell_2_chi24_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi24_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d6

-- Round 275 (§116): hLayer d=7 extraction for residual cell (2).
-- 3-anchor unconditional preamble: chi(20)=B, chi(17)=A, chi(15)=A.
-- 4-step cascade under chi(28)=A: chi(10)=C, chi(11)=A, chi(18)=C, chi(22)=A.
-- Terminal: (28, 15, 22) mono with chi(28)=chi(15)=chi(22)=A.
-- Key cell-2 insight: chi(4)=chi(16)=C creates many cheap unconditional
-- forcings via (4, X, X+1) propagation (chi(15) != C, chi(17) != C, etc.).
#print axioms RadoNumbers.General.residual_cell_2_chi28_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi28_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d7

-- Round 276 (§117): hLayer d=8 extraction for residual cell (2) + reusable helpers.
-- Extracted helpers (unconditional under cell (2), reusable in d=9..16):
--   chi20=chi12 (B): via R273 + (16, 16, 20).
--   chi17=chi9 (A):  via chi20=B + (4, 16, 17) + (20, 12, 17).
-- d=8 closure: ONE-STEP via terminal mono (32, 9, 17) using chi17=A helper.
#print axioms RadoNumbers.General.residual_cell_2_chi20_eq_chi12
#print axioms RadoNumbers.General.residual_cell_2_chi17_eq_chi9
#print axioms RadoNumbers.General.residual_cell_2_chi32_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi32_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d8

-- Round 277 (§118): hLayer d=9 extraction for residual cell (2) + chi5=chi9 helper.
-- Extracted helper:
--   chi5=chi9 (A): via (12, 5, 8) + (4, 4, 5) (UNCONDITIONAL, reusable).
-- 2-step cascade under chi(36)=A: chi(14)=C, chi(18)=C.
-- Terminal: (16, 14, 18) MONO with chi(16)=chi(14)=chi(18)=C.
#print axioms RadoNumbers.General.residual_cell_2_chi5_eq_chi9
#print axioms RadoNumbers.General.residual_cell_2_chi36_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi36_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d9

-- Round 278 (§119): hLayer d=10 extraction for residual cell (2) + chi15=chi9 helper.
-- Extracted helper:
--   chi15=chi9 (A): via (4, 15, 16) + (12, 12, 15) (UNCONDITIONAL, reusable).
-- d=10 closure: ONE-STEP via terminal mono (40, 5, 15)
--   using chi5=A (R277 helper) and chi15=A (NEW R278 helper).
#print axioms RadoNumbers.General.residual_cell_2_chi15_eq_chi9
#print axioms RadoNumbers.General.residual_cell_2_chi40_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi40_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d10

-- Round 279 (§120): hLayer d=11 extraction for residual cell (2) + chi3=chi9 helper.
-- Extracted helper:
--   chi3=chi9 (A): via (4, 3, 4) + (20, 3, 8) (UNCONDITIONAL).
-- 8-step cascade under chi(44)=A:
--   chi(14)=C, chi(18)=A, chi(7)=C, chi(11)=A, chi(22)=C,
--   chi(26)=B, chi(24)=C (via R274), chi(28)=B (via R275).
-- Terminal: (8, 26, 28) MONO with all three positions = B.
#print axioms RadoNumbers.General.residual_cell_2_chi3_eq_chi9
#print axioms RadoNumbers.General.residual_cell_2_chi44_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi44_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d11

-- Round 280 (§121): hLayer d=12 extraction for residual cell (2).
-- ONE-STEP closure via terminal mono (48, 3, 15) using existing helpers
-- chi(3)=A (R279) and chi(15)=A (R278). No new helper extracted.
#print axioms RadoNumbers.General.residual_cell_2_chi48_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi48_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d12

-- Round 281 (§122): hLayer d=13 extraction for residual cell (2).
-- 1-step cascade chi(18)=C + no-color-left terminal on chi(22).
-- Cascade: chi(18)=C via (52,5,18) [≠A] + (8,18,20) [≠B].
-- Terminal: chi(22) excluded from A,B,C via (52,9,22)+(8,20,22)+(16,18,22).
-- No new helper extracted.
#print axioms RadoNumbers.General.residual_cell_2_chi52_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi52_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d13

-- Round 282 (§123): hLayer d=14 extraction for residual cell (2).
-- ONE-STEP closure via terminal mono (56, 3, 17) using existing helpers
-- chi(3)=A (R279) and chi(17)=A (R276). No new helper.
#print axioms RadoNumbers.General.residual_cell_2_chi56_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi56_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d14

-- Round 283 (§124): hLayer d=15 extraction for residual cell (2).
-- 7-step cascade + no-colour-left terminal on chi(30).
-- S1 chi(18)=C via (60,3,18)+(8,18,20); S2 chi(14)=A via (8,12,14)+(16,14,18);
-- S3 chi(22)=A via (8,20,22)+(16,18,22); S4 chi(7)=C via (20,7,12)+(60,7,22);
-- S5 chi(11)=A via (12,8,11)+(16,7,11); S6 chi(24)=B via (24,18,24)+R274;
-- S7 chi(26)=C via (60,11,26)+(8,24,26).
-- Terminal: chi(30) excluded from A,B,C via (60,15,30)+(24,24,30)+(16,26,30).
-- No new helper extracted.
#print axioms RadoNumbers.General.residual_cell_2_chi60_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi60_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d15

-- Round 284 (§125): hLayer d=16 extraction for residual cell (2) — final layer.
-- 6-step cascade + B-monochromatic terminal (12, 33, 36).
-- S1 chi(25)=C via (64,9,25)[≠A]+(20,20,25)[≠B; degenerate y=z];
-- S2 chi(24)=B via (4,24,25)[≠C; uses S1]+R274 [chi(24)∈{B,C}];
-- S3 chi(21)=B via (64,5,21)[≠A; uses chi(5)=A R277]+(16,21,25)[≠C; uses S1];
-- S4 chi(32)=C via self-loop m=8 [chi(24)≠chi(32); uses S2]+R276 [chi(32)∈{B,C}];
-- S5 chi(33)=B via (64,17,33)[≠A; uses chi(17)=A R276]+(4,32,33)[≠C; uses S4];
-- S6 chi(36)=B via (16,32,36)[≠C; uses S4]+R277 d9 [chi(36)∈{B,C}].
-- Terminal: (12, 33, 36) all B forces monochromatic Rado solution.
-- Completes cell (2) hLayer table — all 16 layers (d=1..16) closed.
-- No new helper extracted (reuses chi(5)=A, chi(17)=A, chi(20)=B, layer d6/d8/d9).
#print axioms RadoNumbers.General.residual_cell_2_chi64_eq_chi9_forces_False_short
#print axioms RadoNumbers.General.residual_cell_2_chi64_ne_chi9
#print axioms RadoNumbers.General.residual_cell_2_layer_compression_d16

-- Round 285 (§126): Full hLayer assembly for residual cell (2) + R254 bridge application.
-- Integrates all 16 d-layer compression theorems (d=1..4 base + d=5..16 cascades from R273-R284)
-- into the exact hLayer shape required by R254 scale-by-4 bridge.
-- Then applies scale4_two_color_subcoloring_lifts_mono_solution to derive False
-- directly from cell (2) hypotheses. COMPLETES residual cell (2) closure.
#print axioms RadoNumbers.General.residual_cell_2_full_layer_compression
#print axioms RadoNumbers.General.residual_cell_2_closed_by_scale4_bridge

-- Round 286 (§127): residual cell (3) hLayer d=5 — DELIVERABLE B (forced prefix only).
-- Cell (3) hypotheses: chi(4)=chi(12)=B (left B-anchor), chi(8)=chi(16)=C (right C-anchor).
-- 8 forced positions derived under chi(20)=A: chi(15)=C, chi(11)=A, chi(14)=B,
-- chi(17)=A, chi(13)=A, chi(18)=B, chi(19)=A, chi(6)=B.
-- OBSTRUCTION at n>=20: sub-case (chi(5), chi(7)) = (A, C) admits valid 3-coloring;
-- no terminal mono in [1, 20]. Cell (3) d=5 closure needs higher threshold (n>=28+).
-- This matches the R254 §95 docstring's note about cell (3) obstruction.
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_forces_prefix

-- Round 287 (§128): cell (3) d=5 extended prefix + (C,C) sub-case closure.
-- Extends R286 prefix with chi(22) != A and chi(24) != A at n >= 24.
-- Plus closes sub-case (chi(5), chi(7)) = (C, C) via terminal (8, 5, 7) mono.
-- Obstruction: 3 remaining sub-cases ((A,A), (A,C), (C,A)) need deeper cascade.
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_forces_prefix2
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_subcase_chi5_chi7_both_C_forces_False

-- Round 288 (§129): cell (3) d=5 (A,A) sub-case extended prefix (Deliverable B).
-- 10 NEW forced positions under chi(20)=A + chi(5)=A + chi(7)=A at n >= 32:
--   chi(10)=B (sub-case specific), chi(24)=C, chi(22)=B, chi(25)=C, chi(21)=A,
--   chi(26)=B, chi(23)=A, chi(28)=B, chi(29)=A, chi(31)=A (latter 9 unconditional
--   under R286 prefix + chi(20)=chi(9)).
-- Key derivations: self-loop m=6 forces chi(24) != B; (20, 20, 25) self-mono
-- forces chi(25) != A; chain to chi(28), chi(29), chi(31) all via standard
-- anchor-pair propagation.
-- OBSTRUCTION: Despite 17+ forced positions, no terminal mono in [1, 32].
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_A_forces_prefix

-- Round 289 (§130): cell (3) d=5 (A,A) sub-case FULL CLOSURE at n >= 32.
-- Key: self-loop m=8 ((32, 24, 32)) + chi(24)=C from R288 → chi(32) != C.
-- Trichotomy → chi(32) in {A, B}. Both cases lead to mono:
--   chi(32)=A: terminal (32, 5, 13) all A.
--   chi(32)=B: terminal (32, 4, 12) all B.
-- This is the FIRST closed sub-case of cell (3) d=5 (besides trivial (C,C)).
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_A_forces_False_continuation

-- Round 290 (§131): cell (3) d=5 (A, C) sub-case CLOSURE at n >= 32.
-- Strategic insight: R289's (A,A) proof never used chi(7)=A; the closure
-- via chi(32) split only needs chi(5)=A. So (A, C) closes by IDENTICAL proof
-- with chi(7)=C as unused hypothesis.
-- This reveals that cell (3) d=5 closure depends on chi(5), not chi(7).
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_subcase_chi5_A_chi7_C_forces_False

-- Round 291 (§132): cell (3) d=5 FULL DIRECT CLOSURE at n >= 32.
-- BREAKTHROUGH: chi(32) pivot with terminal (32, 9, 17) for A-case
-- (using only chi(9), chi(17) - both unconditional) bypasses all (chi(5), chi(7))
-- sub-cases. Single direct proof closes cell (3) d=5 entirely.
-- The earlier sub-case theorems (R287/R289/R290) are now specialized historical
-- artifacts; this direct proof subsumes them.
#print axioms RadoNumbers.General.residual_cell_3_chi20_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi20_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d5

-- Round 292 (§133): cell (3) d=6 closure at n >= 24.
-- 4-step cascade under chi(24)=A: chi(15)=C, chi(11)=A, chi(5)=C, chi(3)=C.
-- Terminal: (8, 3, 5) all C → MONO.
-- Cell (3) d=6 closes at LOWER threshold (n >= 24) than d=5 (n >= 32).
#print axioms RadoNumbers.General.residual_cell_3_chi24_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi24_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d6

-- Round 293 (§134): cell (3) d=7 closure at n >= 32.
-- 3-branch case split on (chi(24), chi(32)):
--   Case chi(24)=B: cascade via chi(10)=A→chi(17)=C→chi(21)=B→terminal (4,20,21).
--   Case chi(24)=C, chi(32)=A: cascade via chi(17)=C→chi(21)=B→terminal (4,20,21).
--   Case chi(24)=C, chi(32)=B: terminal (32,4,12) all B.
-- Uses R291 (chi(20)=B) and R292 (chi(24)∈{B,C}). Threshold n>=32.
#print axioms RadoNumbers.General.residual_cell_3_chi28_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi28_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d7

-- Round 294 (§135): cell (3) d=8 closure at n >= 32.
-- 4-step cascade under chi(32)=A (using R291 chi(20)=B, R292 chi(24)∈{B,C}):
--   Step 1: chi(20)=B (from R291) + (16, 16, 20) ≠ C confirms chi(20)=B.
--   Step 2: chi(17)=C via (32, 9, 17) ≠ A (uses chi(32)=A, chi(9)=A) +
--           (20, 12, 17) ≠ B (uses chi(20)=B, chi(12)=B).
--   Step 3: chi(21)=A via (4, 20, 21) ≠ B (uses chi(4)=B, chi(20)=B) +
--           (16, 17, 21) ≠ C (uses chi(16)=C, chi(17)=C).
--   Step 4: chi(13)=C via (32, 13, 21) ≠ A (uses chi(32)=A, chi(21)=A) +
--           (4, 12, 13) ≠ B (uses chi(4)=B, chi(12)=B).
-- Terminal: (16, 13, 17) all C → MONO.
-- No sub-case split needed (direct closure). Threshold n >= 32.
#print axioms RadoNumbers.General.residual_cell_3_chi32_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi32_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d8

-- Round 295 (§136): cell (3) d=9 closure at n >= 36.
-- Clean self-loop cascade under chi(36)=A (using R291 chi(20)=B, R292 chi(24)∈{B,C},
-- R294 chi(32)∈{B,C}):
--   Step P: chi(20)=B (from R291) + (16, 16, 20) ≠ C.
--   Step S1: chi(18)=B via (36, 9, 18) ≠ A (uses chi(36)=A, chi(9)=A) +
--            (8, 16, 18) ≠ C (uses chi(8)=C, chi(16)=C).
--   Step S2: chi(32)=C via R294 + (32, 4, 12) ≠ B (uses chi(4)=B, chi(12)=B).
--   Step S3: chi(24)=B via R292 + (32, 24, 32) ≠ C (uses chi(32)=C; self-loop).
-- Terminal: (24, 18, 24) all B → MONO (self-loop terminal).
-- No sub-case split needed. Threshold n >= 36.
#print axioms RadoNumbers.General.residual_cell_3_chi36_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi36_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d9

-- Round 296 (§137): cell (3) d=10 closure at n >= 40.
-- Minimal cascade under chi(40)=A:
--   P1: chi(20)=B via R291 + (16, 16, 20) ≠ C (self-loop x=y).
--   P2: chi(32)=C via R294 + (32, 4, 12) ≠ B (uses h4_eq_12).
--   P3: chi(24)=B via R292 + (32, 24, 32) ≠ C (self-loop x=z; uses chi(32)=C).
--   S1: chi(30) ≠ B via (24, 24, 30) self-loop x=y (uses chi(24)=B).
--   S2: chi(30) ≠ A via (40, 30, 40) self-loop x=z (uses h40_eq_9).
--   S3: chi(30) = C by trichotomy.
-- Terminal: (8, 30, 32) all C → MONO.
-- Notable: R293 (d=7) and R295 (d=9) are NOT used.
-- Five self-loops total. Threshold n >= 40.
#print axioms RadoNumbers.General.residual_cell_3_chi40_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi40_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d10

-- Round 297 (§138): SHORTCUT DISCOVERY + cell (3) d=11 closure.
-- AUDIT: Triple (32, 8, 16) — d=8, y=8, z=16; 32+32=64=4*16 ✓.
-- Under h8_eq_16 (cell (3) hypothesis), the general Rado constraint forces
-- chi(32) ≠ chi(8) = C. Combined with R294 d=8 (chi(32) ∈ {B,C}) and
-- (32, 4, 12) excluding B, we get IMMEDIATE False at n >= 32.
-- This means: cell (3) hypotheses + hNoMono ⟹ False at n >= 32 unconditionally.
-- All hLayer facts for d >= 5 trivialize via False.elim from here.
--
-- New direct closure theorem:
--   residual_cell_3_closed_directly_at_32
--
-- R297 d=11 three-theorem suite is trivial wrapper over the direct closure;
-- the chi(44) = chi(9) hypothesis in forces_False is unused (kept for signature
-- consistency with R291-R296). R291-R296 not refactored.
--
-- Triples used:
--   (32, 4, 12): excludes chi(32) = B (re-cited from R294).
--   (32, 8, 16): excludes chi(32) = C (the new shortcut).
#print axioms RadoNumbers.General.residual_cell_3_closed_directly_at_32
#print axioms RadoNumbers.General.residual_cell_3_chi44_eq_chi9_forces_False
#print axioms RadoNumbers.General.residual_cell_3_chi44_ne_chi9
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d11

-- Round 298 (§139): cell (3) d=12..16 wrappers + full integration.
-- Five SHORTCUT wrappers (each is just False.elim of residual_cell_3_closed_directly_at_32):
--   d=12 at n>=48, d=13 at n>=52, d=14 at n>=56, d=15 at n>=60, d=16 at n>=64.
-- Full integration theorem residual_cell_3_full_layer_compression assembles
-- the R254 bridge interface ∀ d, 1 ≤ d → d ≤ 16 → χ(4d) ∈ {χ(12),χ(16)} via
-- interval_cases d, dispatching:
--   d=1: h4_eq_12 left.            d=2: h8_eq_16 right.
--   d=3: χ(12)=χ(12) rfl left.     d=4: χ(16)=χ(16) rfl right.
--   d=5..10: R291..R296 cascade.   d=11..16: R297..R298 shortcuts.
-- Bridge closure residual_cell_3_closed_by_scale4_bridge at n>=64 applies
-- R254 (scale4_two_color_subcoloring_lifts_mono_solution) to the full
-- integration. Mirrors R272 (cell 1) and R285 (cell 2).
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d12
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d13
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d14
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d15
#print axioms RadoNumbers.General.residual_cell_3_layer_compression_d16
#print axioms RadoNumbers.General.residual_cell_3_full_layer_compression
#print axioms RadoNumbers.General.residual_cell_3_closed_by_scale4_bridge

-- Round 299 (§140): all-distinct 9-cell integration at n>=64.
-- Trichotomy on (chi(8), chi(4)) ∈ {A=chi9, B=chi12, C=chi16}^2 = 9 cases.
-- omega derives chi4 ∈ {chi9, chi12, chi16} from chi4 < 3 + pairwise distinct.
-- Dispatch:
--   6 direct cells -> existing subcase_8_eq_X_4_eq_Y theorems + R250 witness branch.
--   3 residual cells -> residual_cell_{1,2,3}_closed_by_scale4_bridge.
-- Mirrors bAdicEquation_3_no_chi_6_9_12_all_distinct (b=3, 4 cases).
-- Threshold n>=64 forced by bridge closures.
#print axioms RadoNumbers.General.bAdicEquation_4_no_chi_9_12_16_all_distinct

-- Round 300 (§141): not-all-distinct branch — Case A, Case C, and partial final.
-- Case A (chi9 = chi12) closes via self-loop (12, 9, 12): x=z=12, y=9, d=3.
-- Case C (chi12 = chi16) closes via self-loop (16, 12, 16): x=z=16, y=12, d=4.
-- Case B (chi9 = chi16) is the REMAINING OPEN OBSTRUCTION; no single Rado
-- triple gives False because no self-loop combines positions 9 and 16.
-- Partial final theorem `_when_chi9_ne_chi16` routes through R299.
-- Full `bAdicEquation_4_no_mono_free_at_64` requires closing Case B (see report).
#print axioms RadoNumbers.General.bAdicEquation_4_chi_9_eq_chi_12_forces_False
#print axioms RadoNumbers.General.bAdicEquation_4_chi_12_eq_chi_16_forces_False
#print axioms RadoNumbers.General.bAdicEquation_4_no_mono_free_at_64_when_chi9_ne_chi16

-- Round 301 (§142): Case B sub-case (chi4 = chi9, chi8 = chi12) closure at n >= 64.
-- Repaired cascade avoiding chi13/chi32; 11 explicit triples.
--   S1: chi(5) = C via (16, 5, 9) [≠A] + (12, 5, 8) [≠B]
--   S2: chi(10) = C via (4, 9, 10) [≠A] + (8, 8, 10) [self-loop x=y; ≠B]
--   S3: chi(5) = chi(10) via omega trichotomy
--   S4: chi(20) = B via (16, 16, 20) self-loop + (20, 5, 10) [≠C via chi5=chi10]
--   S5: chi(17) = chi(5) (C) via (4, 16, 17) [≠A] + (12, 17, 20) [≠B] + omega
--   S6: chi(48) = chi(5) (C) via (48, 4, 16) [≠A] + (48, 8, 20) [≠B] + omega
-- Terminal (48, 5, 17) all chi = chi(5) → MONO.
-- Uses omega in place of private third_color_eq from BasicResults.
-- 7 remaining sub-cases of Case B still open: (A,C), (B,A), (B,B), (B,C), (C,A), (C,B), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_eq_12_forces_False

-- Round 302 (§143): Case B sub-case (chi4 = chi12, chi8 = chi9) closure at n >= 64.
-- Short cascade via (32, 8, 16) terminal MONO A:
--   S1: chi(5) = C via (16, 5, 9) [≠A] + (4, 4, 5) [self-loop x=y; ≠B]
--   S2: chi(13) = C via (16, 9, 13) [≠A] + (4, 12, 13) [≠B]
--   S3: chi(5) = chi(13) via omega
--   S4: chi(32) ≠ B via (32, 4, 12) [h4_eq_12]
--   S5: chi(32) ≠ chi(5) via (32, 5, 13) [uses S3]
--   S6: chi(32) = A by omega
-- Terminal (32, 8, 16): chi(32) = chi(8) = chi(16) all A → MONO.
-- 6 remaining sub-cases of Case B still open: (A,C), (B,B), (B,C), (C,A), (C,B), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_9_forces_False

-- Round 303 (§144): Case B sub-case (chi4 = chi9, chi8 = third) closure at n >= 64.
-- SHORTEST Case B sub-case so far — only 6 explicit triples.
--   S1: chi(10) = B via (4, 9, 10) [≠A; h4_eq_9] + (8, 8, 10) [self-loop; ≠C] + omega
--   S2: chi(13) = C via (16, 9, 13) [≠A; h9_eq_16] + (12, 10, 13) [≠B; uses S1] + omega
--   S3: chi(15) = A via (12, 12, 15) [self-loop; ≠B] + (8, 13, 15) [≠C; uses S2] + omega
-- Terminal (4, 15, 16): chi(4) = chi(15) = chi(16) all A → MONO.
-- 5 remaining sub-cases of Case B still open: (B,B), (B,C), (C,A), (C,B), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_9_8_third_forces_False

-- Round 304 (§145): Case B sub-case (chi4 = chi12, chi8 = third) closure at n >= 64.
-- No-color-left contradiction on chi(7) — distinct pattern from MONO terminals.
--   S1: chi(5) = C via (16, 5, 9) [≠A] + (4, 4, 5) [self-loop; ≠B] + omega
--   S2: chi(13) = C via (16, 9, 13) [≠A] + (4, 12, 13) [≠B; h4_eq_12] + omega
--   S3: chi(15) = A via (12, 12, 15) [self-loop; ≠B] + (8, 13, 15) [≠C; uses S2] + omega
--   S4: chi(32) = A via (32, 4, 12) [≠B; h4_eq_12] + (32, 5, 13) [≠C; uses S1+S2] + omega
-- No-color-left on chi(7):
--   chi(7) ≠ C via (8, 5, 7) [uses S1]
--   chi(7) ≠ B via (12, 4, 7) [uses h4_eq_12]
--   chi(7) ≠ A via (32, 7, 15) [uses S3+S4]
--   chi(7) < 3 + ≠ A, ≠ B, ≠ C (three distinct anchors) → omega gives False.
-- 4 remaining sub-cases of Case B still open: (B,B), (C,A), (C,B), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_third_forces_False

-- Round 305 (§146): Case B sub-case (chi4 = third, chi8 = chi12) closure at n >= 64.
-- SHORTEST Case B sub-case overall — only 3 explicit triples.
--   S1: chi(5) = B via (16, 5, 9) [≠A] + (4, 4, 5) [self-loop x=y; ≠C] + omega
-- Terminal (12, 5, 8): chi(12) = chi(5) = chi(8) all B → MONO.
-- Max position 12; max threshold n>=12 (but n>=64 for API compat).
-- 3 remaining sub-cases of Case B still open: (B,B), (C,A), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_12_forces_False

-- Round 306 (§147): Case B sub-case (chi4 = third, chi8 = chi9) closure at n >= 64.
-- Most complex Case B sub-case so far: 3-way nested branch.
-- Universal forced: chi(5) = B, chi(28) ≠ A, chi(10) ≠ A, chi(20) ≠ A.
-- Branch on chi(10):
--   Branch I (chi(10) = B):
--     chi(20) = C via (20, 5, 10) + (16, 16, 20) + omega
--     chi(13) = C via (12, 10, 13) + (16, 9, 13) + omega
--     chi(28) = B via (28, 13, 20) + omega
--     Terminal (28, 5, 12) all B → MONO.
--   Branch II (chi(10) = C):
--     chi(28) = C via (28, 5, 12) [≠B] + omega.
--     Sub-branch on chi(13):
--       II.A (chi(13) = B): chi(32) = C, chi(18) = B, chi(20) = C.
--         Terminal (32, 20, 28) all C → MONO.
--       II.B (chi(13) = C): chi(20) = B, chi(32) = C, chi(18) = B,
--         chi(21) = A, chi(23) = C, chi(17) = A, chi(15) = C.
--         Terminal (32, 15, 23) all C → MONO.
-- 2 remaining sub-cases of Case B still open: (B,B), (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_eq_9_forces_False

-- Round 307 (§148): Case B sub-case (chi4 = chi12, chi8 = chi12) closure at n >= 64.
-- Cell-(1)-shape under h9_eq_16: 3-way nested branch converging at chi(20) = B,
-- then shared downstream cascade to terminal (64, 5, 21) all C.
-- Universal forced: chi(5) = C, chi(13) = C, chi(32) = A.
-- chi(20) = B via 3-way branch (all converge):
--   Branch I (chi(10) = C): (20, 5, 10) ≠ C → chi(20) = B.
--   Branch II (chi(10) = A): chi(6) = C derived.
--     II.B (chi(11) = C): (20, 6, 11) ≠ C → chi(20) = B.
--     II.A (chi(11) = A): chi(15) = C; (20, 15, 20) self-loop → chi(20) = B.
-- Shared downstream: chi(17) = C, chi(48) = A, chi(21) = C, chi(64) = C.
-- Terminal (64, 5, 21) all C → MONO.
-- 1 remaining sub-case of Case B still open: (C,C).
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_eq_12_8_eq_12_forces_False

-- Round 308 (§149): Case B sub-case (chi4 = third, chi8 = third) closure at n >= 64.
-- FINAL Case B sub-case. 2-way branch on chi(10) (universal: chi(10) ≠ C):
--   Branch I (chi(10) = B): short cascade via (12, 10, 13) + (16, 9, 13) → chi(13) = C;
--     (20, 5, 10) + (16, 16, 20) → chi(20) = C.
--     Terminal (20, 8, 13) all C → MONO.
--   Branch II (chi(10) = A): 12-step cascade:
--     chi(6)=B, chi(28)=C, chi(15)=A, chi(11)=B, chi(20)=C, chi(13)=B,
--     chi(24)=C, chi(32)=A, chi(17)=B, chi(48)=A, chi(21)=B.
--     No-color-left on chi(64): (64, 16, 32) ≠ A + (64, 5, 21) ≠ B + (64, 4, 20) ≠ C → omega.
-- ALL 9 Case B sub-cases CLOSED!
#print axioms RadoNumbers.General.bAdicEquation_4_chi9_eq_chi16_subcase_4_third_8_third_forces_False

-- Round 309 (§150): Case B dispatcher at n >= 64.
-- 3x3 by_cases on (chi4, chi8) ∈ {A=chi9, B=chi12, C=third}².
-- Auto-distinctness chi9 ≠ chi12 from bAdicEquation_4_chi_9_ne_chi_12_in_monoFree.
-- Dispatch ledger:
--   (A,A): direct (16, 4, 8) MONO A.
--   (A,B) → R301.   (A,C) → R303.
--   (B,A) → R302.   (B,B) → R307.   (B,C) → R304.
--   (C,A) → R306.   (C,B) → R305.   (C,C) → R308 (omega-derived h4_eq_8).
-- Case B FULLY DISPATCHED.
#print axioms RadoNumbers.General.bAdicEquation_4_chi_9_eq_chi_16_forces_False

-- Round 310 (§151): FINAL ASSEMBLY — bAdicEquation_4_no_mono_free_at_64.
-- 2-way by_cases on h9_eq_16:
--   χ9 = χ16: R309 Case B dispatcher.
--   χ9 ≠ χ16: R300 partial final (routes through R299 all-distinct).
-- Equivalent to R₃(4) ≤ 64. Kernel-pure.
#print axioms RadoNumbers.General.bAdicEquation_4_no_mono_free_at_64

-- Round 311 (§152): MAIN THEOREM — R₃(4) = 64 via the general schema.
-- thm_k3b4_via_general_no_mono_free_schema: applies isRadoNumber_bAdicEquation_of_no_mono_free_at_bpow
-- at (b, k) = (4, 3) using R310 as the no-mono-free obligation.
-- Plus project-namespace version via isRadoNumber_bAdicEquation_iff_project.
-- Mirrors thm_k3b3_via_general_no_mono_free_schema (b=3 regression check).
-- **R₃(4) = 4³ = 64 ESTABLISHED, kernel-pure.**
#print axioms RadoNumbers.General.thm_k3b4_via_general_no_mono_free_schema
#print axioms RadoNumbers.General.thm_k3b4_project_via_general_no_mono_free_schema

-- Round 313 (§153): R₄(3) = 81 setup — scale-3 three-color bridge.
-- b=3, k=4 analog of R254 scale4_two_color_subcoloring_lifts_mono_solution.
-- Takes 4-coloring with multiples-of-3 layer compressed to 3 colors (cA, cB, cC),
-- constructs ψ : ℕ → {0,1,2}, applies R₃(3) = 27 via thm_k3b3_via_general_no_mono_free_schema,
-- lifts mono ψ-solution to mono χ-solution at scale 3.
-- Reusable bridge for the R₄(3) = 81 cascade (analogous to R₃(4) = 64 architecture).
#print axioms RadoNumbers.General.scale3_three_color_subcoloring_lifts_mono_solution

-- Round 314 (§154): R₄(3) = 81 power-anchor prefix.
-- Basic self-loop inequalities along the b=3 power chain {3, 9, 27, 81}.
-- Derived k-agnostically from generic bAdicEquation_self_loop_chi_diff (xz family)
-- and bAdicEquation_self_loop_xy_chi_diff (xy family). Reusable for any
-- k-coloring of [1, n] with hNoMono.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_2_ne_chi_3_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_3_ne_chi_4_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_ne_chi_36_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_54_ne_chi_81_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_18_ne_chi_27_in_monoFree

-- Round 315 (§155): Begin χ(27) = χ(81) branch for R₄(3) = 81.
-- Forces 4 non-A positions {χ18, χ36, χ54, χ72} ≠ A under h27_eq_81.
-- Triples used: (27, 18, 27), (27, 27, 36), (81, 54, 81), (27, 72, 81).
-- Audit: NO direct closure. χ(9) = A consistent; full closure needs nested split.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_chi_81_forces_prefix

-- Round 316 (§156): χ(27) = χ(81) branch, sub-case χ(9) = χ(27).
-- Three A-anchors {χ9, χ27, χ81}. Force 3 additional non-A positions beyond R315:
-- χ(24), χ(30), χ(78) all ≠ A.
-- Triples: (9, 24, 27), (9, 27, 30), (9, 78, 81).
-- No direct contradiction; further split needed for full closure.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_chi_81_subcase_chi_9_eq_27_forces_prefix

-- Round 317 (§157): χ(27) = χ(81) branch, sibling sub-case χ(9) ≠ χ(27).
-- Two distinct anchors A = χ27 = χ81, B = χ9. Forces 6 positions:
--   χ18, χ36, χ54, χ72 ≠ A (from R315).
--   χ6, χ12 ≠ B (universal self-loops at m=3).
-- Cleaner setup than R316; potential for layer compression via χ(18) anchor.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_chi_81_subcase_chi_9_ne_27_forces_prefix

-- Round 318 (§158): χ(27) = χ(81) + χ(9) ≠ χ(27), split on χ(18).
-- Branch I (χ18 = B = χ9): 2 B-anchors {9, 18}.
--   Forced: χ(6), χ(12), χ(15), χ(21), χ(24) ≠ B; χ(36), χ(54), χ(72) ≠ A.
--   No direct closure; B-mono needs 3rd B-anchor.
-- Branch II (χ18 ≠ B): 3-distinct anchors {χ27 = A, χ9 = B, χ18 = C}.
--   Bridge-ready (scale3_three_color_subcoloring_lifts_mono_solution) modulo hLayer.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_eq9_forces_prefix
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_three_anchors

-- Round 319 (§159): Branch II conditional layer-cascade lemmas.
-- Three single-triple conditional lemmas building toward classification of
-- χ(36), χ(54), χ(72) into the anchor set {A := χ27, B := χ9, C := χ18}.
-- Lemma 1 (n ≥ 54): χ(54) = χ(18) → χ(36) ≠ χ(18).  triple (3·18, 18, 36).
-- Lemma 2 (n ≥ 72): χ(72) = χ(18) → χ(42) ≠ χ(18).  triple (3·24, 18, 42).
-- Lemma 3 (n ≥ 72): χ(72) = χ(9)  → χ(33) ≠ χ(9).   triple (3·24, 9, 33).
-- Each uses bAdicEquation_general_rado_constraint with explicit (d, y).
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi18_forces_chi36_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi72_eq_chi18_forces_chi42_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi72_eq_chi9_forces_chi33_ne_chi9

-- Round 320 (§160): Branch II high-layer classifier around χ(54).
-- (1) Universal self-loop χ(36) ≠ χ(54) via (54, 36, 54) at n ≥ 54.
--     Instantiation of bAdicEquation_self_loop_chi_diff at b=3, m=18.
-- (2) Fourth-color classifier: if χ(54) is the fourth color
--     (χ54 ≠ χ9 ∧ χ54 ≠ χ18) under the Branch II 3-anchor setup, then
--     χ(36) ∈ {χ(9), χ(18)}.
--     Proof: pairwise distinctness of {A,B,C,D := χ54} + IsKColoring 4
--     + χ(36) ≠ A (R314) + χ(36) ≠ D (R320 universal) → omega.
-- Provides handler for the χ54 = D branch that R319 conditional lemmas
-- don't cover (R319 covers χ54 = C via χ54_eq_chi18 → χ36 ≠ χ18).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_36_ne_chi_54_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_fourth_forces_chi36_in_9_or_18

-- Round 321 (§161): Unified Branch II χ(54)/χ(36) dispatcher + universal χ(48) ≠ χ(72).
-- (1) Universal self-loop χ(48) ≠ χ(72) via (72, 48, 72) at n ≥ 72.
--     Instantiation of bAdicEquation_self_loop_chi_diff at b=3, m=24.
--     Companion to R320 (A) for χ(72) high-layer analysis in R322.
-- (2) Unified dispatcher: under Branch II 3-anchor setup + IsKColoring n 4 χ,
--     (χ54 ∈ {χ9, χ18}) ∨ (χ36 ∈ {χ9, χ18}).
--     Proof: ℕ-decidable by_cases on χ54 = χ9 / χ54 = χ18; otherwise delegate
--     to R320 chi54_fourth_forces_chi36_in_9_or_18.
-- This is a compression-dispatch invariant: the high-layer pair {54, 36} is
-- partially classified into {B, C} unconditionally in Branch II.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_48_ne_chi_72_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi54_or_chi36_in_9_or_18

-- Round 322 (§162): Parallel Branch II χ(72)/χ(48) weak dispatcher.
-- Audit confirms χ(48) ≠ χ(27) is NOT directly available from a single
-- bAdicEquation 3 triple (no xz/xy self-loop produces {48, 27}; no general
-- rado triple gives single-triple forcing).
-- Therefore the dispatcher delivers the WEAKER classification for χ(48):
--   (χ72 ∈ {χ9, χ18}) ∨ (χ48 ∈ {χ27, χ9, χ18}).
-- The χ(72) = D fourth-color branch uses (27, 72, 81) + h27_eq_81 to derive
-- χ(72) ≠ χ(27), then R321 universal χ(48) ≠ χ(72) + 4-color exhaustion via
-- omega to place χ(48) ∈ {A, B, C}.
-- Still hLayer-progress: provides a coverage unit for χ(48) (as {A,B,C}, not
-- {B, C}) when χ(72) is not classified into {B, C}.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_27_eq_81_chi9_ne27_chi18_ne9_chi72_or_chi48_in_ABC

-- Round 323 (§163): Combined two-pair coverage + mid-layer χ(24)/χ(30) audit.
-- (1) Universal self-loop χ(20) ≠ χ(30) via triple (30, 20, 30) at n ≥ 30.
--     xz self-loop at b=3, m=10. Counterpart to existing chi_16_ne_chi_24 (m=8).
--     Reusable mid-layer self-loop for future χ(30) = D fourth-color analysis.
-- (2) Combined two-pair coverage theorem: And.intro of R321 + R322 dispatchers
--     under Branch II 3-anchor setup. Unified entry point for hLayer consumers.
-- Audit notes (in §163 docstring): χ(24) ≠ χ(18) is already universal via
-- chi_18_ne_chi_24 (BasicResults, m=6); χ(30) has NO direct single-triple
-- exclusion against {A, B, C} in Branch II (enumeration in docstring).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_20_ne_chi_30_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_two_pair_coverage

-- Round 324 (§164): χ(24)/χ(16) mid-layer dispatcher + 3-coverage packaging.
-- (1) Universal self-loops χ(22) ≠ χ(33) (m=11) and χ(28) ≠ χ(42) (m=14).
--     Future support for R319 χ72=B → χ33≠B and χ72=C → χ42≠C sub-branches.
-- (2) Main dispatcher: under Branch II 3-anchor + IsKColoring n 4 χ,
--       (χ24 ∈ {A, B}) ∨ (χ16 ∈ {A, B, C}).
--     Parallel to R322 weak dispatch; uses universal chi_18_ne_chi_24 for
--     χ24 ≠ C and universal chi_16_ne_chi_24 for χ16 ≠ D := χ24 (fourth color
--     case) + 4-color exhaustion via omega.
-- (3) 3-coverage packaging: And.intro of R323 + R324 main dispatcher.
--     Triple-And invariant for unified hLayer entry.
-- Audit note (in §164 docstring): χ(30) re-confirmed NO direct exclusion.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_22_ne_chi_33_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_28_ne_chi_42_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24_or_chi16_in_ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_three_coverage_units

-- Round 325 (§165): χ(72) sub-branch conditional dispatchers for χ(33)/χ(22)
-- and χ(42)/χ(28) + branch refinement packaging.
-- (A) Under h72_eq_9 (χ72 = B sub-branch): (χ33 ∈ {A, C}) ∨ (χ22 ∈ {A, B, C}).
--     Uses R319 chi72_eq_chi9_forces_chi33_ne_chi9 + R324 chi_22_ne_chi_33
--     + IsKColoring 4 + omega 4-color exhaustion.
-- (B) Under h72_eq_18 (χ72 = C sub-branch): (χ42 ∈ {A, B}) ∨ (χ28 ∈ {A, B, C}).
--     Parallel mechanism with R319 chi72_eq_chi18_forces_chi42_ne_chi18 +
--     R324 chi_28_ne_chi_42.
-- (C) Branch refinement: package (A) and (B) as `χ72 = B → ...` ∧ `χ72 = C → ...`
--     for one-shot consumption by future χ72-branch closure.
-- Audit (in §165 docstring): χ(33) and χ(42) have NO unconditional direct
-- A/B/C exclusion — they are inherently conditional on χ(72)'s value.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq9_chi33_or_chi22_dispatch
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq18_chi42_or_chi28_dispatch
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_branch_refinement

-- Round 326 (§166): χ(54) sub-branch conditional dispatchers for χ(36)/χ(24)
-- + branch refinement packaging. Mirror R325 around the χ(54) ∈ {B, C} side.
-- (1) Universal self-loop χ(24) ≠ χ(36) via (36, 24, 36) at n ≥ 36.
--     xz self-loop at b=3, m=12. Counterpart to R320 chi_36_ne_chi_54 (m=18).
-- (B) Under h54_eq_9 (χ54 = B sub-branch): (χ36 ∈ {A, C}) ∨ (χ24 ∈ {A, B, C}).
--     Uses R320 chi_36_ne_chi_54 + h54_eq_9 ⟹ χ36 ≠ B, then R326 universal
--     chi_24_ne_chi_36 + 4-color exhaustion.
-- (C) Under h54_eq_18 (χ54 = C sub-branch): (χ36 ∈ {A, B}) ∨ (χ24 ∈ {A, B, C}).
--     Parallel mechanism with R319 chi54_eq_chi18_forces_chi36_ne_chi18 +
--     R326 chi_24_ne_chi_36.
-- (D) Branch refinement: package (B) and (C) as `χ54 = B → ...` ∧ `χ54 = C → ...`.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_24_ne_chi_36_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq9_chi36_or_chi24_dispatch
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi36_or_chi24_dispatch
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_branch_refinement

-- Round 327 (§167): Chain coverage integration for χ(54) and χ(72) branches.
-- (1) χ(54)-chain coverage: collapses R321 + R326-B + R326-C into a flat
--     disjunctive invariant (χ36 ∈ {A,B,C}) ∨ (χ24 ∈ {A,B,C}). The R321
--     `χ54 ∈ {B,C}` sub-branches are absorbed via R326 sub-branch dispatchers.
-- (2) χ(72)-chain coverage: combines R322 + R325-A + R325-B into the 3-way
--     invariant (χ48 ∈ {A,B,C}) ∨ R325-A ∨ R325-B.
-- (3) Branch II chain coverage summary: And.intro packaging of (1) + (2) +
--     R324 χ24/χ16 dispatch. Triple-And unified entry point for downstream
--     hLayer consumers.
-- Strategic: the R321/R322 dispatch left-branches (χ54/χ72 ∈ {B,C}) were
-- the only un-collapsed obligations in the high-layer attack. R327 collapses
-- them through R325/R326, delivering flat anchor-set membership statements.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_chain_coverage_36_or_24
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_chain_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chain_coverage_summary

-- Round 328 (§168): Refined χ(54)-chain via R324 χ(24)/χ(16) dispatcher.
-- (1) Refined χ(54)-chain coverage: sharpens R327 chi54_chain_coverage by
--     replacing the χ24 ∈ {A,B,C} disjunct with R324's stricter
--     χ24 ∈ {A,B} ∨ χ16 ∈ {A,B,C}.
--     Net: (χ36 ∈ {A,B,C}) ∨ (χ24 ∈ {A,B}) ∨ (χ16 ∈ {A,B,C}).
-- (2) Refined chain coverage summary: And.intro of refined χ54-chain + R327
--     χ72-chain. Replaces R327 chain_coverage_summary on the χ54 side.
-- Audit (in §168 docstring): χ48 is the highest-value next refinement target
-- (it's a layer position 3·16, whereas χ22/χ28 are non-layer transfer points).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_chain_coverage_refined
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chain_coverage_summary_refined

-- Round 329 (§169): χ(48) branch refinement infrastructure.
-- (1) Universal self-loop χ(32) ≠ χ(48) via (48, 32, 48) at n ≥ 48.
--     xz self-loop at b=3, m=16. Companion infrastructure to R320/R321/R326
--     self-loops (m=18, 24, 12) for χ(48) sub-branch dispatchers.
-- (A) Conditional exclusion `χ48 = A → χ75 ≠ A` via (81, 48, 75) + h27_eq_81.
-- (B) Conditional exclusion `χ48 = B → χ51 ≠ B` via (9, 48, 51).
-- (C) Conditional exclusion `χ48 = C → χ54 ≠ C` via (18, 48, 54).
--     Strategic: combined with R321 (χ54 ∈ {B, C}), forces χ54 = B when χ48 = C.
-- (D) Branch refinement package: And of the three implications.
-- Audit (in §169 docstring): χ32 dispatcher provides no new hLayer info beyond
-- R324 (χ32 is not a layer position and links upward to χ24 only via xy m=8).
#print axioms RadoNumbers.General.bAdicEquation_3_chi_32_ne_chi_48_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi27_forces_chi75_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi9_forces_chi51_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi18_forces_chi54_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_branch_refinement

-- Round 330 (§170): Exploit χ(48) = C strategic cascade.
-- R329's χ48 = C → χ54 ≠ C is now combined with R321 dispatcher + R326-B to
-- eliminate the χ54 = C sub-branch of R321 under χ48 = C.
-- (Target B) chi48_eq18_forces_chi36_or_chi24_refined: 2-disjunct conclusion
--     (χ36 ∈ {B,C}) ∨ (R326-B conclusion). Strictly stronger than R327
--     chi54-chain in the χ48 = C scenario.
-- (Target C) chi48_eq18_forces_refined_chain: 4-disjunct further refined via
--     R324 dispatcher:
--       (χ36 ∈ {B,C}) ∨ (χ36 ∈ {A,C}) ∨ (χ24 ∈ {A,B}) ∨ (χ16 ∈ {A,B,C}).
--     χ24 disjunct narrowed from {A,B,C} (R326-B) to {A,B} (R324).
-- Audit (in §170 docstring): χ48 = A/B future steps require additional anchor
-- exclusions analogous to R326's χ54 ≠ A. Candidate self-loops χ50 ≠ χ75
-- (m=25) and χ34 ≠ χ51 (m=17) noted for R331+.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq18_forces_chi36_or_chi24_refined
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq18_forces_refined_chain

-- Round 331 (§171): χ(48) = A and χ(48) = B weak dispatchers.
-- (1) Universal self-loop χ(50) ≠ χ(75) via (75, 50, 75) at n ≥ 75.
--     xz self-loop at b=3, m=25. Future transfer point for χ48 = A branch.
-- (2) Universal self-loop χ(34) ≠ χ(51) via (51, 34, 51) at n ≥ 51.
--     xz self-loop at b=3, m=17. Future transfer point for χ48 = B branch.
-- (A) χ48 = A weak dispatcher: under R329 χ75 ≠ A + by_cases χ75 = B / C,
--     the fourth-color fallback uses chi_50_ne_chi_75 + 4-color exhaustion.
--     Conclusion: (χ75 ∈ {B, C}) ∨ (χ50 ∈ {A, B, C}).
-- (B) χ48 = B weak dispatcher: parallel via R329 χ51 ≠ B + chi_34_ne_chi_51.
--     Conclusion: (χ51 ∈ {A, C}) ∨ (χ34 ∈ {A, B, C}).
-- Audit (in §171 docstring): χ75 has NO unconditional direct B/C exclusion
-- via single triples; the fourth-color path is the only available route.
#print axioms RadoNumbers.General.bAdicEquation_3_chi_50_ne_chi_75_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_chi_34_ne_chi_51_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq27_chi75_or_chi50_in_BC_or_ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq9_chi51_or_chi34_in_AC_or_ABC

-- Round 332 (§172): Full χ(48) branch integration into χ(72)-chain.
-- (A) chi48_in_ABC_full_coverage: consumes χ48 ∈ ABC and returns 3-way
--     expansion via R331-A (χ48=A), R331-B (χ48=B), R330-refined (χ48=C).
-- (B) chi72_chain_coverage_expanded_chi48: replaces R327 chi72-chain's
--     `χ48 ∈ ABC` terminal disjunct with the (A) expansion. χ72-chain now
--     has no terminal χ48 atom — every leaf is a layer/transfer position.
-- (C) chain_coverage_summary_chi48_expanded: updated Branch II global
--     summary with refined chi54-chain + expanded chi72-chain.
-- Audit (in §172 docstring): best next refinement targets are χ75 ∈ {B,C},
-- χ51 ∈ {A,C}, χ33 ∈ {A,C}, χ42 ∈ {A,B} (all layer positions with universal
-- self-loops already in place from R324/R331).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_in_ABC_full_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_chain_coverage_expanded_chi48
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chain_coverage_summary_chi48_expanded

-- Round 333 (§173): χ(75) terminal branch refinement (under χ48 = A path).
-- (A) Conditional exclusion `χ75 = B → χ72 ≠ B` via triple (9, 72, 75).
--     Strategic: prunes R322 χ72 = B branch under χ75 = B.
-- (B) Conditional exclusion `χ75 = C → χ43 ≠ C` via triple (75, 18, 43).
--     Note: χ43 is non-layer; transfer exclusion only.
-- (C) chi75_branch_refinement packaging: And of (A) and (B) implications.
-- (E) chi48_eq27_branch_expanded: combines R331-A dispatcher with R333 (A)/(B)
--     to enrich χ48 = A coverage. Each χ75 ∈ {B,C} sub-branch carries an
--     additional forced exclusion (χ72 ≠ B or χ43 ≠ C).
-- Audit (in §173 docstring): χ75 refinement is asymmetric — strong on B side
-- (prunes χ72 branch), weak on C side (χ43 non-layer). R334+ should consider
-- χ51, χ33, or χ42 alternatives.
#print axioms RadoNumbers.General.bAdicEquation_3_chi75_eq_chi9_forces_chi72_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi75_eq_chi18_forces_chi43_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi75_branch_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq27_branch_expanded

-- Round 334 (§174): Crossed χ(48) = A / χ(72) = B coverage.
-- Strategic insight: R333-A `χ75 = B → χ72 ≠ B` contrapositively says
-- `χ72 = B → χ75 ≠ B`, eliminating χ75 = B sub-branch from R331-A under
-- the joint χ48 = A ∧ χ72 = B context.
-- (A) chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC: crossed theorem
--     `χ48 = A ∧ χ72 = B → (χ75 = C ∧ χ43 ≠ C) ∨ χ50 ∈ ABC`.
--     Strictly stronger than R331-A / R333 expanded in this joint context.
-- (C) chi48_eq27_chi72_eq9_combined_coverage: combines (A) with R325-A
--     dispatcher (χ33/χ22 coverage under h72_eq_9).
--     2-And cross-chain coverage; first theorem unifying χ48 and χ72 branches
--     under joint hypotheses.
-- Audit (in §174 docstring): χ50 and χ43 fallbacks are structural — cannot be
-- eliminated by single-triple analysis. χ50 is R331-A's 4-color exhaustion
-- fallback; χ43 is non-layer with no immediate hLayer impact.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_forces_chi75C_or_chi50ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq27_chi72_eq9_combined_coverage

-- Round 335 (§175): χ(51) terminal branch refinement + χ48=B crossed coverage.
-- Mirror R333/R334 for the χ48 = B path. R331-B gave (χ51 ∈ {A,C}) ∨ χ34 ∈ ABC;
-- R335 refines χ51 and crosses with χ72 = C.
-- (A) Conditional `χ51 = A → χ44 ≠ A` via triple (51, 27, 44).
-- (B) Conditional `χ51 = C → χ35 ≠ C` via triple (51, 18, 35).
--     Note: χ44, χ35 are non-layer; transfer exclusions.
-- (C) chi51_branch_refinement: And of (A) and (B).
-- (D) chi48_eq9_branch_expanded: enriched R331-B with χ51 sub-branch exclusions.
-- (E) Crossed `χ51 = C ∧ χ72 = C → χ75 ≠ C` via triple (72, 51, 75).
--     Strategic: first χ48=B path cross-chain hook to R333 χ75=C branch.
-- (F) chi48_eq9_chi72_eq18_combined_coverage: enriched (D) with (E) χ75 ≠ C
--     under joint χ48 = B ∧ χ72 = C. Parallel to R334 on χ48=B side.
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi27_forces_chi44_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi18_forces_chi35_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51_branch_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq9_branch_expanded
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi18_chi72_eq_chi18_forces_chi75_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq9_chi72_eq18_combined_coverage

-- Round 336 (§176): Crossed χ(72) sub-branch / χ(48) ∈ ABC expansions.
-- Integrate cross-chain theorems from R333/R334/R335 into branch-specific
-- summary theorems under joint χ72 ∈ {B, C} ∧ χ48 ∈ ABC contexts.
-- (A) chi72_eq9_chi48ABC_crossed_expansion: under χ72=B, dispatch χ48 ∈ ABC
--     via R334 crossed (χ48=A), R335-D expanded (χ48=B), R330 refined (χ48=C).
-- (B) chi72_eq18_chi48ABC_crossed_expansion: under χ72=C, dispatch χ48 ∈ ABC
--     via R333-E expanded (χ48=A), R335-F combined (χ48=B), R330 refined (χ48=C).
-- (C) chi72_eq9_chi48ABC_crossed_with_chi33_coverage: (A) ∧ R325-A χ33/χ22.
-- (D) chi72_eq18_chi48ABC_crossed_with_chi42_coverage: (B) ∧ R325-B χ42/χ28.
-- Audit (in §176 docstring): χ33 ∈ {A,C} and χ42 ∈ {A,B} are layer positions
-- and the natural R337+ refinement targets.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_expansion
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_expansion
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_with_chi33_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_with_chi42_coverage

-- Round 337 (§177): χ(33) and χ(42) terminal branch refinements.
-- (A) Conditional `χ33 = A → χ38 ≠ A` via triple (33, 27, 38).
-- (B) Conditional `χ33 = C → χ29 ≠ C` via triple (33, 18, 29).
-- (C) chi33_branch_refinement packaging.
-- (D) chi72_eq9_branch_expanded_chi33: enriches R325-A with (A)/(B) exclusions.
-- (F-1) Conditional `χ42 = A → χ41 ≠ A` via triple (42, 27, 41).
-- (F-2) Conditional `χ42 = B → χ23 ≠ B` via triple (42, 9, 23).
-- (F-3) chi42_branch_refinement packaging.
-- (F-4) chi72_eq18_branch_expanded_chi42: enriches R325-B with (F-1)/(F-2) exclusions.
-- Note: χ38, χ29, χ41, χ23 all non-layer; transfer exclusions only.
-- Audit (in §177 docstring): cross-chain hook (51, 33, 50) is the most
-- promising for R338+ via χ51=X ∧ χ33=X → χ50≠X.
#print axioms RadoNumbers.General.bAdicEquation_3_chi33_eq_chi27_forces_chi38_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi33_eq_chi18_forces_chi29_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi33_branch_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq9_branch_expanded_chi33
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi27_forces_chi41_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi9_forces_chi23_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi42_branch_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq18_branch_expanded_chi42

-- Round 338 (§178): R337 χ(33)/χ(42) expansions integrated into R336 summaries.
-- (A) chi72_eq9_chi48ABC_crossed_with_chi33_expanded: upgrade of R336 Target C,
--     replacing R325-A side with R337 chi33-expanded (adds χ38/χ29 forced
--     exclusions to χ33 sub-branches).
-- (B) chi72_eq18_chi48ABC_crossed_with_chi42_expanded: upgrade of R336 Target D,
--     replacing R325-B side with R337 chi42-expanded (adds χ41/χ23 forced
--     exclusions to χ42 sub-branches).
-- Audit (in §178 docstring): remaining terminal types include χ50/χ34/χ22/χ28
-- transfer fallbacks (structural 4-color, no further single-triple refinement)
-- and χ75/χ51/χ33/χ42 sub-branches (already R333/R335/R337 refined).
-- Best next: (51, 33, 50) cross-chain hook from R337 audit.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq9_chi48ABC_crossed_with_chi33_expanded
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi72_eq18_chi48ABC_crossed_with_chi42_expanded

-- Round 339 (§179): First double-terminal cross-chain lemma (χ51/χ33/χ50).
-- Triple (51, 33, 50): 51 + 3·33 = 150 = 3·50. Links χ48=B terminal (χ51) +
-- χ72=B terminal (χ33) + χ48=A fallback (χ50).
-- (A) `χ51=A ∧ χ33=A → χ50≠A`. Cross-chain A-color same-terminal exclusion.
-- (B) `χ51=C ∧ χ33=C → χ50≠C`. Cross-chain C-color same-terminal exclusion.
-- (C) chi51_chi33_cross_refinement: And-packaging of (A) and (B).
-- (D) chi48_eq9_chi72_eq9_same_terminal_cross: semantic alias of (C) in the
--     χ48=B ∧ χ72=B joint context.
-- (E-1) chi50ABC_refine_of_chi51A_chi33A: χ50∈ABC + χ51=A ∧ χ33=A ⟹ χ50∈{B,C}.
-- (E-2) chi50ABC_refine_of_chi51C_chi33C: χ50∈ABC + χ51=C ∧ χ33=C ⟹ χ50∈{A,B}.
-- Audit (in §179 docstring): (54, 33, 51) is best next cross-chain target.
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi27_chi33_eq_chi27_forces_chi50_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi18_chi33_eq_chi18_forces_chi50_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51_chi33_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq9_chi72_eq9_same_terminal_cross
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi51A_chi33A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi51C_chi33C

-- Round 340 (§180): Three-chain cross lemma (χ54, χ33, χ51).
-- Triple (54, 33, 51): 54 + 3·33 = 153 = 3·51. First triple bridging
-- χ54-chain, χ72-chain, χ48=B branch via three layer-terminal positions.
-- (A) `χ54=C ∧ χ33=C → χ51≠C`. Primary value (eliminates χ51=C sub-branch).
-- (B) `χ54=A ∧ χ33=A → χ51≠A`. Branch II has χ54≠A globally; generic.
-- (C) `χ54=B ∧ χ33=B → χ51≠B`. Generic for completeness.
-- (D) chi54_chi33_chi51_cross_refinement: And-packaging of A/B/C.
-- (E) chi51AC_refine_of_chi54C_chi33C: refines χ51 ∈ {A, C} to χ51 = A
--     under same-color (C) at χ54 and χ33.
-- (G) chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch: practical
--     three-context pruning. Under χ48 = B ∧ χ54 = C ∧ χ33 = C, the
--     R335-D χ51=C sub-branch is eliminated; only χ51=A path survives
--     (with χ34 ∈ ABC fallback).
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi18_chi33_eq_chi18_forces_chi51_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi27_chi33_eq_chi27_forces_chi51_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi9_chi33_eq_chi9_forces_chi51_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_chi33_chi51_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51AC_refine_of_chi54C_chi33C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq9_chi54_eq18_chi33_eq18_refines_chi51_branch

-- Round 341 (§181): Triple-context Branch II combined coverage
-- (χ54=C ∧ χ72=B ∧ χ48=B). Integrates R340 Target G into the wider triple
-- context, using R337-D dispatcher on χ33 to drive 3-way case analysis.
-- (A) chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage: 3-disjunct over χ33
--     cases (A / C / χ22∈ABC), where the χ33=C disjunct uses R340-G to
--     prune the χ51=C sub-branch.
-- Audit (in §181 docstring): χ54=B has low R340 interaction value (χ33
-- terminal in χ72=B is {A,C}, never B). R338 summary integration is best
-- as a separate χ54=C-parameterized theorem (not an in-place upgrade).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48_eq9_combined_coverage

-- Round 342 (§182): Exploit χ(48)=C / χ(54)=C incompatibility.
-- R329 gave `χ48=C → χ54≠C`. R342 uses this to prune χ48=C from coverages
-- under χ54=C, creating χ54=C-parameterized strengthened summaries.
-- (A) chi48_eq18_and_chi54_eq18_false: direct contradiction.
-- (B) chi54_eq18_chi48ABC_refined_no_chi48C: under χ54=C, χ48∈ABC dispatches
--     to R333-E (χ48=A) or R335-D (χ48=B); χ48=C eliminated.
-- (C) chi54_eq18_chi72_eq9_chi48ABC_combined_coverage: under χ54=C ∧ χ72=B
--     ∧ χ48∈ABC, χ48=A uses R334 crossed; χ48=B uses R341.
-- (D) chi54_eq18_chi72_eq18_chi48ABC_combined_coverage: under χ54=C ∧ χ72=C
--     ∧ χ48∈ABC, χ48=A uses R333-E; χ48=B uses R335-F.
-- Audit (in §182 docstring): R338 integration via χ54=C-parameterized
-- summaries (Targets C/D), not in-place R338 modification.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_eq18_and_chi54_eq18_false
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi48ABC_refined_no_chi48C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi72_eq9_chi48ABC_combined_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi72_eq18_chi48ABC_combined_coverage

-- Round 343 (§183): Compact χ(54)=C-parametrized Branch II summary.
-- (D) chi54_eq18_chi72BC_or_chi48AB: under χ54=C, R322 weak dispatcher's
--     χ48 ∈ ABC fallback collapses to χ48 ∈ {A, B} via R342 Target A's
--     incompatibility. Output: (χ72 ∈ {B,C}) ∨ (χ48 ∈ {A,B}).
-- (H) chi54_eq18_core_summary: pair Target D with R326-C dispatcher
--     (`chi54_eq18_chi36_or_chi24_dispatch`) into a 2-And macro-case
--     summary giving (χ36/χ24 dispatch) ∧ (χ72BC ∨ χ48AB).
-- Audit (in §183 docstring): R322 gives DISJUNCTION χ72BC ∨ χ48ABC, NOT
-- conjunction; the χ54=C summary respects this — Target D produces the
-- correct macro-case split, not a misleading conjunction.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_chi72BC_or_chi48AB
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq18_core_summary

-- Round 344 (§184): Compact χ(54)=B core summary and unified χ(54)∈{B,C} summary.
-- (A) chi54_eq9_core_summary: 2-And under χ54=B using R326-B + R322 weak
--     (no χ48-color elimination since χ54=B doesn't conflict with any χ48 anchor).
-- (B) chi54_BC_core_summary: 2-disjunct over χ54 ∈ {B,C} preserving h54-equality,
--     each carrying the corresponding core summary (R344-A or R343).
-- (C) chi54_or_chi36_core_split: R321-rooted — left side uses R344-B; right side
--     gives χ36 ∈ {B,C} directly.
-- (E-1) chi54_eq9_chi48_eq9_forces_chi66_ne_chi9: triple (54, 48, 66). χ66 layer.
-- (E-2) chi72_eq9_chi54_eq9_forces_chi78_ne_chi9: triple (72, 54, 78). χ78 layer.
-- Audit (in §184 docstring): χ54=B does NOT eliminate any χ48 anchor membership;
-- only same-color (B-B) pair forces a future-layer position (χ66/χ78) exclusion.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq9_core_summary
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_BC_core_summary
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_or_chi36_core_split
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi9_chi48_eq_chi9_forces_chi66_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi72_eq_chi9_chi54_eq_chi9_forces_chi78_ne_chi9

-- Round 345 (§185): χ(54)=B parameterized crossed summaries.
-- Parallel to R342 (χ54=C summaries) but no χ48 elimination since χ54=B has
-- no incompatibility with any χ48 anchor. The χ54=B summaries are semantic
-- aliases of underlying R336/R332 expansions with `_h54_eq_9` context tag.
-- (A) chi54_eq9_chi72_eq9_chi48ABC_combined_coverage: delegates to R336-A.
-- (B) chi54_eq9_chi72_eq18_chi48ABC_combined_coverage: delegates to R336-B.
-- (C) chi54_eq9_chi48ABC_full_expansion: delegates to R332-A.
-- Audit (in §185 docstring): χ54=B is structurally weaker than χ54=C for
-- pruning; R345 retains all three χ48 sub-cases. χ66/χ78 annotations not
-- integrated (would clutter without strengthening dispatcher outputs).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq9_chi72_eq9_chi48ABC_combined_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq9_chi72_eq18_chi48ABC_combined_coverage
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_eq9_chi48ABC_full_expansion

-- Round 346 (§186): Unified χ(54)∈{B,C} parameterized summaries.
-- (A) chi54BC_chi48ABC_parameterized_expansion: χ54 ∈ {B, C} ∧ χ48 ∈ ABC.
--     χ54=B side inlines R333-E + R335-D + R330 (with ≠ annotations,
--     unlike R345-C which delegates to bare R332-A). χ54=C side delegates
--     to R342-B (χ48=C eliminated).
-- (B) chi54BC_chi72_eq9_chi48ABC_parameterized_expansion: χ72=B context.
--     χ54=B side → R345-A. χ54=C side → R342-C.
-- (C) chi54BC_chi72_eq18_chi48ABC_parameterized_expansion: χ72=C context.
--     χ54=B side → R345-B. χ54=C side → R342-D.
-- Audit (in §186 docstring): unified summaries are high-resolution
-- dispatch entry points; do not replace compact R344 core split.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54BC_chi48ABC_parameterized_expansion
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54BC_chi72_eq9_chi48ABC_parameterized_expansion
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54BC_chi72_eq18_chi48ABC_parameterized_expansion

-- Round 347 (§187): Transfer-terminal cross-chain (48, 34, 50).
-- Triple 48 + 3·34 = 150 = 3·50. Links χ48 (R331-B branch anchor) +
-- χ34 (χ48=B path transfer terminal) + χ50 (χ48=A path transfer fallback).
-- Cross-branch constraint via χ34 terminal between χ48=A and χ48=B paths.
-- (B-A) `χ48=A ∧ χ34=A → χ50≠A`.
-- (B-B) `χ48=B ∧ χ34=B → χ50≠B`.
-- (B-C) `χ48=C ∧ χ34=C → χ50≠C`.
-- (B-Pkg) chi48_chi34_chi50_cross_refinement: And of B-A/B/C.
-- (C) chi50ABC_refine_of_chi48A_chi34A: χ50 ∈ ABC → χ50 ∈ {B, C}.
-- (D-B) chi50ABC_refine_of_chi48B_chi34B: χ50 ∈ ABC → χ50 ∈ {A, C}.
-- (D-C) chi50ABC_refine_of_chi48C_chi34C: χ50 ∈ ABC → χ50 ∈ {A, B}.
-- Audit (in §187 docstring): next priority is (42, 36, 50) which links
-- two layer-position terminals (χ42 from χ72=C, χ36 from χ54-chain).
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi27_chi34_eq_chi27_forces_chi50_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi9_chi34_eq_chi9_forces_chi50_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi18_chi34_eq_chi18_forces_chi50_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_chi34_chi50_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi48A_chi34A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi48B_chi34B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi48C_chi34C

-- Round 348 (§188): Layer/transfer cross-chain (42, 36, 50).
-- Triple 42 + 3·36 = 150 = 3·50. Connects TWO layer terminals (χ42 from
-- χ72=C branch, χ36 from χ54-chain) with χ50 transfer fallback. Stronger
-- than R347 (R347 had one layer + two transfers; R348 has two layers + one transfer).
-- (A) `χ42=A ∧ χ36=A → χ50≠A`.
-- (B) `χ42=B ∧ χ36=B → χ50≠B`.
-- (C) `χ42=C ∧ χ36=C → χ50≠C`.
-- (D) chi42_chi36_chi50_cross_refinement: And of A/B/C.
-- (E-A) chi50ABC_refine_of_chi42A_chi36A: χ50 ∈ ABC → χ50 ∈ {B, C}.
-- (E-B) chi50ABC_refine_of_chi42B_chi36B: χ50 ∈ ABC → χ50 ∈ {A, C}.
-- (E-C) chi50ABC_refine_of_chi42C_chi36C: χ50 ∈ ABC → χ50 ∈ {A, B}.
-- Audit (in §188 docstring): under χ54=C ∧ χ72=C, both χ42 ∈ {A, B} and
-- χ36 ∈ {A, B}; same-color cases (A-A or B-B) directly refine χ50.
-- R347 + R348 jointly can force χ50 to a single color via 2-exclusion.
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi27_chi36_eq_chi27_forces_chi50_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi9_chi36_eq_chi9_forces_chi50_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi18_chi36_eq_chi18_forces_chi50_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi42_chi36_chi50_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi42A_chi36A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi42B_chi36B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi42C_chi36C

-- Round 349 (§189): ABC color-refinement helpers + R347+R348 χ(50) closures.
-- Helpers A1-A3 (ABC + 2 exclusions → 1 color):
--   A1: branchII_ABC_refine_neA_neB_to_C
--   A2: branchII_ABC_refine_neA_neC_to_B
--   A3: branchII_ABC_refine_neB_neC_to_A
-- Helpers B1-B3 (ABC + 1 exclusion → 2-color disjunction):
--   B1: branchII_ABC_refine_neA_to_BC
--   B2: branchII_ABC_refine_neB_to_AC
--   B3: branchII_ABC_refine_neC_to_AB
-- 6 χ(50) single-color forcing combinators using R347 + R348 with
-- different exclusion colors:
--   forces_C_of_chi48A_chi34A_and_chi42B_chi36B
--   forces_B_of_chi48A_chi34A_and_chi42C_chi36C
--   forces_C_of_chi48B_chi34B_and_chi42A_chi36A
--   forces_A_of_chi48B_chi34B_and_chi42C_chi36C
--   forces_B_of_chi48C_chi34C_and_chi42A_chi36A
--   forces_A_of_chi48C_chi34C_and_chi42B_chi36B
-- Audit (in §189 docstring): under χ54=C ∧ χ72=C, only A-A or B-B same-color
-- fires R348, so combinators are mostly future-leverage. Next: (36, 38, 50)
-- linking R337-D χ33=A sub-branch terminal χ38 with χ36/χ50.
#print axioms RadoNumbers.General.branchII_ABC_refine_neA_neB_to_C
#print axioms RadoNumbers.General.branchII_ABC_refine_neA_neC_to_B
#print axioms RadoNumbers.General.branchII_ABC_refine_neB_neC_to_A
#print axioms RadoNumbers.General.branchII_ABC_refine_neA_to_BC
#print axioms RadoNumbers.General.branchII_ABC_refine_neB_to_AC
#print axioms RadoNumbers.General.branchII_ABC_refine_neC_to_AB
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_C_of_chi48A_chi34A_and_chi42B_chi36B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_B_of_chi48A_chi34A_and_chi42C_chi36C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_C_of_chi48B_chi34B_and_chi42A_chi36A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_A_of_chi48B_chi34B_and_chi42C_chi36C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_B_of_chi48C_chi34C_and_chi42A_chi36A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_forces_A_of_chi48C_chi34C_and_chi42B_chi36B

-- Round 350 (§190): Third χ(50) cross-chain (36, 38, 50).
-- Triple 36 + 3·38 = 150 = 3·50. Bridges χ36 (χ54-chain layer terminal),
-- χ38 (R337-D χ33=A sub-branch exclusion target), χ50 (transfer fallback).
-- (A) `χ36=A ∧ χ38=A → χ50≠A`.
-- (B) `χ36=B ∧ χ38=B → χ50≠B`.
-- (C) `χ36=C ∧ χ38=C → χ50≠C`.
-- (D) chi36_chi38_chi50_cross_refinement: And of A/B/C.
-- (E-A) chi50ABC_refine_of_chi36A_chi38A: χ50 ∈ ABC → χ50 ∈ {B, C}.
-- (E-B) chi50ABC_refine_of_chi36B_chi38B: χ50 ∈ ABC → χ50 ∈ {A, C}.
-- (E-C) chi50ABC_refine_of_chi36C_chi38C: χ50 ∈ ABC → χ50 ∈ {A, B}.
-- Audit (in §190 docstring): χ38 currently only carries "≠ A" condition
-- under R337-D (χ33=A → χ38≠A); not classified positively. R350 is
-- future-leverage pending χ38 positive classification.
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi27_chi38_eq_chi27_forces_chi50_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi9_chi38_eq_chi9_forces_chi50_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi18_chi38_eq_chi18_forces_chi50_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36_chi38_chi50_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi36A_chi38A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi36B_chi38B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi50ABC_refine_of_chi36C_chi38C

-- Round 351 (§191): Active transfer C-exclusion chain.
-- Three small single-triple C-exclusion lemmas for current transfer terminals:
-- (A) `χ48=C → χ34≠C` via triple (48, 18, 34): 48 + 3·18 = 102 = 3·34.
-- (B) `χ16=C → χ22≠C` via triple (18, 16, 22): 18 + 3·16 = 66 = 3·22.
-- (C) `χ22=C → χ28≠C` via triple (18, 22, 28): 18 + 3·22 = 84 = 3·28.
-- (D) C_transfer_exclusion_pack: And of (A), (B), (C).
-- (F-1) chi34ABC_refine_of_chi48C: under χ48=C, χ34 ∈ ABC → χ34 ∈ {A,B}.
-- (F-2) chi22ABC_refine_of_chi16C: under χ16=C, χ22 ∈ ABC → χ22 ∈ {A,B}.
-- (F-3) chi28ABC_refine_of_chi22C: under χ22=C, χ28 ∈ ABC → χ28 ∈ {A,B}.
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi18_forces_chi34_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi16_eq_chi18_forces_chi22_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi22_eq_chi18_forces_chi28_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_C_transfer_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi34ABC_refine_of_chi48C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi22ABC_refine_of_chi16C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi28ABC_refine_of_chi22C

-- Round 352 (§192): Directional anchor-exclusion packs for χ(48)/χ(16)/χ(22).
-- Audit: "same-target A/B/C family" INVALID — z-position depends on anchor x.
-- True families (directional outputs):
--   χ48: A → χ43 (48, 27, 43); B → χ25 (48, 9, 25); C → χ34 (R351).
--   χ16: A → χ25 (27, 16, 25); B → χ19 (9, 16, 19); C → χ22 (R351).
--   χ22: A → χ31 (27, 22, 31); B → χ25 (9, 22, 25); C → χ28 (R351).
-- 6 new lemmas + 3 packs. χ25 emerges as repeated transfer node (3 sources).
-- Note: chi16_eq_chi27_forces_chi25_ne_chi27 uses h27 not h25 (max position in
-- triple (27, 16, 25) is 27, not z=25).
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi27_forces_chi43_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi9_forces_chi25_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48_anchor_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_chi16_eq_chi27_forces_chi25_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi16_eq_chi9_forces_chi19_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi16_anchor_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_chi22_eq_chi27_forces_chi31_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi22_eq_chi9_forces_chi25_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi22_anchor_exclusion_pack

-- Round 353 (§193): χ(25) convergence-node exclusion / forcing system.
-- (A) chi25_exclusion_pack: 3-And of R352 χ25 exclusions (χ48=B, χ16=A, χ22=B).
-- (B) chi19_eq_chi18_forces_chi25_ne_chi18 via triple (18, 19, 25).
-- (C) chi25_exclusion_pack_extended: 4-And including Target B C-exclusion.
-- (D-1) χ25ABC forces C of χ16=A ∧ χ48=B.
-- (D-2) χ25ABC forces C of χ16=A ∧ χ22=B.
-- (D-3) χ25ABC forces A of χ48=B ∧ χ19=C.
-- (D-4) χ25ABC forces B of χ16=A ∧ χ19=C.
-- Audit (§193 docstring): χ25 ABC unavailable unconditionally; forcing theorems
-- are future leverage awaiting χ25 ∈ ABC dispatcher.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_chi19_eq_chi18_forces_chi25_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25_exclusion_pack_extended
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25ABC_forces_C_of_chi16A_and_chi48B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25ABC_forces_C_of_chi16A_and_chi22B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25ABC_forces_A_of_chi48B_and_chi19C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25ABC_forces_B_of_chi16A_and_chi19C

-- Round 354 (§194): χ(19) transfer-control network.
-- Audit Part 1: χ25 ABC has NO unconditional source.
-- Part 2: χ19 transfer-control network.
-- (B) chi19_eq_chi9_forces_chi22_ne_chi9 via (9, 19, 22): 9 + 3·19 = 66 = 3·22.
-- (C) chi19_eq_chi27_forces_chi28_ne_chi27 via (27, 19, 28): 27 + 3·19 = 84 = 3·28.
-- (D-A) chi10_eq_chi27_forces_chi19_ne_chi27 via (27, 10, 19): 27 + 3·10 = 57 = 3·19.
-- (D-C) chi13_eq_chi18_forces_chi19_ne_chi18 via (18, 13, 19): 18 + 3·13 = 57 = 3·19.
-- (E) chi19_directional_exclusion_pack: A (χ10), B (χ16), C (χ13).
-- (F) chi19_transfer_pack: 4-And of χ19-related implications.
-- (G-1) χ19ABC forces C of χ10=A ∧ χ16=B.
-- (G-2) χ19ABC forces B of χ10=A ∧ χ13=C.
-- (G-3) χ19ABC forces A of χ16=B ∧ χ13=C.
-- Audit Target H: χ19ABC unavailable; forcing theorems are future leverage.
#print axioms RadoNumbers.General.bAdicEquation_3_chi19_eq_chi9_forces_chi22_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi19_eq_chi27_forces_chi28_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi10_eq_chi27_forces_chi19_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi13_eq_chi18_forces_chi19_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19_directional_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19_transfer_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19ABC_forces_C_of_chi10A_chi16B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19ABC_forces_B_of_chi10A_chi13C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19ABC_forces_A_of_chi16B_chi13C

-- Round 355 (§195): Output-node directional networks for χ(31) and χ(43).
-- χ31: completes from R352 A-exclusion (χ22=A) with new B (χ28) and C (χ25).
--   New: chi28_eq_chi9_forces_chi31_ne_chi9 via (9, 28, 31).
--   New: chi25_eq_chi18_forces_chi31_ne_chi18 via (18, 25, 31).
--   chi31_directional_exclusion_pack: A (χ22), B (χ28), C (χ25).
--   3 χ31ABC forcing theorems (forces_C/B/A).
-- χ43: completes from R352 A-exclusion (χ48=A) with new B (χ40) and C (χ37).
--   New: chi40_eq_chi9_forces_chi43_ne_chi9 via (9, 40, 43).
--   New: chi37_eq_chi18_forces_chi43_ne_chi18 via (18, 37, 43).
--   chi43_directional_exclusion_pack: A (χ48), B (χ40), C (χ37).
--   3 χ43ABC forcing theorems.
-- Active value: χ31 high (all upstream nodes χ22/χ28/χ25 are active transfer);
-- χ43 lower (χ40/χ37 not yet active in main chain).
#print axioms RadoNumbers.General.bAdicEquation_3_chi28_eq_chi9_forces_chi31_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi25_eq_chi18_forces_chi31_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31_directional_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_forces_C_of_chi22A_chi28B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_forces_B_of_chi22A_chi25C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_forces_A_of_chi28B_chi25C
#print axioms RadoNumbers.General.bAdicEquation_3_chi40_eq_chi9_forces_chi43_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi37_eq_chi18_forces_chi43_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi43_directional_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi43ABC_forces_C_of_chi48A_chi40B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi43ABC_forces_B_of_chi48A_chi37C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi43ABC_forces_A_of_chi40B_chi37C

-- Round 356 (§196): χ(25)/χ(19)/χ(31) internal network + cross-chain (36, 19, 31).
-- Part 1: C-chain pack χ19=C → χ25≠C and χ25=C → χ31≠C (R353 + R355).
-- Part 2: χ25ABC + χ19=C → χ25 ∈ {A,B}; χ31ABC + χ25=C → χ31 ∈ {A,B}.
-- Part 3: triple (36, 19, 31): 36 + 3·19 = 93 = 3·31. Bridges χ36 / χ19 / χ31.
--   (A) χ36=A ∧ χ19=A → χ31≠A.
--   (B) χ36=B ∧ χ19=B → χ31≠B.
--   (C) χ36=C ∧ χ19=C → χ31≠C.
--   Package And of A/B/C.
--   3 χ31ABC refinements (one-exclusion form, R349 B-helpers).
-- Active value: χ54=C produces χ36 ∈ {A,B}; future χ19 classification
-- activates this cross-chain on χ31 dispatcher.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi19_chi25_chi31_C_chain_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi25ABC_refine_of_chi19C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_refine_of_chi25C
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi27_chi19_eq_chi27_forces_chi31_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi9_chi19_eq_chi9_forces_chi31_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi18_chi19_eq_chi18_forces_chi31_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36_chi19_chi31_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_refine_of_chi36A_chi19A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_refine_of_chi36B_chi19B
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi31ABC_refine_of_chi36C_chi19C

-- Round 358 (§198): Concrete leaf case χ(54)=C ∧ χ(72)=B ∧ χ(48)=B projections.
-- Three focused projection theorems extracted from R341 combined coverage:
-- (A) case_54C_72B_48B_33C: χ33=C branch yields pruned R340-G χ51/χ34 coverage.
--     Conclusion: (χ51=A ∧ χ44≠A) ∨ χ34 ∈ ABC. χ51=C eliminated.
-- (B) case_54C_72B_48B_33A: χ33=A branch yields full R335-D χ51/χ34 coverage.
--     Conclusion: ((χ51=A ∧ χ44≠A) ∨ (χ51=C ∧ χ35≠C)) ∨ χ34 ∈ ABC.
-- (C) case_54C_72B_48B_22ABC: χ22ABC fallback branch yields same R335-D
--     coverage as (B). h22ABC is branch label only.
-- Audit (§198): no direct closure in this leaf case; all branches retain
-- χ34 ∈ ABC fallback. R359 should enter χ34 sub-split and apply R347 cross.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_33C_refines_chi51_chi34
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_33A_refines_chi51_chi34
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_22ABC_refines_chi51_chi34

-- Round 359 (§199): χ(34) ∈ ABC split under concrete leaf χ(48)=B.
-- New χ34 directional outputs (3 exclusion lemmas + pack):
--   χ34=A → χ43≠A via (27, 34, 43): 27 + 3·34 = 129 = 3·43.
--   χ34=B → χ37≠B via (9, 34, 37): 9 + 3·34 = 111 = 3·37.
--   χ34=C → χ40≠C via (18, 34, 40): 18 + 3·34 = 120 = 3·40.
-- Split theorem chi34ABC_split_outputs under h48_eq_9: 3-way over χ34.
--   χ34=B middle branch combines χ37≠B (R359) AND χ50≠B (R347-B).
-- No direct closure; refines χ34ABC into 3 narrower sub-cases.
#print axioms RadoNumbers.General.bAdicEquation_3_chi34_eq_chi27_forces_chi43_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi34_eq_chi9_forces_chi37_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi34_eq_chi18_forces_chi40_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi34_directional_output_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_48B_chi34ABC_split_outputs

-- Round 360 (§200): χ(34)=B focused theorem + χ(51) directional outputs.
-- (Part 1) case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B: And of R359 χ37≠B
--   and R347-B χ50≠B in joint χ48=B ∧ χ34=B context.
-- Audit (Parts 2-3, in §200 docstring): χ50ABC and χ37ABC both unavailable
--   in current χ48=B leaf; χ50≠B and χ37≠B are future leverage.
-- (Part 4) χ51 directional outputs:
--   χ51=B → χ54≠B via (9, 51, 54): 9 + 3·51 = 162 = 3·54.
--   χ51=C → χ57≠C via (18, 51, 57): 18 + 3·51 = 171 = 3·57. χ57 layer (3·19).
--   chi51_directional_output_pack: A → χ44 (R335), B → χ54, C → χ57.
-- (Part 5) case_54C_chi51C_forces_chi57_ne_C: focused alias.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_48B_34B_forces_chi37_ne_B_and_chi50_ne_B
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi9_forces_chi54_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi18_forces_chi57_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51_directional_output_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_chi51C_forces_chi57_ne_C

-- Round 361 (§201): χ(51) double exclusions + layer output pack.
-- (Part 1) chi51C_forces_chi35_and_chi57_ne_C: χ51=C double exclusion
--   (R335 χ35≠C + R360 χ57≠C).
-- (Part 2) chi51_eq_chi27_forces_chi60_ne_chi27: NEW χ51=A → χ60≠A via
--   (27, 51, 60): 27 + 3·51 = 180 = 3·60. χ60 = 3·20 (layer).
-- (Part 2 combined) chi51A_forces_chi44_and_chi60_ne_A: χ51=A double exclusion
--   (R335 χ44≠A + R361 χ60≠A).
-- (Part 3) chi51_layer_output_pack: A → χ60 (R361), B → χ54 (R360), C → χ57 (R360).
-- (Part 4) case_54C_72B_48B_51A_forces_layer60_ne_A: leaf alias.
-- Audit (§201): χ57ABC / χ60ABC unavailable; new exclusions are future leverage.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51C_forces_chi35_and_chi57_ne_C
#print axioms RadoNumbers.General.bAdicEquation_3_chi51_eq_chi27_forces_chi60_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51A_forces_chi44_and_chi60_ne_A
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51_layer_output_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_51A_forces_layer60_ne_A

-- Round 362 (§202): Refined output projections for χ(54)=C ∧ χ(72)=B ∧ χ(48)=B.
-- Integrate R358 + R359 + R361 into 3 refined leaf-output projections,
-- one per R358 sub-branch (χ33=C / χ33=A / χ22ABC). Each enriches:
--   χ51=A sub-branch with χ60 ≠ A (R361)
--   χ51=C sub-branch with χ57 ≠ C (R361)
--   χ34ABC fallback with R359 split (3 sub-cases with forced exclusions)
-- Output frontier (Part 4 audit): 2 layer (χ60, χ57) + 5 transfer (χ44, χ35,
-- χ43, χ37, χ50, χ40) exclusions. No direct closure.
-- R363 should attack χ60 / χ57 layer outputs first.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_33C_refined_outputs
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_33A_refined_outputs
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_22ABC_refined_outputs

-- Round 363 (§203): χ(60) and χ(57) layer-output directional infrastructure.
-- χ60 (R361 A + R363 B/C + pack + leaf B-forcing):
--   χ54=C → χ60≠C via (18, 54, 60): 18 + 3·54 = 180 = 3·60.
--   χ57=B → χ60≠B via (9, 57, 60): 9 + 3·57 = 180 = 3·60.
--   chi60_directional_exclusion_pack: A (R361) + B (new) + C (new).
--   case_54C_51A_chi60ABC_forces_B: high-value current-leaf B-forcing.
-- χ57 (R360 C + R363 A/B + pack + χ51=C refinement):
--   χ48=A → χ57≠A via (27, 48, 57): 27 + 3·48 = 171 = 3·57.
--   χ54=B → χ57≠B via (9, 54, 57): 9 + 3·54 = 171 = 3·57.
--   chi57_directional_exclusion_pack: A (new) + B (new) + C (R360).
--   case_51C_chi57ABC_refines_to_AB: χ57 ∈ {A, B} under χ51=C.
-- χ60 is closer to closure (2 active exclusions in χ51=A path under χ54=C).
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi18_forces_chi60_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi57_eq_chi9_forces_chi60_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi60_directional_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_B
#print axioms RadoNumbers.General.bAdicEquation_3_chi48_eq_chi27_forces_chi57_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi9_forces_chi57_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi57_directional_exclusion_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_51C_chi57ABC_refines_to_AB

-- Round 364 (§204): χ(60)=B downstream cascade + χ(63) directional infrastructure.
-- Part 1-3 (χ60=B downstream):
--   χ60=B → χ63≠B via (9, 60, 63): 9 + 3·60 = 189 = 3·63.
--   χ60=B → χ29≠B via (60, 9, 29): 60 + 3·9 = 87 = 3·29.
--   chi60B_downstream_pack: AND of both.
-- Part 4 (full conditional cascade):
--   case_54C_51A_chi60ABC_forces_chi60B_and_downstream: collapses χ60ABC into
--   χ60=B ∧ χ63≠B ∧ χ29≠B in one step.
-- Part 5 (χ63 directional pack):
--   χ54=A → χ63≠A via (27, 54, 63): 27 + 3·54 = 189 = 3·63.
--   χ57=C → χ63≠C via (18, 57, 63): 18 + 3·57 = 189 = 3·63.
--   chi63_directional_exclusion_pack: A (new) + B (via χ60=B) + C (new).
-- R365 should attack χ63 directional pack consolidation under current leaf.
#print axioms RadoNumbers.General.bAdicEquation_3_chi60_eq_chi9_forces_chi63_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi60_eq_chi9_forces_chi29_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi60B_downstream_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_51A_chi60ABC_forces_chi60B_and_downstream
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi27_forces_chi63_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi57_eq_chi18_forces_chi63_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi63_directional_exclusion_pack

-- Round 365 (§205): χ(63) alternative triggers + fourth-color dispatcher + dichotomy.
-- Part 1 (new triggers):
--   χ36=A → χ63≠A via (81, 36, 63): 81 + 3·36 = 189 = 3·63 (uses h27_eq_81).
--   χ54=C ∧ χ45=C → χ63≠C via (54, 45, 63): 54 + 3·45 = 189 = 3·63.
-- Part 2: case_54C_chi63_trigger_pack — four-trigger bundle.
-- Part 4-A: chi42_ne_chi63_in_monoFree — self-loop (63, 42, 63): 63 + 3·42 = 189 = 3·63.
-- Part 4-B: chi63_fourth_forces_chi42ABC — IsKColoring 4 + χ63 ≠ A,B,C ⟹ χ42 ∈ {A,B,C}.
-- Part 5: case_54C_51A_chi60ABC_chi63_dichotomy — under χ54=C ∧ χ51=A ∧ χ60ABC,
--   χ63 = A ∨ χ63 = C ∨ χ42ABC. Removes χ63ABC three-way split.
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi27_forces_chi63_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi54_eq_chi18_chi45_eq_chi18_forces_chi63_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_chi63_trigger_pack
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_ne_chi63_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi63_fourth_forces_chi42ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_51A_chi60ABC_chi63_dichotomy

-- Round 366 (§206): consume χ(63) dichotomy — branch outputs + χ(42)ABC expansion.
-- Part A-1: χ63=A → χ48≠A via (63, 27, 48): 63 + 3·27 = 144 = 3·48 (redundant in leaf, globally valid).
-- Part A-2: χ63=C → χ39≠C via (63, 18, 39): 63 + 3·18 = 117 = 3·39 (new χ39 exclusion).
-- Part B-1: χ42=C → χ48≠C via (18, 42, 48): 18 + 3·42 = 144 = 3·48 (completes χ42 C-direction).
-- Part B-2: chi42_full_ABC_expansion — bundles R337 F-1/F-2 with new B-1.
-- Audit: no branch closes current leaf; all three branches future-leverage.
#print axioms RadoNumbers.General.bAdicEquation_3_chi63_eq_chi27_forces_chi48_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi63_eq_chi18_forces_chi39_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi18_forces_chi48_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi42_full_ABC_expansion

-- Round 367 (§207): χ(60)/χ(63) line stopping round + final local summary.
-- Stop decision: STOP χ(60)/χ(63) line. R366 produced only future-leverage
-- exclusions; current leaf has χ48=B, so χ48≠A/C and χ39≠C are non-closing.
-- Deliverable: full_chi63_42_summary packages R363+R364+R365+R366 into one
-- statement, the canonical entry point for χ54=C ∧ χ51=A region.
-- R368 pivot: return to χ51=C / χ57 branch (R362 parallel frontier).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_51A_chi60ABC_full_chi63_42_summary

-- Round 368 (§208): pivot to χ(51)=C / χ(57) line — activation audit.
-- Part 1: χ30=A → χ57≠A via (81, 30, 57): 81 + 3·30 = 171 = 3·57 (uses h27_eq_81).
-- Part 2-audit: no B-exclusion triple for χ57 from χ48=B or χ72=B.
-- Part 3: chi57_extended_trigger_pack — adds χ30=A to R361/R363 triggers.
-- Audit conclusion: no second active χ57 exclusion in current leaf.
-- R369 will attempt fourth-color dispatcher (Part 4-B style) + weak dichotomy.
#print axioms RadoNumbers.General.bAdicEquation_3_chi30_eq_chi27_forces_chi57_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi57_extended_trigger_pack

-- Round 369 (§209): χ(57) fourth-color dispatcher + χ(51)=C weak dichotomy.
-- Part A: χ38 ≠ χ57 self-loop via (57, 38, 57): 57 + 3·38 = 171 = 3·57.
-- Part B: chi57_fourth_forces_chi38ABC — mirror of R365 Part 4-B for χ57/χ38.
-- Part C: case_51C_chi57_dichotomy — weak dichotomy: χ57 = A ∨ χ57 = B ∨ χ38ABC.
--   "Weak" because only χ57≠C is forced (R361); A/B branches stay disjunctive.
#print axioms RadoNumbers.General.bAdicEquation_3_chi38_ne_chi57_in_monoFree
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi57_fourth_forces_chi38ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_51C_chi57_dichotomy

-- Round 370 (§210): consume χ(57) weak dichotomy + stop χ(57) line.
-- Part A: χ57=A → χ46≠A via (57, 27, 46): 57 + 3·27 = 138 = 3·46.
-- Part B: χ57=B → χ28≠B via (57, 9, 28): 57 + 3·9 = 84 = 3·28.
-- Part C: case_51C_chi57_dichotomy_outputs — full consumption packaging.
-- Stop decision: STOP χ(57) line. All outputs are future-leverage (no closure
-- in current leaf, χ38ABC has no active consumer). R371 pivots upward.
#print axioms RadoNumbers.General.bAdicEquation_3_chi57_eq_chi27_forces_chi46_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi57_eq_chi9_forces_chi28_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_51C_chi57_dichotomy_outputs

-- Round 371 (§211): χ(51) classification audit + canonical leaf joint summary.
-- Part 2-B: chi51_fourth_forces_chi34ABC — standalone fourth-color dispatcher
--   (mirror of R365 Part 4-B, R369 Part B; uses R331 χ34≠χ51 self-loop).
-- Part 3: case_48B_chi51_dichotomy — flat 3-branch form (χ51=A ∨ χ51=C ∨ χ34ABC).
-- Part 4: case_54C_72B_48B_chi51_joint_summary — canonical top-level summary
--   integrating R361 (χ51=A/C double exclusions) + R359 (χ34=A/C) + R360 (χ34=B).
-- Integration round: no new arithmetic; pure composition.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi51_fourth_forces_chi34ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_48B_chi51_dichotomy
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_chi51_joint_summary

-- Round 372 (§212): refined joint summary with χ(51)-fourth-color tag.
-- Same 3-branch structure as R371 Part 4, but the χ34ABC branch carries
-- the explicit triple `χ51 ≠ A ∧ χ51 ≠ B ∧ χ51 ≠ C` for downstream consumers.
-- Audit: metadata-only refinement; no branch reduction beyond R371.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54C_72B_48B_chi51_joint_summary_with_fourth_tag

-- Round 374 (§213): pivot to χ(54)=B symmetric sibling leaf — macro summary.
-- Part 3: case_48B_chi51_chi34_summary — clean h48=B-only joint summary
--   (extract R371 Part 4 without leaf markers).
-- Part 4: case_54B_72B_48B_macro_summary — 3-conjunct And summary
--   (R326-B χ36/χ24 + R337-D χ33/χ22 + Part 3 χ51/χ34).
-- B/C asymmetry note: χ54=B → χ36∈{A,C} (vs C-leaf χ36∈{A,B}); no χ48 color
-- elimination analogous to R342; current leaf χ48=B already fixed.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_48B_chi51_chi34_summary
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_54B_72B_48B_macro_summary

-- Round 375 (§214): (24, 34, 42) cross-macro coupling chain.
-- Part A: χ24=A ∧ χ34=A → χ42≠A via (24, 34, 42): 24 + 3·34 = 126 = 3·42.
-- Part B: χ24=B ∧ χ34=B → χ42≠B (same triple).
-- Part C: χ24=C ∧ χ34=C → χ42≠C (same triple).
-- Part D: chi24_chi34_chi42_cross_refinement — 3-implication packaging.
-- Active reduction audit: χ42 not classified in current leaf; this is
-- future-leverage cross-chain (2D fourth-color scenario only).
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi27_chi34_eq_chi27_forces_chi42_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi9_chi34_eq_chi9_forces_chi42_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi18_chi34_eq_chi18_forces_chi42_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24_chi34_chi42_cross_refinement

-- Round 377 (§215): χ(36)-half canonical entry — directional outputs + χ36BC focus.
-- Part 2-A: χ36=A → χ45≠A via (27, 36, 45): 27 + 3·36 = 135 = 3·45.
-- Part 2-B: χ36=B → χ39≠B via (9, 36, 39): 9 + 3·36 = 117 = 3·39.
-- Part 2-C: χ36=C → χ42≠C via (18, 36, 42): 18 + 3·36 = 126 = 3·42.
-- Part 2-D: chi36_directional_output_pack — 3-implication packaging.
-- Part 3: chi36BC_outputs — χ36 ∈ {B,C} focused output bundle.
-- Cross-chain audit: R348/R356/R350 cross-chains require χ42/χ19/χ38
-- classification (none active under current R321-upper entry).
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi27_forces_chi45_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi9_forces_chi39_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi18_forces_chi42_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36_directional_output_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36BC_outputs

-- Round 378 (§216): χ54/χ36 same-BC mismatch forces χ24ABC.
-- Part A: chi54C_chi36C_forces_chi24ABC — R326-C excludes χ36=C from direct
--   pair {A,B}; same-C between χ54 and χ36 collapses to χ24ABC fallback.
-- Part B: chi54B_chi36B_forces_chi24ABC — symmetric mismatch for B.
-- Part C: chi54_chi36_same_BC_forces_chi24ABC — bundled same-color pair.
-- Genuine branch reduction: converts χ54 ∧ χ36 same-color into χ24ABC,
-- removing intermediate χ36 ABC possibilities.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54C_chi36C_forces_chi24ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54B_chi36B_forces_chi24ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi54_chi36_same_BC_forces_chi24ABC

-- Round 379 (§217): χ(24)ABC refined consumer + same-BC combined paths.
-- Part 1: chi24ABC_refined_to_AB_or_chi16ABC — alias to R324 main (unconditional).
-- Part 2: case_chi54C_chi36C_chi24_refined — R378A + R324 composition.
-- Part 3: case_chi54B_chi36B_chi24_refined — R378B + R324 composition (symmetric).
-- Branch reduction: same-BC → (χ24∈{A,B} 2-value disjunct) ∨ (χ16ABC 3-value
-- transfer fallback). Net reduction from χ24's original 3-value disjunct.
-- χ16 deeper transfer position; continuing requires R380+ commitment.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24ABC_refined_to_AB_or_chi16ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_chi54C_chi36C_chi24_refined
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_chi54B_chi36B_chi24_refined

-- Round 380 (§218): χ(24)/χ(16) canonical downstream entry.
-- Part 1-A: χ24=A → χ35≠A via (24, 27, 35): 24 + 3·27 = 105 = 3·35.
-- Part 1-B: χ24=B → χ17≠B via (24, 9, 17): 24 + 3·9 = 51 = 3·17.
-- Part 1-C: χ24=C → χ26≠C via (24, 18, 26): 24 + 3·18 = 78 = 3·26.
-- Part 1-D: chi24_directional_output_pack — 3-implication packaging.
-- Part 2: chi24AB_outputs — χ24 ∈ {A,B} focused output.
-- Part 3: chi16ABC_directional_outputs — alias to R352 chi16_anchor_exclusion_pack.
-- Part 4: sameBC_chi24_chi16_downstream_summary — chains R379 input into output.
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi27_forces_chi35_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi9_forces_chi17_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi18_forces_chi26_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24_directional_output_pack
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24AB_outputs
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi16ABC_directional_outputs
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_sameBC_chi24_chi16_downstream_summary

-- Round 381 (§219): χ(16)=C ∧ χ(22)ABC joint refinement.
-- chi16C_chi22ABC_refines_to_AB — under χ16=C ∧ χ22ABC, derive χ22∈{A,B}.
-- Mechanism: R352 χ22≠C + R349 helper neC_to_AB.
-- Conditional reduction: co-occurrence in 2D fourth-color paths.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi16C_chi22ABC_refines_to_AB

-- Round 383 (§220): χ(72)=C sibling leaf macro entry.
-- Part 1: case_72C_chi42_or_chi28_summary — focused alias to R337 F-4.
-- Part 3: case_72C_macro_entry — 2-conjunct And: R321 + Part 1.
-- Active overlap audit: only χ42=B ∧ χ36=B same-color firing (R348-B).
-- R384 will exploit this for χ50≠B enrichment.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_72C_chi42_or_chi28_summary
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_72C_macro_entry

-- Round 384 (§221): active χ(42)=B ∧ χ(36)=B coupling under χ(72)=C.
-- case_72C_36B_chi42_refined: under χ72=C ∧ χ36=B, enrich R337 F-4 with
--   χ50≠B in χ42=B sub-branch via R348-B (`χ42=B ∧ χ36=B → χ50≠B`).
-- Audit: χ50≠B is future leverage; χ50ABC not in active disjunct of
--   χ72=C + χ36=B branch (would need χ48=A path additionally).
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_72C_36B_chi42_refined

-- Round 387 (§222): R386 top frontier-search candidates formalized.
-- (24, 28, 36): 24 + 3·28 = 108 = 3·36; χ24=X ∧ χ28=X → χ36≠X (A/B/C + pack).
-- (42, 34, 48): 42 + 3·34 = 144 = 3·48; χ42=X ∧ χ34=X → χ48≠X (A/B/C + pack).
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi27_chi28_eq_chi27_forces_chi36_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi9_chi28_eq_chi9_forces_chi36_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi24_eq_chi18_chi28_eq_chi18_forces_chi36_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24_chi28_chi36_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi27_chi34_eq_chi27_forces_chi48_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi9_chi34_eq_chi9_forces_chi48_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi42_eq_chi18_chi34_eq_chi18_forces_chi48_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi42_chi34_chi48_cross_refinement

-- Round 388 (§223): Integrate R387 cross-chains into active macro summaries.
-- Part 1: chi48B_chi34B_chi42B_false — 3-conjunct contradiction (BRANCH CLOSURE).
-- Part 2: case_72C_48B_34B_refines_chi42_to_A_or_chi28ABC — 3-disjunct → 2-disjunct.
-- Part 3-B: chi24B_chi28B_chi36BC_forces_chi36C — pins χ36=C in same-B path.
-- Part 3-C: chi24C_chi28C_chi36BC_forces_chi36B — pins χ36=B in same-C path.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48B_chi34B_chi42B_false
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_72C_48B_34B_refines_chi42_to_A_or_chi28ABC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24B_chi28B_chi36BC_forces_chi36C
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi24C_chi28C_chi36BC_forces_chi36B

-- Round 391 (§224): R390 active candidates formalized.
-- (60, 28, 48): A/B/C + pack + closure (5 theorems).
-- (36, 16, 28): A/B/C + pack (4 theorems).
-- (18, 28, 34): C-anchor single variant (1 theorem).
#print axioms RadoNumbers.General.bAdicEquation_3_chi60_eq_chi27_chi28_eq_chi27_forces_chi48_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi60_eq_chi9_chi28_eq_chi9_forces_chi48_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi60_eq_chi18_chi28_eq_chi18_forces_chi48_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi60_chi28_chi48_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi48B_chi60B_chi28B_false
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi27_chi16_eq_chi27_forces_chi28_ne_chi27
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi9_chi16_eq_chi9_forces_chi28_ne_chi9
#print axioms RadoNumbers.General.bAdicEquation_3_chi36_eq_chi18_chi16_eq_chi18_forces_chi28_ne_chi18
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36_chi16_chi28_cross_refinement
#print axioms RadoNumbers.General.bAdicEquation_3_chi28_eq_chi18_forces_chi34_ne_chi18

-- Round 392 (§225): Integrate R391 into R388/R390 active reduced branches.
-- Part 1: case_48B_54C_51A_chi60ABC_chi28ABC_refines_to_AC — χ28ABC → {A,C}.
-- Part 2: case_72C_48B_34B_54C_51A_chi60ABC_refined — R388 + Part 1 composition.
-- Part 3-B: chi36B_chi16B_chi28ABC_refines_to_AC — same-B cross-chain.
-- Part 3-C: chi36C_chi16C_chi28ABC_refines_to_AB — same-C cross-chain.
-- Part 4: chi28C_chi34ABC_refines_to_AB — anchor-driven C exclusion.
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_48B_54C_51A_chi60ABC_chi28ABC_refines_to_AC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_case_72C_48B_34B_54C_51A_chi60ABC_refined
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36B_chi16B_chi28ABC_refines_to_AC
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi36C_chi16C_chi28ABC_refines_to_AB
#print axioms RadoNumbers.General.bAdicEquation_3_branchII_chi28C_chi34ABC_refines_to_AB

-- Generic same-color exclusion theorem used by Branch II support lemmas.
#print axioms RadoNumbers.General.bAdicEquation_3_same_color_excl

-- Round 445 (§R445): the RADO LIFT LEMMA (backward-direction mechanism).
-- radoLiftColoring χ(n) = if b ∣ n then g(n/b) else k (fresh) sends a
-- mono-free k-coloring of [1, M] to a mono-free (k+1)-coloring of [1, b·M].
-- The lift machinery is FULLY KERNEL-PURE (no SAT atom):
--   radoLiftColoring_valid   — validity of the lift
--   radoLiftColoring_avoids  — mono-freeness preserved (KEY THEOREM)
--   rado_lift_exists         — existential lift
--   rado_lower_bound_lift    — R_k(b) > M ⟹ R_{k+1}(b) > b·M
#print axioms RadoNumbers.radoLiftColoring_valid
#print axioms RadoNumbers.radoLiftColoring_avoids
#print axioms RadoNumbers.rado_lift_exists
#print axioms RadoNumbers.rado_lower_bound_lift
-- b=3 tower corollary R_6(3) > 729 = 3^6: the LIFT is atom-free, but this
-- corollary inherits the base-case atom r5_witness_valid_sat (via thm_r5_243).
-- Expected: + r5_witness_valid_sat (honest; R446 discharges the base case).
#print axioms RadoNumbers.exists_monoFreeColoring_b3_k6_729

-- Round 446 (§R446): the FULL b=3 BACKWARD TOWER (∀ k ≥ 5, R_k(3) > 3^k).
-- One kernel-pure Nat.le_induction iterating rado_lower_bound_lift from the
-- base thm_r5_243 (R_5(3) > 243 = 3^5). The lift/induction add NO new axiom;
-- the tower inherits EXACTLY the single base-case atom r5_witness_valid_sat.
--   three_mul_pow            — 3·3^k = 3^(k+1) (kernel-pure power helper)
--   rado_b3_backward_tower   — ∀ k ≥ 5, RadoNumberAtLeast 3 k (3^k + 1)
--   rado_b3_k6_via_tower     — R_6(3) > 729 as a tower instance
--   threshold_backward_b3    — breakdown-regime form (4 < k ⟹ R_k(3) > 3^k)
-- Expected three_mul_pow: kernel-pure [propext, Classical.choice, Quot.sound].
-- Expected tower/wrappers: + r5_witness_valid_sat (honest; base case only).
#print axioms RadoNumbers.three_mul_pow
#print axioms RadoNumbers.rado_b3_backward_tower
#print axioms RadoNumbers.rado_b3_k6_via_tower
#print axioms RadoNumbers.threshold_backward_b3

-- Round 448 (§R448): the GENERAL backward tower (arbitrary b).
-- Generalizes the R446 b=3 induction to every base b ≥ 2: iterating the
-- (general) lift rado_lower_bound_lift from the first-breakdown base case
-- R_{2b-1}(b) > b^{2b-1} — taken as a HYPOTHESIS — gives the entire
-- k ≥ 2b-1 region. This is the complete structural reduction of the
-- threshold conjecture's backward direction.
--   mul_pow_succ_base                       — b·b^k = b^(k+1) (general helper)
--   rado_backward_tower_general             — ∀ k ≥ 2b-1, R_k(b) > b^k (PRIMARY)
--   threshold_backward_from_first_breakdown — 2(b-1) < k ⟹ R_k(b) > b^k (wrapper)
-- CRITICAL: because the base case is a hypothesis, these MUST be kernel-pure
-- [propext, Classical.choice, Quot.sound] with NO r5_witness_valid_sat. If any
-- SAT atom appears, the base abstraction leaked — diagnose.
#print axioms RadoNumbers.mul_pow_succ_base
#print axioms RadoNumbers.rado_backward_tower_general
#print axioms RadoNumbers.threshold_backward_from_first_breakdown
-- b=3 instantiation: re-supplies thm_r5_243 for the general hbase, confirming
-- the general theorem specializes. Inherits ONLY r5_witness_valid_sat (via the
-- base), exactly like the direct b=3 tower — does NOT replace it.
#print axioms RadoNumbers.rado_b3_backward_tower_from_general
