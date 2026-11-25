/-
Conway99.Audit — axiom audit, printed on every build.

Every theorem below must report ONLY the three standard Lean/Mathlib axioms
  propext, Classical.choice, Quot.sound
and in particular must NOT mention `sorryAx`.  A `sorryAx` appearing here
means an unproved claim is being passed off as proved — ground rule 1
territory.  CI/humans: eyeball this section of the build log.

ONE deliberate exception, listed LAST and clearly fenced: the roadmap-4
LRAT pilot (`Conway99.srg6_pilot_unsat` and its Boolean core
`srg6_pilot_check`/`srg6_parse_ok`) INTENTIONALLY additionally reports a
`native_decide` compiler-trust axiom, which on this toolchain (v4.32.2)
prints as a per-invocation generated axiom
  Conway99.srg6_*._native.native_decide.ax_*
(the v4.32 successor of the classic `Lean.ofReduceBool`: `nativeEqTrue`
compiles and runs the Boolean check and asserts `<expr> = true`; the
trusted-base delta is the Lean compiler/evaluator, for one run of the
toolchain's verified LRAT checker).  That is the documented cost of
native reflection (see the header of Conway99/LratPilot.lean and
notes/deep-research-verified-encodings.md); it must appear on those
pilot lines and on NO other theorem below.
-/
import Conway99.LexLeader
import Conway99.Group
import Conway99.T2Lex
import Conway99.GradedInvariant
import Conway99.SRG
import Conway99.Switch2
import Conway99.Transition
import Conway99.CanonicalGeometry
import Conway99.Makhnev
import Conway99.FlagCount
import Conway99.Skeleton
import Conway99.WLOG
import Conway99.Parity
import Conway99.C2
import Conway99.C3
import Conway99.C3Wlog
import Conway99.Matchings
import Conway99.Dirac
import Conway99.Alpha22
import Conway99.LratPilot

#print axioms Conway99.lexLeader_sound
#print axioms Conway99.lexLeader_equisat
#print axioms Conway99.lexLeader_mixed_equisat
#print axioms Conway99.LexLe.prefixLexLe
#print axioms Conway99.prefixLexLe_top_iff
#print axioms Conway99.sigma_partner
#print axioms Conway99.sigmaEquiv_injective2
#print axioms Conway99.sigmaEquiv_mul
#print axioms Conway99.card_labelFinset
#print axioms Conway99.mem_labelFinset_map
#print axioms Conway99.card_edgeSlot
#print axioms Conway99.edgeSlotPerm_comp
#print axioms Conway99.labelPerm_comp
#print axioms Conway99.labelPerm_comm_sigma
#print axioms Conway99.edgeSlotPerm_comm_sigma
#print axioms Conway99.sigmaLabel_ne
#print axioms Conway99.card_bOrbit
#print axioms Conway99.bOrbitPerm_comp
#print axioms Conway99.card_t2Pos
#print axioms Conway99.t2PosPerm_comp
#print axioms Conway99.t2PosOf_edgeSlotPerm
#print axioms Conway99.exists_anchors
#print axioms Conway99.SigmaInvariant.comp
#print axioms Conway99.blockFull_equivariant
#print axioms Conway99.e2_eq_blockFull
#print axioms Conway99.t2Vec_equivariant
#print axioms Conway99.e2_and_eq_t2Vec
#print axioms Conway99.exists_slot_over
#print axioms Conway99.blockFull_falsifiable
#print axioms Conway99.e2_needs_sigmaInvariant
#print axioms Conway99.card_combined
#print axioms Conway99.combPerm_comp
#print axioms Conway99.combVec_equivariant
#print axioms Conway99.unique_common_of_adj
#print axioms Conway99.eq_of_common_adj
#print axioms Conway99.neighborhood_matching
#print axioms Conway99.outside_common_neighbor
#print axioms Conway99.lexLeader_mixed_equisat_order
#print axioms Conway99.length_matchingsL
#print axioms Conway99.length_matchingsL_twelve
#print axioms Conway99.length_matchingsL_range12
#print axioms Conway99.perm_of_mem_matchingsL
#print axioms Conway99.nodup_matchingsL
#print axioms Conway99.matchingsL_complete
#print axioms Conway99.eq_of_sym2_perm_matchingsL
#print axioms Conway99.labelReps_nodup
#print axioms Conway99.labelReps_lex_sorted
#print axioms Conway99.enumLabel_bijective
#print axioms Conway99.root_adj_iff
#print axioms Conway99.root_degree
#print axioms Conway99.nVert_adj_iff
#print axioms Conway99.same_pair_iff_partner
#print axioms Conway99.nVert_matching
#print axioms Conway99.outVert_adj_nVert_iff
#print axioms Conway99.outVert_nDegree
#print axioms Conway99.srg_exists_of_skeleton
#print axioms Conway99.nbhd_orbit_matched
#print axioms Conway99.outside_orbit_coclique
#print axioms Conway99.cycleType_of_orderThree_fpf
#print axioms Conway99.isConj_of_orderThree_fpf
#print axioms Conway99.orbitEquiv_val
#print axioms Conway99.canonicalC3_orbit_apply
#print axioms Conway99.canonicalC3_fpf
#print axioms Conway99.canonicalC3_orderOf
#print axioms Conway99.relabel_to_canonicalC3
#print axioms Conway99.c3_trace_core
#print axioms Conway99.c3_trace_lemma
#print axioms Conway99.orbitPermLift_apply
#print axioms Conway99.orbitPermLift_val
#print axioms Conway99.orbitPermLift_mul
#print axioms Conway99.orbitPermLift_comm_canonicalC3
#print axioms Conway99.orbitPermLift_mul_canonicalC3
#print axioms Conway99.orbitPermLift_orbit
#print axioms Conway99.map_invariant_of_conj
#print axioms Conway99.relabel_graph_to_canonicalC3
#print axioms Conway99.orbitPermLift_map_adj
#print axioms Conway99.orbitIsTriangle_map
#print axioms Conway99.exists_perm_comp_eq
#print axioms Conway99.exists_perm_comp_eq_of_notMem
#print axioms Conway99.card_topBlock
#print axioms Conway99.exists_perm_image_eq_topBlock
#print axioms Conway99.relabel_to_canonical_d
#print axioms Conway99.exists_perm_canonical_cycle
#print axioms Conway99.orbitIsTriangle_map_of_fixed
#print axioms Conway99.relabel_to_canonical_cycle
#print axioms Conway99.isSRGWith_of_iso
#print axioms Conway99.exists_partner_compatible_equiv
-- the ROOTED skeleton WLOG (2026-08-11).  `exists_skeleton_iso_rooted` takes the
-- root as a PARAMETER and its conclusion records `e rootV = v0`, so a quantity
-- computed at the skeleton's root transfers to a PRESCRIBED vertex; the three
-- root-forgetting names below are now corollaries of it and are unchanged.
#print axioms Conway99.exists_skeleton_iso_rooted
#print axioms Conway99.skeletonWLOG_rooted
#print axioms Conway99.exists_skeleton_iso
#print axioms Conway99.skeletonWLOG
#print axioms Conway99.skeletonWLOG_poly
-- ... and the invariance that makes the root equation usable: `D` (FlagCount's
-- canonical-transition counter) is an isomorphism invariant, with no srg
-- hypothesis.  `forall_D_le_of_skeleton_root` is the root-quantifier step —
-- from a bound at the SKELETON's root, over all completions that are srgs, to
-- `∀ x, D G x ≤ m`.  The skeleton-root bound itself is a HYPOTHESIS there (it
-- is the SAT/DRAT certificate plus the informal encoder correspondence,
-- lean/README.md item 7(c)); nothing below asserts it.
#print axioms Conway99.isFlag_iso
#print axioms Conway99.isCanonFlag_iso
#print axioms Conway99.classOf_iso
#print axioms Conway99.canonTransitionsAt_iso
#print axioms Conway99.D_iso
#print axioms Conway99.forall_D_le_of_skeleton_root
#print axioms Conway99.conway99_n3_ge_of_skeleton_root
-- graded/G-invariant composition principle (logs 031, 032, 037)
#print axioms Conway99.SInvariant.and
#print axioms Conway99.SInvariant.all
#print axioms Conway99.sInvariant_exists
#print axioms Conway99.gradedInvariant_equisat
#print axioms Conway99.gradedInvariant_subsumes_order
#print axioms Conway99.gradedInvariant_subsumes_mixed
#print axioms Conway99.agreesOn_sInvariant
#print axioms Conway99.agreesOn_lex_tie
#print axioms Conway99.blockCount_permApply
#print axioms Conway99.countProfile_permApply
#print axioms Conway99.counting_sInvariant
#print axioms Conway99.exists_mem_countProfile_iff
#print axioms Conway99.graded_D_sInvariant
#print axioms Conway99.graded_NBAD_sInvariant
#print axioms Conway99.graded_MAXD_sInvariant
#print axioms Conway99.gradedInvariant_counting_equisat
#print axioms Conway99.agreeCount_permApply
#print axioms Conway99.agreeProfile_permApply
#print axioms Conway99.agree_sInvariant
#print axioms Conway99.graded_c_sInvariant
#print axioms Conway99.gradedInvariant_agree_equisat
-- non-vacuity witnesses (the hypotheses are satisfiable AND load-bearing)
#print axioms Conway99.exBlocksPermuted
#print axioms Conway99.counting_nondegenerate
#print axioms Conway99.counting_needs_blocksPermuted
#print axioms Conway99.agreesOn_nondegenerate
#print axioms Conway99.agreesOn_needs_hv
-- the 2-switch theorem (log 034)
#print axioms Conway99.switchGraph_adj_iff
#print axioms Conway99.switch_not_lambda_one
#print axioms Conway99.not_isSRGWith_of_switch
#print axioms Conway99.not_isSRGWith_switch
-- the rooted transition system: Theorems A, B, C (thread1-transition-system.md)
#print axioms Conway99.two_common
#print axioms Conway99.exists_second_common
#print axioms Conway99.IsPartner.symm
#print axioms Conway99.IsLabel.symm
#print axioms Conway99.exists_unique_partner
#print axioms Conway99.partner_unique
#print axioms Conway99.partner_injective
#print axioms Conway99.apex_unique
#print axioms Conway99.exists_apex
#print axioms Conway99.exists_label
#print axioms Conway99.label_unique
#print axioms Conway99.label_not_matched
#print axioms Conway99.label_ne_of_partner
#print axioms Conway99.no_three_circuit_core
#print axioms Conway99.no_three_circuit
#print axioms Conway99.partner_bipartite
#print axioms Conway99.line_through_of_two_nbrs
#print axioms Conway99.line_off_root_meets_once
#print axioms Conway99.shared_index_apex
#print axioms Conway99.shared_index_no_outside_triangle
#print axioms Conway99.outside_line_stays_outside
#print axioms Conway99.line_split_count
#print axioms Conway99.line_split_99
#print axioms Conway99.line_split_243
-- the canonical geometry: planes, the far corner, the Hall gap (logs 033-035)
#print axioms Conway99.CanonicalAt.transfer
#print axioms Conway99.not_adj_of_ne_class
#print axioms Conway99.canonical_class_rule
#print axioms Conway99.corner_unique
#print axioms Conway99.plane_set_unique
#print axioms Conway99.common_neighbors_not_adj
#print axioms Conway99.chordless_quadrangle
#print axioms Conway99.grid_of_canonical
#print axioms Conway99.IsFarCorner.symm
#print axioms Conway99.apexes_not_adj
#print axioms Conway99.exists_far_corner
#print axioms Conway99.far_corner_unique
#print axioms Conway99.exists_unique_far_corner
#print axioms Conway99.grid_far_point
#print axioms Conway99.far_corner_well_defined
#print axioms Conway99.far_corner_well_defined_of_canonical
-- the STS completion: the block set and the EXACT COVER (log 042)
#print axioms Conway99.IsFarCorner.adj_left
#print axioms Conway99.IsFarCorner.adj_right
#print axioms Conway99.IsDiagonal.symm
#print axioms Conway99.IsDiagonal.third
#print axioms Conway99.IsDiagonal.pairwise
#print axioms Conway99.exists_grid_of_canonical
#print axioms Conway99.grid_far_corner_eq
#print axioms Conway99.grid_isDiagonal
#print axioms Conway99.IsDiagonal.rotate
#print axioms Conway99.diagonal_unique
#print axioms Conway99.adj_of_mem_line
#print axioms Conway99.not_adj_of_mem_diagonal
#print axioms Conway99.line_pair_form
#print axioms Conway99.diagonal_pair_form
#print axioms Conway99.block_card
#print axioms Conway99.IsDiagonal.in_plane
#print axioms Conway99.block_pair_form
#print axioms Conway99.sts_exact_cover
-- each plane carries the 12-block AG(2,3) design, and is closed
#print axioms Conway99.ag23_card
#print axioms Conway99.ag23_block_card
#print axioms Conway99.ag23_exact_cover
#print axioms Conway99.ag23_mem_of_ne
#print axioms Conway99.plane_blocks_are
#print axioms Conway99.plane_blocks_isBlock
#print axioms Conway99.plane_blocks_card
#print axioms Conway99.plane_blocks_closed
#print axioms Conway99.two_choose_two
#print axioms Conway99.sts_blocks_per_point
#print axioms Conway99.sts_block_count
#print axioms Conway99.sts_blocks_99_243
#print axioms Conway99.hall_fraction
#print axioms Conway99.hall_fraction_99_243
-- the Diophantine side: (i) unbounded, what the application needs ...
#print axioms Conway99.not_pow_three_of_between
#print axioms Conway99.not_pow_three_of_not_dvd
#print axioms Conway99.family_factorisations
#print axioms Conway99.family_not_power_of_three
#print axioms Conway99.family_not_power_of_three_dvd
#print axioms Conway99.family_powers_of_three
-- ... and (ii) the FINITE VERIFICATION (n <= 12), which is not the general
-- Diophantine theorem and must not be quoted as one
#print axioms Conway99.diophantine_finite_check
#print axioms Conway99.diophantine_of_exp_le
-- non-vacuity witnesses for the canonical geometry (Paley(9))
#print axioms Conway99.paley9_srg
#print axioms Conway99.paley9_isGrid
#print axioms Conway99.paley9_canonicalAt
#print axioms Conway99.paley9_canonical_premises_fire
#print axioms Conway99.paley9_grid_of_canonical
#print axioms Conway99.paley9_farCorner
#print axioms Conway99.paley9_translate_adj
#print axioms Conway99.paley9_canonical
#print axioms Conway99.paley9_isDiagonal
#print axioms Conway99.paley9_blocks_both_kinds
#print axioms Conway99.paley9_sts_exact_cover
#print axioms Conway99.paley9_planeBlocks_card
-- COROLLARY C1 (log 046): Makhnev's condition (*) IS canonicality.
-- The BACKBONE first (lambda=1 only): the join of two disjoint triangles is a
-- matching, so the join count lies in {0,1,2,3}.
#print axioms Conway99.eq_third_of_adj_two
#print axioms Conway99.cross_at_most_one
#print axioms Conway99.lines_meet_once
#print axioms Conway99.lines_through_point_no_cross
#print axioms Conway99.mem_joinSet
#print axioms Conway99.join_card_le_three
#print axioms Conway99.two_le_join_card
#print axioms Conway99.join_card_eq_three
#print axioms Conway99.adj_third_of_join_card
-- ... the two renderings of (*), and that they AGREE (so the relational form is
-- Makhnev's sentence, not an editorial choice) ...
#print axioms Conway99.makhnevStar_iff_card
-- ... the flag construction shared by both directions ...
#print axioms Conway99.flag_disjoint
#print axioms Conway99.apex_eq_label_of_adj
-- ... the backbone at its true strength: "every edge lies in at most one
-- triangle" (UniqueTriangle), which lambda=1 supplies and which twoJoin -- not
-- an SRG -- also satisfies.  That weakening is what lets FlagCount's fibre
-- count be INSTANTIATED at m = 2 (see below).
#print axioms Conway99.uniqueTriangle_of_srg
#print axioms Conway99.cross_at_most_one_ut
#print axioms Conway99.twoJoin_uniqueTriangle
-- ... and C1 itself.  `adj_third_of_canonicalAt` is LOCAL: only canonicality at
-- the single root p' is used.  NOTE: Makhnev's Theorem 2 (no srg(99,14,1,2)
-- satisfies (*)) is CITED, never proved or assumed; nothing here bears on
-- existence.  THEOREM C's counting identity is not formalized in THIS file;
-- it is proved in FlagCount.lean (theoremC_n1 / theoremC_n3, audited below).
#print axioms Conway99.adj_third_of_canonicalAt
#print axioms Conway99.canonicalAt_of_makhnevStar
#print axioms Conway99.join_card_eq_two_of_not_canonical
#print axioms Conway99.makhnevStar_iff_canonical
#print axioms Conway99.makhnevStarCard_iff_canonical
#print axioms Conway99.makhnevStar_iff_canonical_99
#print axioms Conway99.makhnevStar_iff_canonical_243
-- ... non-vacuity: Paley(9) satisfies (*) AND its premises fire on a concrete
-- prism (two disjoint triangles joined by three edges) ...
#print axioms Conway99.paley9_makhnevStar
#print axioms Conway99.paley9_makhnevStarCard
#print axioms Conway99.paley9_prism
#print axioms Conway99.paley9_makhnevStar_fires
-- ... and falsifiability: on the 2-join (two disjoint triangles joined by
-- exactly two edges) BOTH renderings of (*) are FALSE, with join count 2.
#print axioms Conway99.twoJoin_config
#print axioms Conway99.twoJoin_join_card
#print axioms Conway99.twoJoin_not_makhnevStar
#print axioms Conway99.twoJoin_not_makhnevStarCard
-- the Dirac-type perfect matching lemma (proved outright, no literature input)
#print axioms Conway99.not_isTutteViolator_of_card_eq_two_mul
#print axioms Conway99.exists_perfectMatching_of_card_eq_two_mul
#print axioms Conway99.exists_perfectMatching_of_card_le_two_mul_degree
#print axioms Conway99.exists_perfectMatching_of_card_eq_fourteen
-- ... and its non-vacuity witness (the 4-cycle, where the degree bound is tight)
#print axioms Conway99.C4_degree_eq
#print axioms Conway99.C4_hypotheses
#print axioms Conway99.C4_exists_perfectMatching
-- the alpha=22 zero-power theorem (log 043): "C2" holds in EVERY 2-(22,4,2)
-- design, so the filter removes nothing.  Lemma 1 (`card_heavy_le`) is
-- UNCONDITIONAL -- read its statement: no hypothesis on block intersections.
#print axioms Conway99.mem_blocksThrough
#print axioms Conway99.card_heavy_le
#print axioms Conway99.replication_mul
#print axioms Conway99.partnerGraph_adj_iff
#print axioms Conway99.card_blocksThrough_eq
#print axioms Conway99.card_le_degree_partnerGraph
#print axioms Conway99.exists_perfectMatching_partnerGraph
#print axioms Conway99.card_blocksThrough_22_4_2
#print axioms Conway99.card_partner_vertices_22_4_2
#print axioms Conway99.ten_le_partner_degree
#print axioms Conway99.c2_always_holds
-- ... its non-vacuity witnesses: the Fano plane, and the Fano plane DOUBLED
-- (a design with every block REPEATED, on which the theorem actually fires)
#print axioms Conway99.fanoBlocks_card
#print axioms Conway99.fano_pair_count
#print axioms Conway99.fano_isDesign
#print axioms Conway99.fano_heavy_empty
#print axioms Conway99.fano2_pair_count
#print axioms Conway99.fano2_isDesign
#print axioms Conway99.fano2_replication
#print axioms Conway99.fano2_partner_perfectMatching
-- ... including that Lemma 1's LHS is INHABITED on the doubled Fano plane
-- (count 1 against the allowed 2), so it is not bounded at an empty set
#print axioms Conway99.fano2_heavy_card
#print axioms Conway99.fano2_heavy_nonempty
#print axioms Conway99.fano2_partner_adj
#print axioms Conway99.fano2_partner_not_adj
#print axioms Conway99.fano2_degree_eq_four
#print axioms Conway99.fano2_three_le_degree
-- ... and the ARITHMETIC of the derivation chain.  These are numeric
-- identities ONLY: they do not assert the Hoffman ratio bound (absent from
-- this Mathlib) and they do not assert any value of alpha.
#print axioms Conway99.alpha22_chain_arithmetic
#print axioms Conway99.hoffman_ratio_value_99
#print axioms Conway99.hoffman_ratio_value_27

-- FlagCount.lean — THEOREM C, the flag-counting identity (log 046's
-- hand proof, machine-checked; log 047 for the evidence layer).  The FIBRE
-- COUNT is the content: over an ordered pair of disjoint triangles whose
-- join has m edges there are exactly m^2 - m flags, so 6 per ordered prism
-- (12 per prism) and 2 per ordered 2-join (4 per 2-join).  Its hypothesis
-- is UniqueTriangle, not the srg axioms.
#print axioms Conway99.cross_at_most_one_finset
#print axioms Conway99.card_crossEnds
#print axioms Conway99.card_fiberOf
#print axioms Conway99.exists_flagImage
#print axioms Conway99.flagImage_unique
#print axioms Conway99.flagImage_join_three
#print axioms Conway99.flagImage_join_two
#print axioms Conway99.flag_double_count
#print axioms Conway99.card_canonFlagSet
#print axioms Conway99.card_badFlagSet
-- ... the two factors of 2 (ordered/unordered pairs; flags/transitions)
#print axioms Conway99.card_ordJoinPairs
#print axioms Conway99.card_image_classOf
#print axioms Conway99.card_flagsAt
#print axioms Conway99.card_transitionsAt
-- ... THEOREM C itself, division-free
#print axioms Conway99.theoremC_n1
#print axioms Conway99.theoremC_n3
-- ... the published cross-check (Reimbayev Prop. 5(6)), DERIVED not cited
#print axioms Conway99.reimbayev_prop5
-- ... and the Makhnev bridge, re-proved by counting
#print axioms Conway99.canonicalAt_iff_forall_flag
#print axioms Conway99.D_le
#print axioms Conway99.D_eq_card_transitionsAt
#print axioms Conway99.canonicalAt_of_D_eq
#print axioms Conway99.D_eq_iff_canonicalAt
#print axioms Conway99.n3_eq_zero_iff_canonical
#print axioms Conway99.n3_eq_zero_iff_makhnevStar
-- ... the v = 99 corollaries.  `D(x) <= 77` is a HYPOTHESIS of these
-- theorems (it is the SAT certificate of logs 031-032, not a Lean proof).
#print axioms Conway99.conway99_sum_D_le
#print axioms Conway99.conway99_sum_D_le'
#print axioms Conway99.conway99_n1_le
#print axioms Conway99.conway99_n3_ge
-- ... NON-VACUITY, DERIVED grade: Paley(9) has 6 prisms and no 2-joins.
-- These follow FROM the identity, so they CANNOT falsify its constants;
-- the agreement with brute force is checked outside Lean.
#print axioms Conway99.paley9_D
#print axioms Conway99.paley9_sum_D
#print axioms Conway99.paley9_n1
#print axioms Conway99.paley9_n3
-- ... NON-VACUITY, FALSIFIABLE grade (log 047): every one of these is a
-- `decide` off the definitions, paired with the value the theorems predict.
-- BOTH fibre branches are covered -- m = 3 on Paley(9), m = 2 on twoJoin,
-- the latter possible only because card_fiberOf's hypothesis is
-- UniqueTriangle.  No member of the srg(1+2r^2,2r,1,2) family can witness
-- m = 2: both known members are canonical, so both have n3 = 0.
#print axioms Conway99.paley9_prism_fibre
#print axioms Conway99.paley9_prism_fibre_pred
#print axioms Conway99.twoJoin_fibre
#print axioms Conway99.twoJoin_fibre_pred
#print axioms Conway99.paley9_flagsAt_card
#print axioms Conway99.paley9_canonFlagsAt_card
#print axioms Conway99.paley9_D_computed

-- Parity.lean — the PER-ROOT PARITY obstruction (log 032's "`D = 83` is the
-- only unachievable value", proved).  A non-canonical transition never stands
-- alone at its own root, so the bad count at a root is never 1 and
-- `D(x) = 2r(r-1) - 1` is impossible.  This DOUBLES log 031's rung: the same
-- certificate `D(x) <= 83` that gives `n3 >= 51` gives `n3 >= 99`.
-- `hD` / `hskel` remain HYPOTHESES (the SAT certificate), as in FlagCount F13.
#print axioms Conway99.canonTransitionsAt_subset
#print axioms Conway99.card_badTransitionsAt_add
#print axioms Conway99.exists_second_bad_transition
#print axioms Conway99.card_badTransitionsAt_ne_one
#print axioms Conway99.D_ne_pred
#print axioms Conway99.conway99_D_ne_83
#print axioms Conway99.conway99_three_dvd_n3
#print axioms Conway99.conway99_n3_ge_51
#print axioms Conway99.conway99_n3_ge_99
#print axioms Conway99.conway99_n3_ge_99_of_not_canonical
#print axioms Conway99.conway99_n3_ge_99_of_skeleton_root
-- ... and the falsifiable `decide`s pinning the root split on Paley(9)
#print axioms Conway99.paley9_transitionsAt_card
#print axioms Conway99.paley9_badTransitionsAt_card

/- ─────────────────────────────────────────────────────────────────────────
   INTENTIONAL AXIOM-DELTA SECTION — roadmap-4 LRAT pilot ONLY.
   The three lines below are EXPECTED to additionally report a
   `native_decide` compiler-trust axiom, printed on this toolchain as
   `Conway99.srg6_*._native.native_decide.ax_*` (v4.32's per-invocation
   form of the classic `Lean.ofReduceBool`): the Lean compiler is
   trusted for one Boolean run of the toolchain's verified LRAT checker.
   This is the documented compiler-trust delta of Conway99/LratPilot.lean
   — accepted and confined to this fence.  If ANY `*.native_decide.ax_*`
   axiom (or `Lean.ofReduceBool` / `Lean.trustCompiler`) ever appears on
   a line ABOVE this fence, that is a bug: fail the audit.
   ───────────────────────────────────────────────────────────────────── -/
#print axioms Conway99.srg6_parse_ok
#print axioms Conway99.srg6_pilot_check
#print axioms Conway99.srg6_pilot_unsat
