# Conway-99 Lean formalization

Machine-checked mathematics for the SAT attack in this repository.
Lean 4 + Mathlib, pinned to release `v4.32.2` (toolchain and dependency
locked by `lean-toolchain` / `lake-manifest.json`).

## Build & check

```bash
cd lean
lake build            # compiles everything AND prints the axiom audit
lake exe export_frame # tabulates the frame from the proven definitions
cd .. && python3 src/crosscheck_lean.py   # byte-for-byte vs symmetry.py
```

## What is PROVED

Sorry-free, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`); `Conway99/Audit.lean` prints the axiom base of every
headline theorem on every build, so a smuggled `sorry` fails loudly.
ONE fenced exception: the road-map-4 LRAT pilot (`LratPilot.lean`)
additionally carries the `native_decide` compiler-trust axiom — see the
audit's explicitly-annotated final section and road-map item 4 below.

### `LexLeader.lean` — soundness of the symmetry breaking (the keystone)

- `LexLe` — the exact first-difference order the CNF lex clauses encode
  (`false < true`, position 0 most significant).
- `lexLeader_sound` — for any finite, nonempty, composition-closed set `S`
  of position permutations and any `S`-invariant constraint predicate,
  every satisfying assignment yields one that also satisfies ALL
  lex-leader constraints for `S` (the orbit lex-minimum).  Inverses are
  not needed; invariance is only needed in the forward direction.
- `lexLeader_equisat` / `lexLeader_mixed_equisat` — adding lex-leader
  constraints for ANY subset of `S`, each with its own prefix window
  (`PrefixLexLe`) — precisely the `(element, prefix)` batches
  `src/symbreak.py` emits — preserves satisfiability EXACTLY.  A future
  UNSAT on a symmetry-broken instance therefore transfers to the original
  problem, modulo the two cross-checked correspondences below.
- `lexLeader_mixed_equisat_order` — the same, under an ARBITRARY fixed
  comparison order (proved by conjugating with the order permutation):
  exactly what `campaign.py gen --sb-order s2first/nested` emits for the
  v2/v3 per-orbit instances.  One order per instance; the proof makes
  clear why mixing orders within an instance would be unsound (each
  order has its own orbit minimum).

### `GradedInvariant.lean` — the `G`-invariant composition principle (logs 031/032/037)

The soundness principle the graded canonical campaign runs on
(`notes/math/graded-canonical.md` §1).  THREE certified theorems depend on
it — log 031's canonical-transition exclusion and log 032's Theorems A and
B — and until now it existed only as a prose Proposition plus exhaustive
computational checks (`g(POS) = POS` over all 645,120 group elements).
This file is the Lean name to cite.

- **It is an INSTANTIATION, not new mathematics, and the file says so.**
  `lexLeader_sound` was ALREADY stated for an arbitrary constraint
  predicate `C` with an arbitrary invariance hypothesis `hC`; it never
  cared what `C` says.  `SInvariant S C` names that hypothesis;
  `SInvariant.and` / `SInvariant.all` prove invariance is closed under
  (finite) conjunction — the one mathematical step the Proposition adds
  beyond `lexLeader_sound` — and `gradedInvariant_equisat` is the
  Proposition in the shape the campaign uses: for `S`-invariant `Base` and
  `S`-invariant `Extra`, adding lex-leader constraints for ANY subset of
  `S`, each with ITS OWN prefix window, under ANY single comparison order,
  preserves satisfiability EXACTLY.
- **It visibly subsumes both earlier lex theorems.**
  `gradedInvariant_subsumes_order` re-derives
  `lexLeader_mixed_equisat_order` from it (take `Extra = True`) and
  `gradedInvariant_subsumes_mixed` re-derives `lexLeader_mixed_equisat`
  (take also `o = 1`) — so the composition principle is a strict
  generalization of both, not a parallel statement.
- **The two SHAPES every campaign family takes, each proved `S`-invariant
  ONCE.**
  - FIXED-SET (`AgreesOn`, `agreesOn_sInvariant`): "the assignment agrees
    with a fixed partial assignment `v` on a position set `U`", for `U`
    setwise invariant and `v` invariant along the action.  This is log
    031's 924 canonical unit clauses (84 positive + 840 negative).  Its
    two hypotheses are also exactly those of log 032 §9's Proposition,
    whose conclusion — every position of `U` is a lex TIE, so ordering `U`
    first is a no-op — is proved here as `agreesOn_lex_tie`.
  - COUNTING (`blockCount`, `countProfile`, `counting_sInvariant`):
    positions partitioned into blocks permuted by `S` (for the campaign,
    the 14 canonical sextets), and ANY predicate whatsoever on the
    MULTISET of per-block counts.  `countProfile_permApply` is the orbit
    invariance of the profile; the named corollaries
    `graded_D_sInvariant`, `graded_NBAD_sInvariant`,
    `graded_MAXD_sInvariant` are log 032's three families verbatim (the
    certified `D` rungs are `--dmin`, a cardinality over the 84 POSITIVE
    slots, so they are genuine true-counts), and log 037's second-root
    cells `SEC ≤ j` / `SEC ≥ t` are predicates of the same kind.
    `gradedInvariant_counting_equisat` assembles principle + counting
    family into the exact statement the ladder consumes.
  - AGREEMENT COUNTING (`agreeCount`, `agreeProfile`,
    `agree_sInvariant`): the same with agreement against a fixed reference
    valuation in place of "true".  `graded_canonical.py`'s fourth family,
    `--cmin` (`c ≥ m` over the 924 MIXED-SIGN canonical literals), is
    **not** a function of the true-count profile — a true-count cannot see
    the 840 negative literals' agreements — so it needs this shape;
    `graded_c_sInvariant` / `gradedInvariant_agree_equisat` cover it, and
    `countProfile_eq_agreeProfile` shows the plain counting shape is the
    special case `v ≡ true`.  (No certified rung uses `--cmin`; the family
    is covered so that the theorem carries every family in the code, not
    only the ones that happened to be refuted.)
- **The hypotheses are not vacuous, and they are load-bearing.**  All of
  the above is TRUE for degenerate data (`U = ∅`, `blk ≡ none`, `β` empty,
  `P` constant) and would then say nothing, so the file discharges that
  reading in `T2Lex.lean`'s style: `exBlocksPermuted` /
  `agreesOn_nondegenerate` exhibit the hypotheses jointly satisfied by a
  NON-identity element with a NON-constant valuation and a falsifiable
  constraint; `counting_nondegenerate` separates two assignments with the
  SAME total true-count, so the counting predicate really reads the block
  structure; and `counting_needs_blocksPermuted` / `agreesOn_needs_hv`
  give explicit counterexamples showing each invariance hypothesis cannot
  be dropped — which is what makes the exhaustive 645,120-element Python
  checks (V3, S2) load-bearing rather than decorative.
- `sInvariant_exists` names the Proposition's other hypothesis — that a
  family presented as the projection of an (assignment, auxiliary)
  relation is extendable on its auxiliaries, which is what `cardtest`
  checks exhaustively for the sequential counter on the Python side.  The
  lemma records where that hypothesis enters; it does not prove it OF any
  particular encoding.
- **What this does NOT do, stated exactly** (same discipline as
  `T2Lex.lean`): the file is abstract in `n`, in `S` and in the
  predicates.  That the CNF clause sets project onto these predicates, and
  that the concrete blocks really are permuted by `G` (`BlocksPermuted` is
  a HYPOTHESIS here; on the Python side it is log 037's exhaustive
  645,120-element check S2), stay exactly where they were — informal items
  1 and 7 below.

### `Group.lean` — the residual group S₂≀S₇, generically

All statements quantified over ALL 645,120 wreath elements (π, s);
structural proofs, no per-element enumeration.

- `sigmaEquiv π s : Equiv.Perm (Fin 14)` — every wreath element is a
  permutation of N(0), with explicit computable inverse.
- `pairOf_sigma` / `sigma_partner` — blocks move by π and partners stay
  partners: the matching, hence the skeleton, is preserved.
- `sigmaEquiv_injective2` — distinct (π, s) give distinct permutations:
  the residual group has at least 7!·2⁷ = 645,120 elements.
- `sigmaEquiv_mul` — the wreath multiplication law; `edgeSlotPerm_comp` —
  the induced edge-slot action respects composition.  Together these give
  the closure hypothesis `lexLeader_sound` consumes.
- `card_labelFinset = 84`, `card_edgeSlot = 3486`; `labelPerm` /
  `edgeSlotPerm` — the induced actions on the 84 labels and the 3,486
  edge slots are permutations, for every group element.

### `T2Lex.lean` — the t2 / B-orbit lex layer (C2 campaign)

The obligation set of `notes/t2-lex-design.md` §2.3, proved.  The design
moves the lex-leader layer onto the 861 `t2` indicator variables (one per
unordered pair of σ-orbits on the 84 outside labels), in front of the 3,486
edge slots, so `lexLeader_mixed_equisat(_order)` gets instantiated at
n = 4,347.  That instantiation is free — `LexLeader.lean` is abstract in `n`,
in the position type, in `S` and in `C` — but the group action on the new
positions and the equivariance of the t2 DEFINITION are not.  Both are here.

- **σ is central, structurally.** `sigmaSign` is the wreath element
  σ = (π = id, s = 1⁷) that `src/c2_instance.py` prescribes;
  `sigma_sigmaSign_comp_left`/`_right` show both composition orders give
  (π, ¬s), hence `labelPerm_comm_sigma` and `edgeSlotPerm_comm_sigma`.  This
  is the design §2.1 fact (there machine-checked by enumerating all 645,120
  elements) proved once for all of them.  `labelPerm_comp` — the `labelPerm`
  analogue of `edgeSlotPerm_comp` — is the workhorse.
- **42 B-orbits.** `sigmaLabel` is σ's label action `L`; `sigmaLabel_ne`
  proves it is FIXED-POINT-FREE (a label joins two distinct matched pairs,
  so it cannot equal its own partner-swap), `sigmaLabel_sigmaLabel` that it
  is an involution, and `card_bOrbit : Fintype.card BOrbit = 42` follows by
  fibrewise counting on the 84 labels — matching `enrich_clauses`'
  `assert len(reps) == 42`.
- **861 t2 positions, with the action.** `bOrbitPerm` / `bOrbitPerm_comp`
  (every wreath element permutes the B-orbits, respecting composition) and
  `T2Pos` / `card_t2Pos = 861` / `t2PosPerm` / `t2PosPerm_comp`, all in the
  `labelPerm` / `edgeSlotPerm` mold.  Composition-closure of the image is
  exactly the `hmul` hypothesis `lexLeader_sound` consumes, now on the new
  positions; the direction is fixed by the theorem (`Q` is built from the
  same forward action as `P`, the error design §5.4 warns about).
- **THE NEW LEMMA PAIR** (the design's crux — the E2 definition is NOT
  equivariant on arbitrary assignments, and the E2 CLAUSE SET is provably
  not invariant at all):
  - `blockFull_equivariant` — the block form (all four edge slots between
    two B-orbits) is equivariant UNCONDITIONALLY: for every assignment,
    every wreath element, every position.  It is stated fibrewise over the
    projection `t2PosOf` (edge slot ↦ B-orbit pair, `t2PosOf_edgeSlotPerm`),
    so no representative is ever named and no σ-hypothesis is used.
  - `e2_eq_blockFull` — on σ-INVARIANT assignments E2's two-slot
    conjunction equals the block form.  The hypothesis is `SigmaInvariant`,
    stated exactly as `c2_instance.py`'s `eq_clauses` enforce it
    (`∀ q, X (σ q) = X q`; the 42 σ-fixed slots make the ∀-form and the
    1,722 clause pairs equivalent).  The two anchors are arbitrary labels of
    the two orbits — the CNF's min-index `r_a`, `r_b` are one instance —
    which is what removes the anchor-flip problem.  `e2_and_eq_t2Vec` is the
    design's Boolean shape of the same statement.
  - Corollaries: `t2Vec_equivariant` (the `hC` shape on the t2 half:
    `t2Vec (X ∘ P_g) = (t2Vec X) ∘ Q_g`) and `SigmaInvariant.comp` (the
    σ-invariant set is mapped to itself — centrality again), plus the
    non-vacuity guard `exists_anchors`.
  - **Both lemmas are guarded against the degenerate reading.**  `blockFull`
    is a bounded ∀, so an empty fibre would make `blockFull_equivariant` a
    tautology about nothing: `exists_slot_over` proves every fibre is
    inhabited and `blockFull_falsifiable` that the predicate can fail.  And
    `e2_needs_sigmaInvariant` proves — in Lean, for EVERY t2 position at
    once — that `e2_eq_blockFull`'s σ-hypothesis cannot be dropped: there is
    always an assignment satisfying E2's two anchor slots but not the block
    form.  That upgrades the design §3 counterexample and the Python negative
    control (0/200 vs 200/200) from a test to a theorem.
- **The combined 4,347-position frame.**  `combPerm` (= `Q_g` on the t2 half,
  `P_g` on the edge half — `c2_instance.combined_perm`), `combPerm_comp` (the
  `hmul` hypothesis on the COMBINED type, not one half at a time — both
  halves move under the same wreath multiplication law, so `g ↦ combPerm g`
  is a homomorphism), `card_combined = 861 + 3,486 = 4,347`, and
  `combVec_equivariant`, the `hC` shape on the full position vector.  The
  numbering `T2Pos ⊕ EdgeSlot ≃ Fin 4347` is the one link still outside Lean
  (item 6b).
- **What this does NOT do, stated exactly.**  `hC` itself is NOT proved and
  stays at today's epistemic level: that the edge half of the constraint set
  is preserved by the wreath action remains test-verified on the Python side
  and informal (item 6 below).  The pair above removes the NEW risk the t2
  layer introduces — that a DEFINED variable's definition might fail to be
  equivariant, which without the σ-equalities it demonstrably does — and
  nothing else.

### `C2.lean` — the involution's canonical form (asymmetry campaign)

Given the Makhnev–Minakova one-fixed-vertex theorem as a hypothesis
(literature input, clearly marked), `nbhd_orbit_matched` proves every
σ-orbit on the fixed vertex's neighborhood is a matched pair — rooted
there, the involution IS the partner-swap `c2_instance.py` prescribes —
and `outside_orbit_coclique` proves the outside orbits are cocliques
(the E1 enrichment's 42 forced-false variables).  The C2 claim chain's
mathematical links are now all machine-checked except the literature
input itself.

### `C3.lean` — the order-3 canonical form and trace lemma (asymmetry campaign)

Two layers, mirroring `C2.lean`'s discipline (real mathematics proved;
literature inputs enter only as clearly-marked hypotheses, never `sorry`):

- **Conjugacy WLOG — fully proved, no literature input.**
  `cycleType_of_orderThree_fpf`: a fixed-point-free order-3 permutation
  of a 99-element type has cycle type 3³³; `isConj_of_orderThree_fpf`:
  any two such permutations are conjugate; `canonicalC3` (with
  `canonicalC3_orderOf` / `canonicalC3_fpf` / `canonicalC3_orbit_apply` /
  `orbitEquiv_val`): the concrete g = (0 1 2)(3 4 5)⋯(96 97 98) of
  `src/c3_instance.py` — vertex 3i+a ↦ 3i+((a+1) mod 3) — is such a
  permutation; `relabel_to_canonicalC3`: every fixed-point-free order-3
  σ on `Fin 99` is carried to g by a relabeling p (p ∘ σ = g ∘ p, i.e.
  p σ p⁻¹ = g).  This machine-checks the group-theoretic core of the
  WLOG in `c3_instance.py`'s docstring; the last glue sentence — that
  the relabeled graph p(G) is then g-invariant with the same srg
  parameters — is now ALSO proved: `relabel_graph_to_canonicalC3`
  (`C3Wlog.lean`, 2026-08-08, closing former informal item 4b).
  (That an order-3
  automorphism of a Conway graph IS fixed-point-free is Behbahani–Lam
  2011 — a campaign-level literature input; these theorems take it as
  the hypothesis `hfpf` and never claim it.)
- **Trace lemma t ∈ {6,13,20,27} — hypothesis form.** `c3_trace_core`
  proves the arithmetic core sorry-free: t ≤ 33, a ≤ 32 and
  2t + 114 = 7a force (t,a) ∈ {(6,18), (13,20), (20,22), (27,24)}.
  `c3_trace_lemma` concludes t ∈ {6,13,20,27} — the four `--fix-t`
  slices of `c3_instance.py` exhaust the C3 search — from hypotheses
  (`hcard`/`hmem`/`hsum`) that are EXACTLY the equitable-partition
  spectral containment package: the 33 quotient eigenvalues are 14
  (exactly once) plus 32 values in {3,−4}, and the trace is their sum
  (standard algebraic graph theory — Godsil–Royle ch. 9; applied to srg
  orbit matrices by Behbahani 2009 and Behbahani–Lam 2011) — plus the
  definitional facts tr C = 2t and t ≤ 33.  CAVEAT, stated exactly: the
  spectral containment itself is NOT proved in Lean — it enters as a
  literature-input hypothesis (informal list below), the same way
  Makhnev–Minakova enters `C2.lean` via `hfix`, and nothing stronger
  than the containment is assumed.

### `C3Wlog.lean` — the D-cycle campaign's relabeling WLOGs (asymmetry campaign)

The two WLOGs of notes/c3-dcycle-design.md §4, machine-checked in the
`relabel_to_canonicalC3` mold — the formalization the design's risk 1
demanded before any headline claim rides on `--canon-d` instances or
`(t, L)` cubes.  No literature input anywhere in this file.

- **Centralizer action.** `orbitPermLift π` lifts an orbit permutation
  π ∈ S₃₃ to `Fin 99` (3i+a ↦ 3π(i)+a; `orbitPermLift_apply` /
  `orbitPermLift_val`); it CENTRALIZES the canonical g
  (`orbitPermLift_comm_canonicalC3`, group form
  `orbitPermLift_mul_canonicalC3`), acts on orbit indices exactly as π
  (`orbitPermLift_orbit`), and lifting is a homomorphism
  (`orbitPermLift_mul` — composed WLOG relabelings are again lifts).
  Generic transport: a permutation-relabeled graph is isomorphic to the
  original (`mapPermIso`); conjugation carries σ-invariance to
  g-invariance (`map_invariant_of_conj`); orbit-blocks transport by π
  with offsets untouched (`orbitPermLift_map_adj` — the bridge along
  which every orbit-level derived structure, d-pattern and D-graph
  included, moves), specialised to the triangle indicator by
  `orbitIsTriangle` / `orbitIsTriangle_map`.
- **WLOG-C (d-canonicalization — soundness of `--canon-d`).**
  `exists_perm_image_eq_topBlock`: any T ⊆ Fin 33 with |T| = t ≤ 33 is
  carried onto the top block {33−t..32} (`topBlock`, `card_topBlock`) by
  some π ∈ S₃₃.  Campaign corollary `relabel_to_canonical_d`: any
  g-invariant graph on `Fin 99` with triangle-orbit set T is isomorphic,
  via the centralizing lift `orbitPermLift π`, to a still-g-invariant
  graph whose triangle-orbit set is exactly `topBlock t` — the 33 canon-d
  units of `c3_instance.py` lose no g-invariant models.
- **WLOG-D (cycle canonicalization — soundness of the `(t, L)` cube
  units).**  Workhorse `exists_perm_comp_eq` (S_α is transitive on
  injections β ↪ α) and its relative form `exists_perm_comp_eq_of_notMem`
  (two enumerations avoiding a frozen block are related by a permutation
  fixing the block POINTWISE — deliberately general: level-2 sub-splits
  freeze `topBlock t ∪ {0..L−1}` and instantiate the SAME lemma).
  `exists_perm_canonical_cycle`: given any graph D on Fin 33 and an
  injective enumeration `c : Fin L → Fin 33` of a closed walk avoiding
  the top block (consecutive vertices D-adjacent, Fin-L addition
  supplying the wrap), some π fixes `topBlock t` pointwise (stronger
  than the design's setwise requirement) and relabels the cycle to
  (0, 1, …, L−1): the relabeled D carries the L canonical edges
  {s, s+1} plus wrap {0, L−1} — the positive w2 cube units of
  `c3_cubes.py`.  Campaign corollary `relabel_to_canonical_cycle`: the
  lift of that π preserves g-invariance AND the canonical d-pattern
  (`orbitIsTriangle_map_of_fixed`) while putting the D-cycle in
  canonical position, with the block-transport clause included.
- **Graph-level conjugacy WLOG (bonus).** `relabel_graph_to_canonicalC3`
  composes `relabel_to_canonicalC3`, `mapPermIso`,
  `map_invariant_of_conj` and `isSRGWith_of_iso`: every srg(99,14,1,2)
  with a fixed-point-free order-3 automorphism is isomorphic to a
  `canonicalC3`-invariant srg(99,14,1,2).  Former informal item 4(b) —
  now a theorem.
- **CAVEATS, stated exactly** (the D-cycle chain links that stay
  semantic — see informal item 5): WLOG-D consumes the cycle enumeration
  `c` as a HYPOTHESIS; that a model's D-graph is 2-regular and decomposes
  into cycles ≥ 3 with a well-defined cycle through orbit 0 of allowed
  length (D8 + the E3 enrichment) is NOT proved here.  Likewise the
  identification of the abstract D with the counting-derived |S_ij| = 2
  relation of a concrete model is the E3 clause layer (definitional
  counting on top of the proved block transport), not a Lean theorem.

### `Matchings.lean` — the cube cover, machine-checked

The partition-soundness link at EVERY level of the cube tree: the
enumerator `matchingsL` (structural mirror of `cubes.py:matchings`)
provably lists every perfect matching of a duplicate-free list
(`matchingsL_complete` — proved directly, not by counting), lists only
perfect matchings (`perm_of_mem_matchingsL`), lists them without
duplicates even at the unordered-cube level
(`eq_of_sym2_perm_matchingsL` — added by the adversarial verifier after
catching that list-level Nodup alone doesn't give cube distinctness),
and has length (2k−1)!! — exactly 10,395 entries for a 12-element block
(`length_matchingsL_range12`).  The Lean↔Python enumerator agreement is
cross-checked order-exactly over the full list via a position-weighted
checksum (26593306125996701025 on both sides); cube ids in every ledger
index this shared order.

### `SRG.lean` — the skeleton's local structure

For ANY strongly regular graph with λ = 1 (μ = 2 where stated), via
Mathlib's standard `SimpleGraph.IsSRGWith`:

- `neighborhood_matching` — λ=1 ⇒ every vertex's neighborhood induces a
  perfect matching (why N(0) carries `{1,2},…,{13,14}`).
- `eq_of_common_adj` — an adjacent pair's common neighbor is unique
  (why no outside vertex attaches to both ends of a matched pair).
- `outside_common_neighbor` — λ=1, μ=2 ⇒ each non-matched pair of a
  neighborhood has exactly one other common neighbor, and it lies OUTSIDE
  the neighborhood (the key step of the outside-vertex ↔ pair bijection).

### `Switch2.lean` — the 2-switch theorem (log 034)

> **THEOREM.**  No degree-preserving 2-switch on an srg(v,k,1,2) yields an
> srg(v,k,1,2).

The theorem that fell out of the audit of the external srg(243,22,1,2)
deliverable, and the reason its 4.03-million-trial 2-switch hunt for a
non-canonical member of the λ=1, μ=2 family had **provably zero power**
under any seed.  Proved from Mathlib's `SimpleGraph.IsSRGWith` with λ = 1,
μ = 2; no literature input anywhere in the file.

- `switchGraph G a b c d` — delete `{a,b}` and `{c,d}`, insert `{a,c}` and
  `{b,d}` — with the `SwitchRemoved` / `SwitchAdded` pair predicates and a
  `DecidableRel` instance, so `IsSRGWith` applies to it directly.
- `switch_not_lambda_one` is the sharp statement and it proves MORE than
  the headline: the switched graph cannot satisfy λ = 1 **at all** — no
  assumption on its vertex count, degree or μ.  It is stated for ANY graph
  whose adjacency is the switch of `G`'s (`hspec`), with
  `switchGraph_adj_iff` the concrete witness that keeps it non-vacuous.
- `not_isSRGWith_of_switch` / `not_isSRGWith_switch` are the headline
  corollary, in spec form and on the concrete switched graph.
- Proof, following log 034 line for line: the apex `t` of the deleted edge
  `{a,b}` avoids `c` and `d`, so the switch leaves `N(t)` untouched; the
  SURVIVING edge `{a,t}` loses its unique common neighbour `b`, so λ = 1
  in the switched graph forces `t ~ c`, and symmetrically `t ~ d`; then
  `{a,b}` and `{c,d}` are two edges of the perfect matching on `N(t)`
  (λ = 1), whence `a ≁ d` and `b ≁ c`; μ = 2 gives the non-adjacent pair
  `a`, `c` a SECOND common neighbour `s`, which by the previous step is
  neither `b` nor `d` and therefore survives the switch — so the NEW edge
  `{a,c}` has two common neighbours `s` and `t`, contradicting λ = 1.
- The hypotheses are exactly a valid switch: `{a,b}` and `{c,d}` disjoint
  edges (the four distinctness facts) with `a ≁ c` and `b ≁ d`.
  "Degree-preserving" is the standard name for the operation — each of the
  four vertices loses one incidence and gains one — and is not needed as
  an assumption.

### `Dirac.lean` — the Dirac-type perfect matching lemma

> **THEOREM.**  A graph on an EVEN number of vertices whose every degree is
> at least half the vertex count has a perfect matching.

A general graph-theory tool, **proved outright, not quoted**: the matching
shadow of Dirac's 1952 Hamiltonicity theorem.  No literature input, no
`sorry`, nothing Conway-specific in the file — so it appears NOWHERE in the
informal list, and no theorem downstream of it is conditional on anything.

**This is a genuine addition, not a re-proof of something Mathlib already
has.**  Mathlib v4.32.2 supplies `SimpleGraph.tutte` (the ⟺ with "no Tutte
violator") but **no Dirac-type minimum-degree matching lemma** — checked
2026-08-11: nothing under `Mathlib/Combinatorics/` so much as mentions Dirac.
The missing step is exactly `not_isTutteViolator_of_card_eq_two_mul`; `tutte`
then does the rest in one line.

- `not_isTutteViolator_of_card_eq_two_mul` is the sharp form and carries all
  the content: on `2 * m` vertices with minimum degree `≥ m`, **no** vertex
  set `u` is a Tutte violator.  Everything else is Mathlib's
  `SimpleGraph.tutte` applied to it.
- `exists_perfectMatching_of_card_eq_two_mul` (generic `m`),
  `exists_perfectMatching_of_card_le_two_mul_degree` (the `Even (card V)` +
  `card V ≤ 2 * degree v` form, no division anywhere) and
  `exists_perfectMatching_of_card_eq_fourteen` (the concrete 14/7 instance,
  which NOTHING consumes — the `14` that actually arises downstream is the
  replication number of a 2-(22,4,2) design, not a neighbourhood size, and
  `Alpha22.lean` reaches it through the generic `2 * m` form) are the
  corollaries.
- Proof.  Every component of `G - u` has `≥ δ - |u| + 1` vertices (a
  surviving vertex keeps `≥ δ - |u|` neighbours, all in its own component).
  For `|u| = 0` that leaves at most ONE component, and the odd-component
  count has the parity of the vertex count — even — so there are none.
  For `1 ≤ |u| ≤ m`, a violation would need `(|u|+1)(m-|u|+1) ≤ 2m-|u|`,
  which after writing `|u| = a+1`, `m = a+1+s` reads `a·s + 2 ≤ 1`.  For
  `|u| > m` there are simply fewer than `|u|` vertices left.  Evenness is
  used only in the first case, and only through the parity of the count.
- Non-vacuity: `C4` (the 4-cycle on `Fin 4`, as "different parity") meets the
  hypotheses TIGHTLY — `C4_degree_eq` shows every degree is exactly `2 = 4/2`
  — `C4_hypotheses` is the `decide`-checked satisfiability of the hypothesis
  set, and `C4_exists_perfectMatching` runs the theorem on it.

### `Alpha22.lean` — the α = 22 branch's "C2" filter has ZERO POWER (log 043)

> **THEOREM.**  In EVERY 2-(22,4,2) design whatsoever, at every point `s`, the
> 14 blocks through `s` pair up into 7 couples meeting exactly in `{s}`.

The audit of log 043 upgraded an external collaborator's **C1 ⟹ C2** (correct,
and not disputed) to an unconditional statement: the partner-degree bound needs
no C1 hypothesis, so C2 can never fail and a search filtering by it removes
nothing.  Counting the three zero-power hunts log 034 found in the same
author's srg(243,22,1,2) deliverable, this is a **fourth provably zero-power
search from that author**, and it is zero-power over the entire 2-(22,4,2)
design universe rather than merely over the C1 survivors (log 043's own
comparison).  It is **not** the project's first universe-wide zero-power
result — `not_isSRGWith_switch` (`Switch2.lean`) already quantifies over every
srg(v,k,1,2) and every valid 2-switch.

- `card_heavy_le` is **the heart of the file**: for an arbitrary indexed
  block family with `k`-point blocks and every point-pair in exactly `λ`
  blocks, at most `(k-1)(λ-1)` of the other blocks through `s` meet a given
  block through `s` in ≥ 2 points.  *Read the statement*: `blocks` is an
  arbitrary function and NO hypothesis about block intersections appears.
  (Proof: such a block shares a point `x ≠ s` with the fixed one; `k-1`
  choices of `x`, and `{s,x}` lies in `λ` blocks of which the fixed one is
  already one.  Union bound over `x`.)
  On provenance: this is an elementary union bound and **no literature search
  has been made for it**, so "ours" can only mean "not taken from the
  deliverable under audit" (which gets the same `10` out of C1 instead).  Like
  `Dirac.lean`'s Dirac bound it is proved outright rather than quoted, so
  nothing downstream turns on the answer.
- Designs are presented with an **indexed** block family `blocks : ι → Finset P`,
  so repeated and heavily-overlapping blocks are inside the scope — dropping
  them would quietly narrow the universe the zero-power claim is about.
- `replication_mul` proves the double count `r(k-1) = (v-1)λ`, so `r = 14` at
  (22,4,2) is **derived, not assumed** (`card_blocksThrough_22_4_2`).
- `card_le_degree_partnerGraph` is the subtraction-free min-degree corollary
  `r ≤ deg + 1 + (k-1)(λ-1)`; `ten_le_partner_degree` instantiates it to
  `deg ≥ 10` and `exists_perfectMatching_partnerGraph` composes it with
  `Dirac.lean`.  `c2_always_holds` is the headline.
- Non-vacuity: the Fano plane 2-(7,3,1) (`fano_isDesign`, and
  `fano_heavy_empty` runs Lemma 1 on it to the sharp value `0` — but that is a
  bound on an EMPTY set, so it does not on its own show anything fires), and —
  the important one — **the Fano plane DOUBLED**, a 2-(7,3,2) design on 14
  indices with every block repeated, `r = 6 = 2·3`, where the matching theorem
  actually fires (`fano2_partner_perfectMatching`).  There
  `fano2_heavy_nonempty` shows Lemma 1's left-hand side is INHABITED (count 1,
  against the allowed 2), and the partner graph is shown to have an edge
  (`fano2_partner_adj`) AND a non-edge (`fano2_partner_not_adj`: the two copies
  of a line are not partners), so the conclusion is not free.  How much slack:
  that partner graph is `K_{2,2,2}` with all degrees `4` against the `3` the
  theorem needs (`fano2_degree_eq_four`), so the witness shows the hypotheses
  FIRE, not that they are tight — tightness is `Dirac.lean`'s `C4`.

**CAVEATS — the scope, stated because a "zero power" headline is easy to
over-read, and the file's docstring says all of this at length.**  The Hoffman
ratio bound is not available in this Mathlib, so the v = 99 chain
"α ≤ 22 ⟹ a 2-(22,4,2) design" is a literature input — but a WEAKER kind of
one than `C2.lean`'s `hfix`, which is a hypothesis of Lean theorems and so
makes its consumers visibly conditional: the α = 22 chain is carried by **no
Lean statement in this file at all** (no theorem there mentions v = 99 or Γ),
and is registered in informal item 4(c) below.  No α value is computed
(`α(BvLS(243)) = 45`, `α(srg(27,10,1,5)) = 6 < 9` are log 043 Python
computations, cited); `alpha22_chain_arithmetic` / `hoffman_ratio_value_99` /
`hoffman_ratio_value_27` are **numeric identities only**; nothing here bears
on whether srg(99,14,1,2) exists — the theorem is about 2-(22,4,2) designs and
its only role in the project is to retire a search filter; and no 2-(22,4,2)
design is exhibited in Lean (they do exist — log 043 enumerates 738,100
distinct ones in a single stratum, 800/800 sampled machine-verified as genuine
BIBDs — but that is a Python computation, and the headline holds either way,
since over an empty class a filter also removes nothing).

### `Transition.lean` — the rooted transition system: Theorems A, B, C (logs 031–038)

The local reformulation every canonicality result in this project is
stated in (`notes/math/thread1-transition-system.md` §1–2), and the three
theorems that note grades PROVED.  All for an arbitrary
`G.IsSRGWith n k 1 μ` (Theorems A and C) or `n k 1 2` (Theorem B) — nothing
is specific to v = 99.

Setting, relationally (no `Classical.choice`-extracted maps — each relation
is proved functional, so downstream files may use whatever labelling they
already have, the same discipline as `Switch2.lean`'s `hspec` form):

- `IsPartner G x a a'` — `a′` is `a`'s partner in the matching `Γ[N(x)]`;
  `exists_unique_partner`, `partner_unique`, `partner_injective`.
- `IsLabel G x a b z` — `z = z_ab` is the outside vertex labelled `{a,b}`;
  `exists_label`, `label_unique` (the `μ = 2` bijection of the note's
  Lemma 2), `label_not_matched` (no outside vertex meets both ends of a
  matched pair), `label_ne_of_partner`.
- `IsApex G u w t` / `IsLine G p q r` — the third point of the line on an
  edge, and a line as a triangle; `apex_unique` is λ = 1.
- `two_common` / `exists_second_common` — the two halves of μ = 2 (a
  non-adjacent pair has at most, and at least, two common neighbours).
  These two are the workhorses of both new files.

> **THEOREM A — no 3-circuits.** `no_three_circuit`: for `a,b,c ∈ N(x)`
> pairwise non-matched, the transitions `M_a(b) = c`, `M_b(a) = c`,
> `M_c(a) = b` cannot all hold; every circuit of the transition system has
> length ≥ 4.

Uses **λ = 1 only** (μ = 2 enters only via the existence of the labels,
which is a hypothesis).  `no_three_circuit_core` is the label-free form:
if two outside neighbours of `a ∈ N(x)` are adjacent, their apex is `a`,
so nothing outside `N[x]` is adjacent to both.

> **THEOREM B — the `a`/`a′` bipartite perfect matching.**
> `partner_bipartite`: for a matched pair `{a,a′}` and an outside vertex
> `z ~ a`, there is EXACTLY ONE outside vertex adjacent to both `a′` and
> `z`.

Symmetric in `a` and `a′`, so the induced bipartite graph between
`N(a) ∖ N[x]` and `N(a′) ∖ N[x]` is a perfect matching.  λ = 1 gives
`a′ ≁ z`; μ = 2 gives the second common neighbour of `a′` and `z` besides
`a`; λ = 1 again puts it outside `N[x]`.

> **THE LINE-SPLIT THEOREM — the second subconstituent splits.**

**Naming, fixed 2026-08-11.** `notes/math/thread1-transition-system.md`
calls this "Theorem C". It is **not** the paper's Theorem C — that is the
flag-counting identity `6n₁ = Σ_x D(x)` in `FlagCount.lean`, 300 lines
below. Two different theorems carried one label; in the Lean layer and in
the arXiv draft "THEOREM C" now means the counting identity and nothing
else.

Formalized as its three structural statements plus the arithmetic:

- `line_through_of_two_nbrs` / `line_off_root_meets_once` — a line meeting
  `N(x)` twice passes through `x`; so relative to a root the lines fall
  into exactly three classes (through `x`; missing `x` and meeting `N(x)`
  once; disjoint from `N[x]`).
- `shared_index_apex` / `shared_index_no_outside_triangle` — the line on an
  index-sharing ("D-") edge of the second subconstituent is `{a, z, w}`
  with `a ∈ N(x)`, so such an edge lies in NO triangle inside the second
  subconstituent.
- `outside_line_stays_outside` — an edge whose two labels are disjoint has
  its whole line outside `N[x]` (no SRG axiom needed).
- `line_split_count` — the ℕ identity
  `v·r = 3·r + 3·(2r(r−1)) + 2r(r−1)(r−2)` for `v = 1 + 2r²`, `r ≥ 2`,
  with `line_split_99` (231 = 7 + 84 + 140) and `line_split_243`
  (891 = 11 + 220 + 660) as instances.

**Scope caveat, stated because it is easy to over-read.** The *counting*
half of the line-split theorem is the arithmetic identity only.  There is no Lean
development of "the set of lines" as a finite object and no proof that its
cardinality is `vr/3` or that the three classes have sizes `r`, `2r(r−1)`,
`2r(r−1)(r−2)/3`; that would need a double-counting layer this file does
not build.  What is proved is that the trichotomy is exhaustive and
exclusive, and that the numbers the note quotes are consistent.

### `CanonicalGeometry.lean` — planes, the far corner, and the Hall gap (logs 033–035)

The geometry that surrounds log 031's certified theorem, from
`notes/math/hall-analogue.md` and log 035's two "NEW RESULT"s.  Again all
generic in `G.IsSRGWith n k 1 2`.

- `CanonicalAt G x` — the transition system at `x` is `M_a(b) = b′`;
  `Canonical G` — canonical at every vertex, `hall-analogue.md`'s unqualified
  word, and the hypothesis of the completion theorems below.
- `CanonicalAt.transfer` — canonicality is a property of the ABSTRACT graph:
  it transports along any adjacency-preserving bijection.  (Also what makes
  the Paley(9) witness for `Canonical` cheap — see non-vacuity below.)
- `not_adj_of_ne_class` — the class rule's first half (λ = 1): a neighbour
  of `x` outside the matched class `{b,b′}` is adjacent to neither.
- `canonical_class_rule` — its second half: under canonicality,
  `z_ab ~ z_ac ⇒ z_ac = z_ab′`.

> **PLANE UNIQUENESS (μ = 2 ONLY).** `corner_unique` / `plane_set_unique`:
> the four corners of the configuration spanned by two lines through `x`
> are each pinned as "the common neighbour other than `x`", so two
> nine-point configurations on the same pair of lines are equal.

As the note stresses, canonicality is what makes the nine points a *grid*,
not what makes them unique — `corner_unique` uses μ = 2 and nothing else.

**Read the scope of `plane_set_unique` narrowly** (adversarial pass,
2026-08-10).  There is no Lean object "plane", so what is proved is that two
nine-point configurations *built from the same two lines and the same four
label positions* coincide — the note's step "the 9 points of Π(L,M) are
determined by L, M and μ = 2".  The rest of `hall-analogue.md` Theorem 1 —
(1) a plane is a subspace, (3) every non-adjacent pair lies in a unique
plane, (4) #planes = #non-adjacent pairs / 18 — is **not** formalized, and
the note remains the citation for it.  See informal item 8(g).

- `common_neighbors_not_adj` / `chordless_quadrangle` — two vertices with
  two distinct common neighbours sit in an INDUCED 4-cycle, and each pair's
  common neighbours are exactly the other pair.  (`hall-analogue.md`
  Theorem 1(3)'s configuration.)

> **THE PLANE EXISTS.** `grid_of_canonical` (`hall-analogue.md` Lemma 1):
> if `G` is canonical at `x`, the nine points `x, a, a′, b, b′, z_ab,
> z_ab′, z_a′b, z_a′b′` induce Paley(9) — rows and columns are its six
> lines.

`IsGrid G pt` records a 3×3 grid on `pt : Fin 3 → Fin 3 → V` (distinct
points; same row or column ⇒ adjacent; neither ⇒ non-adjacent).  The two
diagonal non-adjacencies `z_ab ≁ z_a′b′`, `z_ab′ ≁ z_a′b` are the only
steps that need work, and they go exactly as the note has them (μ = 2 at
`a`, using canonicality at `b′` resp. `b`).

> **THE FAR CORNER IS WELL DEFINED** — log 035's NEW RESULT 1.
> `far_corner_well_defined_of_canonical`: for `G` canonical at `u` and
> `x ≁ y` two neighbours of `u`, the far corner computed at `u` and the far
> corner computed at the OTHER common neighbour `w` of `x` and `y` are the
> same point.

`IsFarCorner G u x y F` says `F` is a common neighbour, other than `u`, of
the two apexes of `ux` and `uy` — the point diagonally opposite `u` in the
grid at `u`, i.e. the third point of the Steiner block `{x, y, x∘y}`.
Supporting theorems: `apexes_not_adj`, `exists_far_corner` (μ = 2),
`far_corner_unique` (μ = 2, at a fixed `u`), `IsFarCorner.symm`
(commutativity), and `far_corner_well_defined` (the grid-hypothesis form,
which also proves the log's intermediate claim that μ = 2 forces the second
common neighbour to BE the grid's inner corner).

Two theorems added by the adversarial pass of 2026-08-10, both of which the
first draft left as gaps:

- `exists_unique_far_corner` — **existence and uniqueness of the far corner,
  unconditionally.**  `exists_far_corner` takes the two apexes as
  hypotheses, so on its own it does not say the far corner exists; λ = 1
  supplies them (`Transition.exists_apex`, also new — every edge has an
  apex, not merely at most one).  Needs NO canonicality.
- `grid_far_point` — **the apex definition is the note's definition.**
  `hall-analogue.md` Theorem 2 defines `x ∘ y` as the unique point of the
  plane non-adjacent to both; `IsFarCorner` defines it by the two apexes.
  Inside a grid the only points non-adjacent to both `pt 1 0` and `pt 0 1`
  are those two and `pt 2 2` — the point `far_corner_well_defined` returns.
  Without this the far-corner theorems would be about a Lean-internal
  notion rather than the note's operation.

> **THE STEINER COMPLETION — the block set and the EXACT COVER** (2026-08-10;
> this replaces the earlier "partial" entry).  `hall-analogue.md` Theorem 2's
> defining property is now a Lean theorem, so **the STS-completion theorem's
> DESIGN content cites Lean, not the note** — its algebraic framing (the
> quasigroup laws as equations), its block COUNT, and the identification of
> a plane's subsystem with `AG(2,3)` *as a design over* `GF(3)` still do not;
> see item 8(b), which survives in exactly that reduced form:
>
> `sts_exact_cover` : for `G.IsSRGWith n k 1 2` with `Canonical G`, **every
> pair of distinct points lies in exactly one block** of
> `IsBlock G = {lines} ∪ {{x, y, x∘y} : x ≁ y}`, and `block_card` : every
> block has exactly three points.
>
> **HYPOTHESIS STRENGTH — this says NOTHING NEW about v = 99, and must not be
> quoted as if it did.**  `Canonical G` is canonicality at EVERY vertex,
> whereas log 031 certifies the failure of `CanonicalAt` at a SINGLE vertex —
> a strictly stronger refutation.  The completion theorems are therefore
> consequences of a hypothesis already known (certifiably) to be false at
> v = 99; they neither extend that certificate nor depend on it (informal
> item 8(e)).  Their content is generic, about λ = 1, μ = 2 graphs.

The supporting layer, each piece named because each is separately quotable:

- `IsDiagonal G x y F` — `F` is a far corner of the non-adjacent pair
  `{x,y}` at SOME common neighbour.  `diagonal_unique` — the common
  neighbour does not matter; this IS far-corner well-definedness in block
  form, and it is where `Canonical` is used (via
  `far_corner_well_defined_of_canonical`).
- `IsDiagonal.symm` (the third point is symmetric in the two defining
  points) and `IsDiagonal.rotate` (ANY two of the three points define the
  block — total symmetry of the Steiner operation).  With
  `diagonal_pair_form` / `line_pair_form` / `block_pair_form` these say the
  block set is well defined as a set of unordered TRIPLES.
- `IsDiagonal.pairwise` (λ = 1 only) — a diagonal block is a co-triangle:
  its three points are distinct and pairwise NON-adjacent.  Hence
  `not_adj_of_mem_diagonal` (an adjacent pair lies in no diagonal) and
  `adj_of_mem_line` (a non-adjacent pair lies in no line): the two kinds of
  block never compete for the same pair, which is the note's decomposition.
- `exists_grid_of_canonical`, `grid_far_corner_eq`, `grid_isDiagonal`,
  `IsDiagonal.in_plane` — the grid calculus the above runs on: the far
  corner of a grid's corner pair is the opposite corner, every broken
  diagonal of a grid is a diagonal block, and every diagonal block is a
  diagonal of a plane.

**Each plane carries the 12-block AG(2,3) design.**  `ag23` is the affine
plane of order 3 written out on `Fin 3 × Fin 3` (3 rows, 3 columns, 6 broken
diagonals); `planeBlocks pt` is its image in a grid.

- `ag23_card` = 12, `ag23_block_card` = 3, and `ag23_exact_cover` — the 12
  blocks cover each of the `C(9,2) = 36` point pairs exactly once (`decide`).
- `plane_blocks_are` — the plane's 6 lines (rows and columns) and 6
  diagonals; `plane_blocks_isBlock` — all twelve are blocks of the design;
  `plane_blocks_card` = 12 (they are distinct).
- `plane_blocks_closed` — **the plane is a SUBSYSTEM**: the design's block
  through any two of its points is one of those twelve.

And the counting identity that makes the completion close:

- `sts_blocks_per_point` — `r + 2·C(r,2) = r²`: the `r` graph lines plus
  the `r(r−1)` plane diagonals give exactly the `r² = (v−1)/2` blocks an
  STS(v) needs at a point, **with no slack and no overlap** (v = 99:
  7 + 42 = 49; v = 243: 11 + 110 = 121).
- `sts_block_count` — the same globally, multiplicatively, using
  `v − 1 = 2r²`.

> **THE HALL GAP, EXACTLY** — log 035's NEW RESULT 2.  `hall_fraction`:
> `6·C(r,2) · r(r+1) = 6·C(r²,2)`, i.e. canonicality certifies the
> fraction `6/(r(r+1))` of the pairs of blocks at a point that Hall's
> condition requires — `126/1176 = 3/28` at v = 99, `330/7260 = 1/22` at
> v = 243 (`hall_fraction_99_243`), and it tends to 0.

> **WHAT THE APPLICATION NEEDS, UNBOUNDED** (2026-08-10; this replaces the
> earlier bounded-only entry).  `family_not_power_of_three` : **for ALL `n`**,
> none of `99`, `6273`, `494019` equals `3ⁿ`.  Proved twice, elementarily and
> independently: by bracketing between consecutive powers
> (`not_pow_three_of_between`; `3⁴ < 99 < 3⁵`, `3⁷ < 6273 < 3⁸`,
> `3¹¹ < 494019 < 3¹²`) and by divisibility
> (`not_pow_three_of_not_dvd` applied to the factorisations
> `99 = 3²·11`, `6273 = 3²·17·41`, `494019 = 3⁵·19·107`, which
> `family_factorisations` VERIFIES rather than asserts) —
> `family_not_power_of_three_dvd`.  `family_powers_of_three` records the
> contrast (`9 = 3²`, `243 = 3⁵`), so the statement is a real separation.

Since the Hall route's conclusion is "`v` is a power of 3", this unbounded
statement is the whole of what an application would consume, and it carries
no bound.

> **THE GENERAL DIOPHANTINE IS STILL NOT OURS.**
> `diophantine_finite_check` / `diophantine_of_exp_le`: for `n ≤ 12`,
> `1 + 2r² = 3ⁿ` forces `r ∈ {0,1,2,11}`.

**This is a FINITE VERIFICATION and must be quoted as one** — `decide` over
`r ≤ 520`, `n ≤ 12` (with the `r`-bound derived, so it is complete for those
`n`), the same discipline as `C3.lean`'s `c3_trace_core`.  It is NOT a proof
of `1 + 2r² = 3ⁿ ⇒ r ∈ {0,1,2,11}`.  The unbounded statement is a
Ramanujan–Nagell-type theorem (the classical route factors
`3ⁿ = (1 + r√−2)(1 − r√−2)` in `ℤ[√−2]` and needs a primitive-divisor
argument) and is **CITED classical, not ours**.  Nothing in the project
depends on it: the name to use is `family_not_power_of_three`.  (The old name
`diophantine_bounded` was renamed `diophantine_finite_check` for exactly this
reason.)

**Non-vacuity.**  `paley9`, `paley9_srg` (`IsSRGWith 9 4 1 2`, by
`decide`), `paley9_isGrid`, `paley9_canonicalAt` exhibit one graph
satisfying `IsSRGWith`, `IsGrid` and `CanonicalAt` simultaneously.  Those
three alone are not enough, because `CanonicalAt` is a ∀-implication and
would hold vacuously in a graph with no label vertices at all; the
adversarial pass of 2026-08-10 therefore added witnesses that the PREMISES
fire:

- `paley9_canonical_premises_fire` — a concrete matched pair, a concrete
  `a` outside it, the two concrete label vertices, and the adjacency
  `CanonicalAt` asserts.  So `IsPartner` and `IsLabel` are inhabited and
  `paley9_canonicalAt` has content.
- `paley9_grid_of_canonical` — `grid_of_canonical` APPLIED: all ten of its
  hypotheses hold at once in Paley(9), producing the coordinate grid.  A
  theorem with jointly unsatisfiable hypotheses could not be applied.
- `paley9_farCorner` — `IsFarCorner` inhabited: far corner `(2,2)` of the
  pair `{(1,0),(0,1)}` at `(0,0)`, apexes `(2,0)`, `(0,2)`.

For the completion theorems the hypothesis is `Canonical` (all nine roots),
so the witness had to be strengthened (2026-08-10):

- `paley9_canonical : Canonical paley9` — **`Canonical` is satisfiable**, so
  `sts_exact_cover` is not vacuous.  Obtained by lifting the single-root
  `paley9_canonicalAt` through `CanonicalAt.transfer` along the nine
  translations, whose adjacency-invariance `paley9_translate_adj` is one
  cheap `decide` over 729 triples.  (Deciding `Canonical paley9` directly
  ranges over `9⁶` tuples and costs minutes of build time; this route costs
  seconds and is the same theorem.)
- `paley9_isDiagonal`, `paley9_blocks_both_kinds` — `IsDiagonal` is
  inhabited and BOTH kinds of block occur (a rook row; the main diagonal),
  so `IsBlock` is not secretly one-sided.
- `paley9_sts_exact_cover` — `sts_exact_cover` APPLIED: all its hypotheses
  hold at once in Paley(9).  `paley9_planeBlocks_card` — its coordinate grid
  carries 12 blocks, i.e. the whole STS(9).

Log 034 records that canonicality at v = 9 is automatic (`B_a` is a
2-set) — this is a witness for the HYPOTHESES, and is not evidence about
v = 99.  There is no Lean-side BvLS(243) witness (243 vertices is far
beyond kernel `decide`); the second known member's canonicality is a
Python check (`notes/math/adjudicate_ab.py`), not a Lean theorem.

### `Makhnev.lean` — COROLLARY C1: Makhnev's (∗) IS canonicality (log 046)

The bridge to the literature.  A. A. Makhnev, *Strongly regular graphs with
λ = 1*, Mat. Zametki 44(5) (1988) 667–672, isolates

> **(∗)** any two triangles joined by at least two edges are joined by exactly
> three,

and proves (his Theorem 2) that no srg(99,14,1,2) satisfies it.
`notes/math/local-canonicality-conjecture.md` §2 records, hand-proved, that (∗)
is the same condition as `Canonical`.  This file machine-checks that.

> **COROLLARY C1** — `makhnevStar_iff_canonical`: in any `G.IsSRGWith n k 1 2`,
> `MakhnevStar G ↔ Canonical G`.  Also `makhnevStarCard_iff_canonical` (the
> cardinality rendering), and the v = 99 / v = 243 instances.

- **The backbone, λ = 1 only.**  `eq_third_of_adj_two` (a vertex adjacent to
  two points of a line IS the third) ⇒ `cross_at_most_one` (a vertex OFF a
  line has at most one neighbour on it) ⇒ `join_card_le_three`: the cross
  edges between two vertex-disjoint triangles form a MATCHING, so the join
  count lies in `{0,1,2,3}`.  Reusable, and both directions of C1 run on it.
  `joinSet` is the join as a `Finset (V × V)`; `two_le_join_card`,
  `join_card_eq_three`, `adj_third_of_join_card` convert between "the join has
  k edges" and the explicit matching.
- **Two renderings, PROVED equal.**  `MakhnevStar` is relational (the style of
  `Transition.lean`: two disjoint lines with two aligned cross edges have the
  third); `MakhnevStarCard` is Makhnev's literal sentence (`2 ≤ join → join =
  3`).  `makhnevStar_iff_card` (λ = 1 only) proves they agree — so the
  relational form is not an editorial choice about what he meant.
- **The flag construction**, shared by both directions and the same map
  Theorem C counts flags along: `flag_disjoint` (the two lines `{a,z_ab,y}`,
  `{x,b,b′}` are vertex-disjoint) and `apex_eq_label_of_adj` (the third cross
  edge forces `y = z_ab′`, i.e. canonicality).
- `adj_third_of_canonicalAt` — the ⇐ direction, and it is **LOCAL**: only
  canonicality at the single root `p′` is used.
- `canonicalAt_of_makhnevStar` — the ⇒ direction.
- `join_card_eq_two_of_not_canonical` — the sharp form: a NON-canonical
  transition exhibits a pair of disjoint triangles joined by **exactly two**
  edges.  This is the local content of the `n₃` half of Theorem C, and where
  "n₃ > 0" and "some transition is not canonical" become one sentence.
- `lines_meet_once`, `lines_through_point_no_cross` — why (∗) may be read on
  vertex-DISJOINT triangles: distinct lines meet in ≤ 1 point, and two lines
  through a common point carry no edge between their residual pairs.

**Non-vacuity, both signs.**  `paley9_makhnevStar` / `paley9_makhnevStarCard`
(Paley(9) satisfies (∗), via C1 and `paley9_canonical`); `paley9_prism` — rows
0 and 1 of the rook's graph are two vertex-disjoint triangles joined by exactly
three edges (an induced triangular prism, the object `n₁` counts), so the
premises FIRE and `join_card_le_three`'s bound is ATTAINED;
`paley9_makhnevStar_fires` — the implication applied.  And the opposite guard,
which matters as much: `twoJoin` is the six-vertex graph of two disjoint
triangles joined by exactly TWO edges, `twoJoin_join_card` gives join = 2, and
`twoJoin_not_makhnevStar` / `twoJoin_not_makhnevStarCard` show **both
renderings of (∗) are FALSIFIABLE**.  (`twoJoin` is deliberately not an SRG; it
is a witness about the definitions, which are stated for arbitrary graphs.
Inside the λ=1, μ=2 family no such witness can be given — both known members
are canonical, and by C1 a non-canonical one is exactly what nobody has ever
produced.)

**What this file does NOT do, and the claim must travel with it.**  Makhnev's
Theorem 2 is **CITED, never proved and never assumed**; nothing here bears on
the existence of an srg(99,14,1,2).  C1 is a translation lemma: it says two
hypotheses are the same hypothesis.  No count appears in THIS file: `n₁`, `n₃`,
`D(x)` are not objects of it, and `joinSet` counts one join, never a sum over
the graph — C1 is proved directly from the backbone and the label lemmas, not
by specialising Theorem C to `n₃ = 0`.  THEOREM C itself — the counting
identity — is formalized SEPARATELY in `FlagCount.lean` (2026-08-11, below),
which also re-derives C1 by counting (`n3_eq_zero_iff_makhnevStar`); the two
proofs are independent.

### `FlagCount.lean` — THEOREM C: the counting identity (logs 046–047)

The identity that converts our SAT certificates into the currency the
published literature on this family actually uses (prisms and 2-joins).
`notes/math/local-canonicality-conjecture.md` §2 stated it hand-proved; this
file proves it, division-free.

> **THEOREM C.**  In any `G.IsSRGWith n k 1 2`,
> `theoremC_n1 : 6 * n1 G = ∑ x, D G x`; and given `k = 2r`,
> `theoremC_n3 : 2 * n3 G = ∑ x, (2 * r * (r - 1) - D G x)`.

> **THE FIBRE COUNT** (`card_fiberOf`, the whole content).  Over an ORDERED
> pair of vertex-disjoint triangles whose join has `m` edges there are
> exactly `m² − m` flags.  Hypothesis: `UniqueTriangle G` — every edge lies
> in at most one triangle — and nothing else.

> **COROLLARY C1, again, by counting.**
> `n3_eq_zero_iff_canonical : n3 G = 0 ↔ Canonical G`, and
> `n3_eq_zero_iff_makhnevStar : n3 G = 0 ↔ MakhnevStar G`.

> **REIMBAYEV Prop. 5(6)** (arXiv:2409.10620), DERIVED not cited:
> `reimbayev_prop5 : 12 * n1 G + 4 * n3 G = n * (k * (k - 2))`, i.e.
> `3n₁ + n₃ = ¼nk(k−2)`, with both `Σ_x D(x)` terms cancelling identically.

> **v = 99, from the hypothesis `hD : ∀ x, D G x ≤ 77`:**
> `conway99_n1_le : n1 G ≤ 1270` and `conway99_n3_ge : 348 ≤ n3 G`.

The supporting pieces:

- **The objects are Lean objects.**  `n1 G` and `n3 G` are the EDGE COUNTS of
  `joinGraph G 3` and `joinGraph G 2` — graphs on `Finset V` whose adjacency
  is "vertex-disjoint 3-cliques with a join of exactly `m` edges".  Using a
  `SimpleGraph` is what makes them counts of UNORDERED pairs with no division:
  `card_ordJoinPairs` is `SimpleGraph.two_mul_card_edgeFinset`.  `D G x` is the
  number of canonical TRANSITIONS at `x` — the counter logs 031/032 bound.
- **The flag map is relational**, in the style of `Transition.lean`: `IsFlag`,
  `IsCanonFlag`, `FlagImage`, with `exists_flagImage` + `flagImage_unique`
  proving it a function.  No `Classical.choice`-extracted map; `classOf` (the
  matched class `{b,b′}`) is likewise choice-free.
- **`card_fiberOf`'s bijection** is with the off-diagonal of the CROSS ENDS of
  `T′`, which biject with the join (`card_crossEnds`) because the cross edges
  form a matching (`Makhnev.cross_at_most_one_ut`).  So `m = 3` gives 6 flags
  per ordered prism pair, i.e. **12 per prism**; `m = 2` gives 2, i.e.
  **4 per 2-join** — log 046's constants, confirmed, with the factor 2 between
  "12" and "6" made explicit instead of divided away.
- **The backbone is stated at its true strength.**  `Makhnev.UniqueTriangle`
  ("every edge lies in at most one triangle"), with `uniqueTriangle_of_srg`
  deriving it from λ = 1, `cross_at_most_one_ut` and
  `cross_at_most_one_finset` above it.  This is not tidiness: `twoJoin` is not
  an SRG, and the weaker hypothesis is the only reason the 2-join branch of the
  fibre count can be instantiated at all (below).
- **Two factors of 2, each proved, neither assumed**: ordered ↔ unordered pairs
  of triangles (`card_ordJoinPairs`), and flags ↔ transitions
  (`card_image_classOf`: a flag set closed under `b ↦ b′` is twice its
  transition set).  Plus `card_flagsAt : #flags at x = k(k−2)`, proved from
  regularity and the neighbourhood matching.
- **The `D` ↔ `CanonicalAt` bridge**: `canonicalAt_iff_forall_flag`,
  `card_transitionsAt` (`= 2r(r−1)`), `D_le`, and BOTH directions of the
  equality case — `D_eq_card_transitionsAt`, `canonicalAt_of_D_eq`, packaged as
  `D_eq_iff_canonicalAt : D G x = 2r(r−1) ↔ CanonicalAt G x`.  So `D` is not a
  new invariant that happens to correlate with canonicality; it is a counter
  whose maximum IS canonicality, which is what lets log 031's certificate be
  quoted as "no vertex is canonical".
- **The divisibility refinement is automatic** — `Σ D = 6·n₁` and `Σ D ≤ 7623`
  force `Σ D ≤ 7620` (`conway99_sum_D_le'`), which is the correction log 046
  made to the earlier `n₃ ≥ 347`.

**Non-vacuity, in two grades, and the difference matters.**  §F14's
`paley9_D = 4`, `paley9_sum_D = 36`, `paley9_n1 = 6`, `paley9_n3 = 0` are all
DERIVED from the theorems above; they agree with the brute-force counts of
`notes/math/theorem_c_check.py`, but that comparison happens outside Lean and
none of them could detect a wrong constant.  §F15 is the falsifiable grade:
`paley9_prism_fibre = 6` and `twoJoin_fibre = 2` are `decide` computations
straight off the definitions, each stated ALONGSIDE the value the theorems
predict (`paley9_prism_fibre_pred`, `twoJoin_fibre_pred`), together with
`paley9_flagsAt_card = 8`, `paley9_canonFlagsAt_card = 8` and
`paley9_D_computed = 4`.  BOTH fibre branches are covered — `m = 3` on
Paley(9), `m = 2` on `twoJoin` — and the second exists only because
`card_fiberOf` asks for `UniqueTriangle` rather than the srg axioms.  No
member of the srg(1+2r², 2r, 1, 2) family can witness `m = 2`: both known
members are canonical, hence have `n₃ = 0`.

**CAVEATS — read these before quoting anything from this file.**
**`D(x) ≤ 77` IS NOT A THEOREM.**  It is a HYPOTHESIS (`hD`) of
`conway99_n1_le` and `conway99_n3_ge`, and what stands behind it is a SAT
certificate — logs 031–032's refutation of `D ≥ 78`, drat-trim and cake_lpr
VERIFIED — not a Lean proof; the encoder correspondence that ties that
certificate to these Lean objects is informal item 7(c), unchanged.
**One link that used to be missing from the chain to `hD` is now proved**
(2026-08-11): the certificate bounds `D` at the SKELETON's root, and
`WLOG.lean`'s `forall_D_le_of_skeleton_root` (rooted WLOG + `D_iso`) turns a
skeleton-root bound into the `∀ x` form `hD` asks for.  Before that, the WLOG
in this library licensed only `∃ x, D G x ≤ 77`, which yields `n₃ ≥ 6`, not
348.  That is a step in the DERIVATION of `hD`, not a proof of it.  Nothing
in this file bears on the existence of an srg(99,14,1,2); `conway99_n1_le` is
a statement about a hypothetical graph.  `reimbayev_prop5` is **not** an
in-Lean arbiter of the constants: it is derived from `card_canonFlagSet_n1`,
`card_badFlagSet_n3` and `card_flagsAt`, i.e. from the lemmas one would want
it to check, so it cannot fail — its force is the EXTERNAL comparison with
Reimbayev's published statement, which was made numerically (18 = 18 at
v = 9, 26,730 = 26,730 at v = 243) and which also forces the unordered
reading of `n₁`, `n₃`, the ordered one giving 36 ≠ 18.  The SRG-specific
2-join lemmas — `flagImage_join_two`, `card_badFlagSet`, `card_badFlagSet_n3`,
`theoremC_n3` — are never instantiated at a concrete graph anywhere in this
library and cannot be, for the reason just given; their external evidence is
`theorem_c_check.py`'s random partial Steiner systems (9,775 2-joins, fibre 4
on every one), and *only* those graphs carry it — Paley(9), BvLS(243),
H(3,3), H(4,3), GQ(2,2) and GQ(2,4) all have `n₃ = 0`.  `n₁` counts PAIRS OF
TRIANGLES joined by three edges; that each such pair spans an induced prism is
immediate, but the converse reading — "every induced prism subgraph arises
from exactly one such pair", which needs "a prism contains exactly two
triangles" — is not formalized.  Reimbayev's Theorem 2 (the hexagon count) is
absent, so the note's hexagon corollary `≥ 209,634` is NOT available in Lean.
The `μ ≠ 2` generalisation `12n₁ + 4n₃ = nk(k−2)(μ−1)` is not stated.
`theoremC_n3` takes `k = 2r` as a hypothesis and proves nothing about
feasibility.

### `WLOG.lean` — the full skeleton WLOG theorem (hard direction)

> **THE ROOTED FORM IS THE ONE TO CITE** (2026-08-11).
> `exists_skeleton_iso_rooted (h : G.IsSRGWith 99 14 1 2) (v₀ : V)` takes the
> root as a PARAMETER and its conclusion records `e rootV = v₀`.

**Why the change.** `exists_skeleton_iso` obtained the root *inside* its
proof (`obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hpos`), so its STATEMENT said
nothing about which vertex of `G` became the skeleton's root.  A bound proved
at the skeleton's root could therefore be exported only as `∃ x, …` — enough
for `n₃ ≥ 6`, not for the paper's `n₃ ≥ 348`, which needs `∀ x, D G x ≤ 77`.
The mathematics was never in doubt (the construction uses nothing about `v₀`
beyond membership in `V`); the STATEMENT was the hole.  Taking `v₀` as a
parameter is half the fix; the load-bearing half is recording that the
isomorphism carries `rootV` — vertex `0` of the `1 + 14 + 84` decomposition,
`Skeleton.lean`'s `rootV` — to `v₀`, because a root parameter alone still
does not transfer a root-indexed quantity.

- `exists_skeleton_iso_rooted` / `skeletonWLOG_rooted` — the rooted
  statements (the second also carrying
  `(skeletonGraph X …).IsSRGWith 99 14 1 2`, so it is the form a certificate
  about skeleton completions is consumed in).
- `exists_skeleton_iso`, `skeletonWLOG`, `skeletonWLOG_poly` — **unchanged
  statements**, now corollaries obtained by supplying some root and
  forgetting the root equation.  Everything downstream (the campaign, this
  README, `Audit.lean`, `C3Wlog.lean`) keeps citing them; they license only
  existential transfer of root-indexed facts.
- **`D_iso` — the canonical-transition counter is an isomorphism
  invariant.**  `D G' (f x) = D G x` for any `f : G ≃g G'`, with **no srg
  hypothesis**: `D` is built from adjacency and equality alone.  Supporting:
  `IsPartner.map`, `IsLabel.map`, `IsFlag.map`, `IsCanonFlag.map`,
  `isFlag_iso`, `isCanonFlag_iso`, `classOf_iso`, `canonFlagsAt_iso`,
  `canonTransitionsAt_iso`.  Without this the root equation would still not
  move a `D`-bound: it is what makes "the skeleton's root satisfies the
  bound" say something about `v₀`.
- **`forall_D_le_of_skeleton_root` — THE ROOT-QUANTIFIER STEP, and the only
  new mathematical content of the fix.**  From
  `∀ X hsymm hirrefl, (skeletonGraph X …).IsSRGWith 99 14 1 2 → D (skeletonGraph X …) rootV ≤ m`
  it derives `∀ x : V, D G x ≤ m` for every abstract srg(99,14,1,2).
  `conway99_n3_ge_of_skeleton_root` composes it with `FlagCount`'s
  `conway99_n3_ge` to give `348 ≤ n3 G` at `m = 77`.
  **Read the hypothesis, not the name**: the skeleton-root bound is a
  HYPOTHESIS of both theorems — it is the SAT/DRAT certificate of logs
  031–032 tied to `D … rootV` by the encoder correspondence (informal item
  7(c)), which this fix does not touch and cannot close.  What the fix closes
  is the ROOT QUANTIFIER, nothing else.

- `skeletonWLOG : skeletonWLOG_statement` — every srg(99,14,1,2), on ANY
  vertex type, is isomorphic to a completion of the canonical skeleton:
  there is an assignment `X` of the 3,486 free outside-outside variables
  with `(skeletonGraph X …).IsSRGWith 99 14 1 2`.  Together with the easy
  direction `srg_exists_of_skeleton` (`Skeleton.lean`): srg(99,14,1,2)
  exists **iff** a completion of the canonical skeleton is one — the SAT
  search loses no models.  Assembly pieces, each proved standalone:
  - `isSRGWith_of_iso` (with `card_commonNeighbors_iso`, `degree_iso`) —
    `IsSRGWith` transports along any graph isomorphism.
  - `exists_partner_compatible_equiv` — any fixed-point-free involution
    on a 14-element type admits an enumeration `Fin 14 ≃ S` aligned with
    the fixed matching `partner` (orbit quotient ≃ 7 pairs × Bool).
  - `exists_skeleton_iso` — the construction: root choice, the λ=1
    matching involution on N(v₀), the matching-compatible enumeration,
    the unique outside witness per non-matched pair
    (`outside_common_neighbor`), injectivity via μ=2 (no outside vertex
    sees three of N(v₀)), bijectivity by counting 99 = 1 + 14 + 84, and
    region-by-region adjacency agreement with `skeletonGraph`.
  - `skeletonWLOG_poly` — the same conclusion for `V : Type*` (any
    universe; `skeletonWLOG_statement` itself pins `V : Type`), with no
    `DecidableEq V` hypothesis: one-line corollary of the two pieces
    above, added in verification to make "ANY vertex type" literal.
  - **All four of these forget the root** (see the rooted forms at the head
    of this section): they say *a* completion exists, not which vertex it is
    rooted at.  For any statement indexed by the root — `D`, `CanonicalAt`,
    the transition counters — cite `exists_skeleton_iso_rooted` /
    `skeletonWLOG_rooted` instead.

## What is CROSS-CHECKED computationally (not a formal proof about Python)

`lake exe export_frame` tabulates the 84 labels and the 91 structured
elements' induced edge permutations FROM THE PROVEN DEFINITIONS
(`sigma` etc.); `src/crosscheck_lean.py` — test battery T6 — compares the
result byte-for-byte with what `src/symmetry.py` feeds the CNF generator.
Current status: identical (175 lines).  Notes: the sbB config's random
elements exercise the same Python code path but only the structured 91
are cross-checked; the CNF clause layer itself is tested exhaustively
(T3), not formalized; and the cross-check covers the LABEL and EDGE-SLOT
frames only — `T2Lex.lean`'s B-orbits and t2 positions have no export, so
their tie to `c2_instance.enrich_clauses`' variable ids is by construction
and review (informal item 6b).

## What remains INFORMAL — future formalization targets, in order

1. **The CNF encoding**: that `symmetry.lex_le_clauses`' projection onto
   the edge variables is exactly `LexLe` (currently T3-tested).
2. **Exactness of the group order**: surjectivity of (π, s) onto the full
   skeleton stabilizer (order exactly 645,120, not just ≥).
3. **LRAT checking in Lean** of solver UNSAT certificates — PILOT DONE
   2026-08-08 (`LratPilot.lean`, road-map item 4 below): the ground-truth
   srg(6,3,0,2) certificate is checked by the toolchain's verified
   full-RAT checker, with the one documented `native_decide`
   compiler-trust axiom.  What remains informal here: the pilot's CNF
   term is tied to the solver's DIMACS by the deterministic generator
   `src/gen_lrat_pilot_lean.py` + recorded sha256s, not by a Lean-side
   encoding theorem (that is road-map item 3), and scale-up (LRAT-Catcher
   reflection / per-cube batching) is future work.
4. **The literature-input hypotheses consumed by `C2.lean`/`C3.lean`**:
   the Makhnev–Minakova 2004 one-fixed-vertex theorem (C2's `hfix`); the
   Behbahani–Lam 2011 fixed-point-freeness of an order-3 automorphism
   (C3's `hfpf`); and the equitable-partition spectral containment for
   the C3 quotient (Godsil–Royle ch. 9; Behbahani 2009 — enters
   `c3_trace_lemma` as `hcard`/`hmem`/`hsum`, bundled with the
   srg(99,14,1,2) spectrum 14¹ 3⁵⁴ (−4)⁴⁴).  Formalizing the containment
   needs equitable partitions and srg spectral theory, both absent from
   Mathlib v4.32.2 (checked 2026-08-08: `Matrix.IsHermitian.eigenvalues`
   exists; interlacing/quotient spectra do not).  Two notes: (a) the
   "spectral containment package" bundles three standard facts —
   eigenvalue containment, multiplicity bounds, and the row-sum-14
   Perron fact giving 14 exactly once; (b) RESOLVED 2026-08-08: the
   graph-level glue of the C3 WLOG — that conjugating an automorphism by
   the relabeling p turns a σ-invariant srg into a g-invariant one — is
   now PROVED, `relabel_graph_to_canonicalC3` (`C3Wlog.lean`).
   (c) **The α = 22 chain of `Alpha22.lean` (2026-08-11) — a WEAKER kind of
   input than the three above, registered here so this list stays the
   complete registry.**  The Hoffman ratio bound, and with it the
   implication "α(Γ) ≤ 22 ⟹ the neighbourhoods of a maximum coclique of Γ
   form a 2-(22,4,2) design", are cited in that file's docstring and are
   **carried by no Lean statement in it**: unlike `hfix`/`hfpf`/the
   spectral containment, they are not hypotheses of any theorem, because no
   theorem in the file mentions v = 99 or Γ — it starts from a design.  So
   nothing there is conditional on them; what depends on the chain is only
   the *interpretation* (that the retired C2 filter was filtering the
   α = 22 branch), not any proved statement.  Same missing Mathlib
   prerequisite as above: equitable partitions / srg spectral theory.
   Also cited, not proved, in that file: the α values (`α(BvLS(243)) = 45`,
   `α(srg(27,10,1,5)) = 6`) and the existence of 2-(22,4,2) designs — all
   log 043 Python computations.
5. **The C3 D-cycle campaign's remaining semantic links** (the WLOG-C /
   WLOG-D relabelings themselves are PROVED — `C3Wlog.lean`; what stays
   informal, mirroring c3_cubes.py's soundness-chain items 3 and 5):
   the E1–E4 enrichment equisatisfiability (dossier arithmetic D5–D6 —
   two small Diophantine systems riding on the same spectral input as
   item 4); D8 (a finite simple 2-regular graph is a disjoint union of
   cycles of length ≥ 3, giving the well-defined cycle through orbit 0
   whose enumeration `exists_perm_canonical_cycle` consumes as a
   hypothesis, and the allowed-length set n−L ∈ {0} ∪ [3,∞)); and the
   definitional bridge that a concrete model's counting-derived
   |S_ij| = 2 relation is the abstract D these theorems relabel (block
   transport `orbitPermLift_map_adj` is proved; the counting layer is
   the E3 clauses, tested not formalized).

6. **What the t2 lex layer rests on** (`T2Lex.lean` proves the group action
   and the equivariance of the t2 DEFINITION; these four links are what is
   left, and none of them is new — they are the pre-existing informal items
   applied to the new position block):
   (a) **`hC`'s edge half** — that the model set of the base instance
   (skeleton + srg conditions + the C2 enrichment families E1–E4) is
   preserved by the wreath action.  Test-verified on the Python side
   (`src/test_symmetry.py`; the design's §3.1a recomputations: E4 incidence
   equivariance 0 failures in 3,822 checks; the E2 equivariance battery
   0/200 on σ-invariant assignments with the negative control failing
   200/200 on arbitrary ones), NOT proved in Lean.  `blockFull_equivariant`
   + `e2_eq_blockFull` supply the t2 half of `hC` and nothing more.
   (b) **The identification of these objects with CNF variable ids** — that
   Lean's `BOrbit`/`T2Pos` are the `reps`/IDPool-allocated `t2(j,k)` of
   `c2_instance.enrich_clauses`, and that the numbering
   `T2Pos ⊕ EdgeSlot ≃ Fin 4347` is `t2_pairs()` ++ `edge_positions()` in
   that order.  The frame cross-check (T6) covers the 84 labels and the 91
   edge permutations only; there is no B-orbit export, so this tie is by
   construction and review, at the same status as informal item 1's
   projection layer.  `combPerm`/`combVec_equivariant` supply everything on
   the combined TYPE; only the transport to `Fin 4347` is informal.
   (c) **The σ-equality clauses must actually be in the instance.**
   `SigmaInvariant` is a HYPOTHESIS of `e2_eq_blockFull`; drop those clauses
   and the equivariance of the t2 definition fails (design §3.2), so any
   instance built on this layer must carry them.
   (d) **Fixed-point dropping** in `symmetry.lex_le_clauses` (the compared
   sequence omits positions the element fixes) applies verbatim to t2
   positions — the same informal step as item 1, neither improved nor
   degraded.

7. **What the graded / `G`-invariant campaign (logs 031, 032, 037) rests
   on.**  The head of this chain is now PROVED and must be cited as a Lean
   name, not as a note:
   (a) **The composition principle is PROVED** —
   `Conway99.gradedInvariant_equisat` (`GradedInvariant.lean`), with the
   two constraint SHAPES proved `S`-invariant (`agreesOn_sInvariant`,
   `counting_sInvariant`) and the campaign's three families as named
   corollaries.  `notes/math/graded-canonical.md` §1's Proposition is no
   longer an informal link.  What is left below is everything OTHER than
   that principle, and none of it changed.
   (b) **The invariance HYPOTHESES for the concrete objects** — that `G`
   fixes the canonical literal set (`hU`/`hv` of `agreesOn_sInvariant`)
   and permutes the 14 canonical sextets as blocks (`BlocksPermuted`) —
   are exhaustive Python checks over all 645,120 elements (log 032 V3,
   log 037 S2), not Lean theorems.  They are hypotheses in the Lean
   statements, exactly like the literature inputs of item 4.
   (c) **Encoder correspondence**: that the CNF the solver refuted
   projects onto these predicates — the sequential-counter cardinality
   layer for `D`/`NBAD`/`SEC`, the 924 units for log 031 — and that the
   auxiliary layer is extendable (`sInvariant_exists`' hypothesis, tested
   by `cardtest`).  This is item 1's projection layer applied to the new
   clause families: tested, not formalized.  Note the scope precisely: the
   CNF's counter lives at the SKELETON's root, so the correspondence to
   state is `D (skeletonGraph X …) rootV`, per completion `X`.  Getting from
   there to a statement about every vertex of an abstract srg is a SEPARATE
   step, and that one is now PROVED — `forall_D_le_of_skeleton_root`
   (`WLOG.lean`, 2026-08-11) = rooted WLOG + `D_iso`.
   (d) **Orbit transport** — the campaign's asserted soundness link 3
   (fixing a witness root by `G`-transport, which is what buys propagation
   where the graded families buy free lex composition; log 037's
   "pick one") — remains informal; road-map item 5.
   (e) **The C3 D-cycle chain's E-family arithmetic (D5–D6) and D8**
   remain informal exactly as in item 5; nothing here touches them.

8. **What the canonical-geometry layer (logs 031–038) still leaves out.**
   `Transition.lean` and `CanonicalGeometry.lean` (2026-08-10) moved the
   structural theorems of `notes/math/thread1-transition-system.md` and
   `notes/math/hall-analogue.md` from "PROVED in markdown" to
   machine-checked.  **None of them was previously on this list** — they
   lived only in the notes — so nothing above is deleted by their arrival,
   and in particular items 7(b) orbit/blocks invariance, 7(c) encoder
   correspondence, 7(d) orbit transport, and item 5's E-family arithmetic
   and D8 are untouched and remain informal.  What the two new files do
   NOT cover:
   (a) **The counting half of Theorem C.**  `line_split_count` is a pure-ℕ
   identity.  There is no formal "set of lines", no proof that it has
   `vr/3` elements, and no proof that the three classes of the trichotomy
   have sizes `r`, `2r(r−1)`, `2r(r−1)(r−2)/3`.  The trichotomy itself
   (exhaustive, exclusive) IS proved.
   (b) **The Steiner completion — what is left after 2026-08-10.**  The
   design itself is now PROVED and this sub-item is what remains.  `IsBlock`
   (the block set), `sts_exact_cover` (every pair in exactly one block),
   `block_card` (every block a 3-set), `plane_blocks_closed` (each plane a
   closed 12-block AG(2,3)-shaped subsystem) are Lean theorems, so
   `hall-analogue.md` Theorem 2's design content no longer needs the note as
   its citation.  NOT formalized: (i) the completion as an ALGEBRA — there is
   no Steiner operation `∘` as a function, hence no idempotent/totally
   symmetric QUASIGROUP statement as equations (the file is relational
   throughout; total symmetry appears as `IsDiagonal.rotate`); (ii) the
   CARDINALITY of the block set — `sts_block_count` is an arithmetic
   identity, and there is no double-counting layer deriving
   `#blocks = v(v−1)/6` from the exact cover; (iii) an isomorphism to
   `AG(2,3)` over `GF(3)` — the plane is proved to carry the explicit
   12-block design `ag23` on `Fin 3 × Fin 3`, which is the affine plane's
   block set written out, but there is no Lean model of `AG(2,3)` and no
   design-isomorphism theorem.
   (c) **The Hall census as a census.**  `hall_fraction` proves the
   arithmetic identity `6·C(r,2)·r(r+1) = 6·C(r²,2)`.  That the certified
   pairs are exactly the `6·C(r,2)` counted — i.e. that distinct grid
   planes through a point certify disjoint sets of block pairs — is the
   note's combinatorial step and is not formalized.
   (d) **The general Diophantine `1 + 2r² = 3ⁿ ⇒ r ∈ {0,1,2,11}` is a CITED
   classical result, not ours** (Ramanujan–Nagell-type; thread A §5's
   remark).  `diophantine_finite_check` is a `decide` over `n ≤ 12` and is
   labelled a finite verification, not a theorem about all `n`.  **This costs
   the project nothing**, because what any application needs — that 99, 6273
   and 494019 are not powers of 3 — is proved unbounded and twice over
   (`family_not_power_of_three`, `family_not_power_of_three_dvd`), 2026-08-10.
   (e) **Nothing connects any of this to log 031's SAT certificate.**  The
   certificate says no srg(99,14,1,2) is canonical at any vertex; these
   files say what canonicality would imply.  The bridge is the encoder
   correspondence of item 7(c), unchanged.
   (f) **The point reflections `σ_p` and Hall's theorem itself** (thread A
   §4–5) are absent.  So is any statement that a canonical srg(v,k,1,2)
   exists at some order — the Paley(9) witness in the file is a witness for
   the HYPOTHESES (non-vacuity), nothing more.
   (g) **`hall-analogue.md` Theorem 1 beyond part (2)'s determinacy step.**
   `plane_set_unique` proves that two nine-point configurations on the same
   two lines with the same four label positions coincide.  There is no Lean
   notion of "plane" as an object, hence no proof that a plane is a
   SUBSPACE (Theorem 1(1)), that every non-adjacent pair lies in a unique
   plane (1(3)), or the plane count (1(4)).  `chordless_quadrangle` is the
   configuration 1(3)'s proof starts from, not its conclusion.  (Added by
   the adversarial pass, 2026-08-10.)  **Unchanged by the completion work**:
   `plane_blocks_*` quantify over a GIVEN grid `pt`, and `IsDiagonal.in_plane`
   produces one; neither turns "plane" into an object with a uniqueness
   theorem, so (g) stands exactly as written.
   (h) **THEOREM C — the counting identity — is PROVED as of 2026-08-11**
   (`FlagCount.lean`): `6·n₁ = Σ_x D(x)` (`theoremC_n1`) and
   `2·n₃ = Σ_x (2r(r−1) − D(x))` (`theoremC_n3`), with `n₁`, `n₃`, `D(x)` as
   Lean objects, the fibre count `m² − m` (`card_fiberOf`) as its content, and
   Reimbayev's Prop. 5(6) derived from it (`reimbayev_prop5`) rather than cited.
   This item therefore SHRINKS to what the identity is quoted alongside and what
   still is not proved: (i) **`D(x) ≤ 77` is a SAT certificate, not a theorem**
   — it is a hypothesis of `conway99_n1_le` / `conway99_n3_ge`, exactly like the
   literature inputs of item 4, and the encoder correspondence that ties it to
   the CNF is item 7(c), unchanged.  **Sub-link CLOSED 2026-08-11**: the
   certificate bounds `D` at the SKELETON's root, and the step from there to
   the `∀ x` form is now proved — `forall_D_le_of_skeleton_root`
   (`WLOG.lean`), which needs the ROOTED WLOG `exists_skeleton_iso_rooted`
   (root as a parameter, `e rootV = v₀` in the conclusion) and `D_iso` (`D`
   is an isomorphism invariant).  The old root-forgetting
   `exists_skeleton_iso` licensed only `∃ x, D G x ≤ 77`, hence only
   `n₃ ≥ 6`; the gap was in the STATEMENT, never in the mathematics.  What
   remains between the certificate and `hD` is exactly item 7(c) — that the
   refuted CNF projects onto `D (skeletonGraph X …) rootV ≥ 78` over the
   completions `X` that are srg(99,14,1,2) — which is tested, not formalized;
   (ii) **Reimbayev's Theorem 2 (the hexagon
   count) is CITED and absent from Lean**, so Corollary C2's third clause — the
   hexagon floor missed by ≥ 348 — still rests on that citation, even though
   `n₃ ≥ 348` itself is now proved from the hypothesis; (iii) `n₁` counts pairs
   of triangles, and "every induced prism subgraph is exactly one such pair"
   (i.e. a prism contains exactly two triangles) is not formalized; (iv) the
   `μ ≠ 2` form `12n₁ + 4n₃ = nk(k−2)(μ−1)` is not stated; (v) the SRG-specific
   2-join lemmas
   (`flagImage_join_two`, `card_badFlagSet`, `theoremC_n3`) are **never
   instantiated at a concrete graph**, and cannot be inside this family — both
   known members are canonical, so both have `n₃ = 0`.  The Python arbiter
   `notes/math/theorem_c_check.py` (121 checks over ten λ=1 graphs, 0 failures,
   the fibre sizes confirmed pair by pair, the falsification scan pinning
   `(12,4)`) remains the check on the STATEMENT's agreement with brute force,
   and only its random partial Steiner systems carry the "4" — Paley(9),
   BvLS(243), H(3,3), H(4,3), GQ(2,2) and GQ(2,4) all have `n₃ = 0` and are
   ZERO-POWER against it.  Grade the in-Lean numbers correctly (log 047):
   `paley9_n1 = 6` / `paley9_n3 = 0` are DERIVED from the identity and so cannot
   falsify its constants; the falsifiable in-Lean checks are §F15's `decide`
   computations — `paley9_prism_fibre = 6` (m = 3) and `twoJoin_fibre = 2`
   (m = 2), each stated beside the value the theorems predict.
   (i) **Makhnev's Theorem 2 itself** — "no srg(99,14,1,2) satisfies (∗)",
   Mat. Zametki 44(5) (1988) 667–672 — is CITED and is neither proved nor
   assumed anywhere in this library.  `Makhnev.lean` proves only that his
   hypothesis and ours coincide.  Nothing in the canonical-geometry layer
   bears on existence.

(The skeleton WLOG assembly, formerly item 1 here, is now PROVED —
`WLOG.lean`, 2026-08-07; **restated in ROOTED form 2026-08-11**
(`exists_skeleton_iso_rooted`), which is what lets a bound proved at the
skeleton's root be quoted for EVERY vertex rather than for some vertex — see
item 8(h)(i).  The graded composition principle, which was
never in this list but should have been, is PROVED as of 2026-08-10 —
`GradedInvariant.lean`; see item 7 for what its hypotheses still rest on.
The transition-system and canonical-geometry theorems of logs 031–038 are
PROVED as of 2026-08-10 — `Transition.lean`, `CanonicalGeometry.lean`; they
were never on this list, so the list did not get shorter, and item 8 records
exactly what they leave out.  Later the same day the two sub-items that had
been recorded as *partial* were closed on their merits: 8(b)'s STS completion
is now the proved exact-cover design `sts_exact_cover`, and 8(d)'s
application-facing Diophantine claim is now the unbounded
`family_not_power_of_three`.  Both sub-items SURVIVE in reduced form — the
completion is a design and not an algebra, and the general Diophantine
remains cited — and are rewritten above to say exactly that.)

Nothing in this library is `sorry`d: every claim is proved, cross-checked,
or listed above as informal.

## The proofs road-map (how proofs keep solving this, in order)

1. **C2/C3 canonical forms** — C2 DONE (`C2.lean`); C3 DONE 2026-08-08
   (`C3.lean`): 3³³ conjugacy WLOG fully proved, trace lemma
   t ∈ {6,13,20,27} proved in hypothesis form (arithmetic core
   sorry-free; equitable-partition spectral containment as the
   clearly-marked literature-input hypothesis — informal item 4).
   Remaining C3 quotient facts (row types 1¹⁰2² / 1¹², no entry ≥ 3,
   2-entry cycle structure) ride on the diagonal quotient equation
   Σ_s c_is² = 18 − c_ii — same spectral input; formalize with (or
   after) the containment.  The D-cycle campaign's relabeling WLOGs
   (WLOG-C d-canonicalization, WLOG-D cycle canonicalization) and the
   graph-level conjugacy glue are DONE 2026-08-08 (`C3Wlog.lean`);
   remaining D-cycle links = informal item 5 (D5–D6, D8, counting
   bridge).
2. **Skeleton WLOG assembly** — DONE (`Skeleton.lean` stage 1 +
   `WLOG.lean` hard direction, 2026-08-07): every certified statement is
   upgraded from "no srg extending the skeleton" to "no srg at all."
   ROOTED form added 2026-08-11 (`exists_skeleton_iso_rooted`,
   `skeletonWLOG_rooted`, with `D_iso` and
   `forall_D_le_of_skeleton_root`): the isomorphism is now proved to carry
   the skeleton's root to a PRESCRIBED vertex, which is what upgrades a
   root-indexed certified bound from "at some vertex" to "at every vertex".
   The old names survive unchanged as corollaries.
3. **Encoder correctness — build on Trestle/VEncCNF** (dossier:
   notes/deep-research-verified-encodings.md).  Architecture: typed
   unordered-pair edge variables (illegal states unrepresentable);
   verified exactly-k / guarded-exactly-k combinators proved ONCE
   (Trestle's sinzExactlyOne as the template; LeanSMS's verified
   sequential counter as precedent); the COMPLETENESS direction only
   (graph ⟹ SAT) — sufficient for nonexistence, halves the effort
   (LeanSMS methodology).  The DIMACS the solver sees must be a
   serialization of the Lean-defined CNF term, not a separate generator.
4. **In-Lean certificate checking — via the public facade + LRAT-Catcher**
   (Szeider 2026, arXiv 2607.00815).  **PILOT DONE 2026-08-08**
   (`Conway99/LratPilot.lean`, generated by
   `src/gen_lrat_pilot_lean.py` from the committed artifact pair in
   `lean/pilot/`): `Conway99.srg6_pilot_unsat : srg6CNF.Unsat` — the
   pipeline's canonical UNSAT ground truth srg(6,3,0,2) (267 vars / 624
   clauses), solved by glucose42, DRAT→LRAT via drat-trim (`s VERIFIED`),
   then re-checked INSIDE Lean by the toolchain's verified full-RAT
   checker: `Std.Tactic.BVDecide.LRAT.parseLRATProof` at elaboration
   (panic-free Except match) + `check` discharged by `native_decide` +
   `check_sound`.  Mechanics learned and documented in the file header:
   (a) DIMACS→`CNF Nat` is the −1 shift, exactly undone inside
   `CNF.convertLRAT` (identity `relabelFin` then +1 into `PosFin`, leading
   `none` restoring 1-based clause ids); (b) the checker assigns lemma
   ids POSITIONALLY, so drat-trim's gapped ids must be densified — a
   trust-neutral rewrite of untrusted input (`srg_6_3_0_2.dense.lrat`,
   sha-recorded like the other three artifacts).  **Compiler-trust
   delta, accepted + confined**: on v4.32.2 `native_decide` asserts
   `<check> = true` as a per-invocation generated axiom
   (`srg6_pilot_check._native.native_decide.ax_1_1` — the successor of
   `Lean.ofReduceBool`); `Audit.lean` fences the pilot lines explicitly
   and every other audited theorem stays standard-axioms-only.
   **Scale-up path**: LRAT-Catcher-style reflection (`lrat_reflect_cnf`
   imports a certificate as `myFormula.Unsat` about the Lean-defined
   formula; published scale: 628 MB certificate in 77 s native, 49 GB
   composed cube-and-conquer in 83 min) or per-cube batching with the
   in-Lean C&C composition theorem (leaf proofs + LRAT-certified cover,
   parallel per-leaf mode — exactly our tree architecture); either way
   the generator step should eventually be replaced by road-map item 3's
   Lean-defined CNF term so the sha tie becomes a definitional tie.
5. **Orbit-transport formalization** — the p(6)=11 partition argument
   as a Lean theorem, closing campaign soundness link 3 formally.
