/-
Conway99.Skeleton — the CONCRETE canonical-skeleton graph on `Fin 99`, and
stage 1 of the WLOG theorem.

This module instantiates, on actual vertices `Fin 99`, the canonical frame
that `src/encode.py:build_skeleton_conway99` fixes on the Python side:

  * vertex `0` — the root;
  * vertices `1..14` — N(0), carrying the fixed perfect matching
    (1,2),(3,4),...,(13,14) in the Python 1-based numbering (here: `nVert w`
    for `w : Fin 14`, matched iff `pairOf w = pairOf w'`, exactly
    `Conway99.Group`'s 0-based convention shifted by one);
  * vertices `15..98` — the 84 outside vertices, vertex `15 + i` carrying
    the `i`-th outside label in THE canonical order: non-matched pairs
    {a,b} ⊆ N(0), a < b, listed lexicographically with the smaller vertex
    first — the order of `symmetry.outside_labels()` / `encode.py`'s
    `non_matched` list.

Contents:

  * `labelReps` / `labelAt` / `enumLabel` — the canonical enumeration
    `Fin 84 → Label` of the 84 outside labels, with machine-checked
    lexicographic sortedness (`labelReps_lex_sorted`), endpoint spot checks
    (`labelAt_zero/one/last`), and a PROOF that it is a bijection
    (`enumLabel_bijective`, packaged as `labelEquiv : Fin 84 ≃ Label`).
    Byte-level agreement with the Python list is a separate T6-style export
    concern, NOT attempted here; the sortedness + bijectivity theorems pin
    the order mathematically.
  * `skeletonAdjB` / `skeletonAdj` / `skeletonGraph` — the skeleton
    adjacency as a Bool matrix over `Fin 99`, parameterized by the ONLY
    free data: a symmetric irreflexive Bool matrix `X` on the 84 outside
    indices (the 3,486 free edge variables of the SAT instance).
    `skeletonGraph X hsymm hirrefl : SimpleGraph (Fin 99)` has decidable
    adjacency.
  * Sanity theorems, independent of `X`: the root's neighbors are exactly
    `1..14` (`root_adj_iff`, `root_degree`); the graph induced on N(0) is
    exactly the 7 matched pairs (`nVert_adj_iff`, `nVert_adj_iff_partner`,
    `nVert_matching`); each outside vertex meets N(0) in exactly the two
    elements of its label (`outVert_adj_nVert_iff`, `outVert_nDegree`).
  * `srg_exists_of_skeleton` — the easy WLOG direction: a skeleton
    completion that is srg(99,14,1,2) is in particular an srg(99,14,1,2).
  * `skeletonWLOG_statement` — the PRECISE statement (a `def`, not a
    sorry'd theorem: this project never commits sorries) of the hard
    direction, with the proof plan in its docstring.

Everything here is sorry-free, `decide`-only (no `native_decide`), and
audited in `Conway99/Audit.lean`.
-/
import Mathlib
import Conway99.Group
import Conway99.SRG

/- The `decide`-based enumeration proofs below evaluate an 84-entry list
inside the kernel; that needs more recursion depth than the default 512
(plain `decide` only — `native_decide` is banned project-wide). -/
set_option maxRecDepth 10000

namespace Conway99

open SimpleGraph

/-- The vertex type of the rooted frame: `0` = root, `1..14` = N(0),
`15..98` = outside vertices in canonical label order. -/
abbrev V99 : Type := Fin 99

/-! ### The canonical enumeration of the 84 outside labels

`Conway99.Group` provides `Label` (the 84 non-matched unordered pairs of
`Fin 14`) and `card_label : Fintype.card Label = 84`, but no ORDER on them.
The SAT side is order-sensitive — `symmetry.outside_labels()` lists the
labels lexicographically (smaller vertex first) and everything downstream
(variable numbering, lex-leader constraints, cubes) keys off that list.
Here we build the same enumeration from ordered representatives and prove
it bijective. -/

/-- The 84 ordered label representatives `(a, b)`, `a < b`, from DISTINCT
matched pairs, in lexicographic order with the smaller vertex first: the
0-based mirror of `symmetry.outside_labels()`'s `(a+1, b+1)` list.  Built
row-major — `a` ascending, then `b` ascending — which IS lexicographic
order (proved below in `labelReps_lex_sorted`, not just by construction). -/
def labelReps : List (Fin 14 × Fin 14) :=
  (List.finRange 14).flatMap fun a =>
    ((List.finRange 14).filter fun b =>
      decide (a < b) && decide (pairOf a ≠ pairOf b)).map fun b => (a, b)

/-- There are exactly 84 representatives, matching `card_label`. -/
theorem labelReps_length : labelReps.length = 84 := by decide

/-- No representative is listed twice. -/
theorem labelReps_nodup : labelReps.Nodup := by decide

/-- Every representative is ordered: smaller vertex first. -/
theorem labelReps_lt : ∀ p ∈ labelReps, p.1 < p.2 := by decide

/-- Every representative joins two DISTINCT matched pairs — i.e. it denotes
a genuine outside label, not a matched edge or a loop. -/
theorem labelReps_pairOf_ne : ∀ p ∈ labelReps, pairOf p.1 ≠ pairOf p.2 := by
  decide

/-- The list is strictly increasing in the lexicographic order on ordered
pairs — THE canonical order of the Python side (`symmetry.outside_labels`).
This pins the enumeration mathematically; byte-level agreement with Python
is left to a future T6-style export. -/
theorem labelReps_lex_sorted :
    labelReps.Pairwise fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  decide

/-- The `i`-th ordered representative. -/
def labelAt (i : Fin 84) : Fin 14 × Fin 14 :=
  labelReps.get (Fin.cast labelReps_length.symm i)

theorem labelAt_mem (i : Fin 84) : labelAt i ∈ labelReps :=
  labelReps.get_mem _

theorem labelAt_lt (i : Fin 84) : (labelAt i).1 < (labelAt i).2 :=
  labelReps_lt _ (labelAt_mem i)

/-- Spot check: the first label is {0,2} — Python's `(1, 3)`, the first
non-matched pair. -/
theorem labelAt_zero : labelAt 0 = (0, 2) := by decide

/-- Spot check: the second label is {0,3} — Python's `(1, 4)`. -/
theorem labelAt_one : labelAt 1 = (0, 3) := by decide

/-- Spot check: the last label (index 83) is {11,13} — Python's `(12, 14)`,
the last non-matched pair (`(13, 14)` itself is matched). -/
theorem labelAt_last : labelAt 83 = (11, 13) := by decide

/-- Distinct indices give distinct representatives (from `labelReps_nodup`). -/
theorem labelAt_injective : Function.Injective labelAt := by
  intro i j h
  have hg := List.nodup_iff_injective_get.mp labelReps_nodup h
  exact Fin.ext (congrArg Fin.val hg)

/-- Every representative is (the representative of) a member of
`labelFinset`: its two vertices lie in distinct matched pairs. -/
theorem labelReps_mem_labelFinset (p : Fin 14 × Fin 14) (hp : p ∈ labelReps) :
    s(p.1, p.2) ∈ labelFinset := by
  simp only [labelFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    sameBlock_mk, decide_eq_false_iff_not]
  exact labelReps_pairOf_ne p hp

/-- THE canonical enumeration of the 84 labels: `enumLabel i` is the label
carried by outside vertex `15 + i`.  Mirrors `symmetry.outside_labels()[i]`
(0-based here, 1-based there). -/
def enumLabel (i : Fin 84) : Label :=
  ⟨s((labelAt i).1, (labelAt i).2), labelReps_mem_labelFinset _ (labelAt_mem i)⟩

/-- The enumeration is injective: an unordered pair determines its ordered
representative (the order `a < b` breaks the `Sym2` symmetry), and distinct
indices have distinct representatives. -/
theorem enumLabel_injective : Function.Injective enumLabel := by
  intro i j h
  apply labelAt_injective
  have hv : s((labelAt i).1, (labelAt i).2) = s((labelAt j).1, (labelAt j).2) :=
    congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · -- crossed match: would force (labelAt j).2 < (labelAt j).1,
    -- contradicting smaller-vertex-first.
    have hi := labelAt_lt i
    have hj := labelAt_lt j
    rw [h1, h2] at hi
    exact absurd hi (not_lt.mpr hj.le)

/-- The enumeration is a bijection: injective between fintypes of equal
cardinality (`card_label : Fintype.card Label = 84` from `Conway99.Group`). -/
theorem enumLabel_bijective : Function.Bijective enumLabel :=
  (Fintype.bijective_iff_injective_and_card enumLabel).mpr
    ⟨enumLabel_injective, by rw [Fintype.card_fin, card_label]⟩

/-- The canonical order packaged as an equivalence `Fin 84 ≃ Label`. -/
noncomputable def labelEquiv : Fin 84 ≃ Label :=
  Equiv.ofBijective enumLabel enumLabel_bijective

/-! ### The rooted frame: regions of `Fin 99` -/

/-- The root, vertex `0`. -/
def rootV : V99 := ⟨0, by omega⟩

/-- Vertex `1 + w` of N(0): the Lean `Fin 14` vertex `w` in the Python
1-based numbering.  Matched pairs (1,2),(3,4),...,(13,14) correspond to
`pairOf w = pairOf w'` on the `Fin 14` side. -/
def nVert (w : Fin 14) : V99 := ⟨w.val + 1, by have := w.isLt; omega⟩

/-- Vertex `15 + i`: the outside vertex carrying label `enumLabel i`. -/
def outVert (i : Fin 84) : V99 := ⟨i.val + 15, by have := i.isLt; omega⟩

@[simp] theorem rootV_val : rootV.val = 0 := rfl
@[simp] theorem nVert_val (w : Fin 14) : (nVert w).val = w.val + 1 := rfl
@[simp] theorem outVert_val (i : Fin 84) : (outVert i).val = i.val + 15 := rfl

/-- Which of the three regions of the frame a vertex belongs to. -/
inductive Region : Type
  | root : Region
  | inN : Fin 14 → Region
  | outside : Fin 84 → Region
  deriving DecidableEq

/-- Region decoding: `0` is the root, `1..14` is N(0) (shifted down by 1),
`15..98` is outside (shifted down by 15). -/
def regionOf (u : V99) : Region :=
  if h0 : u.val = 0 then .root
  else if hN : u.val ≤ 14 then .inN ⟨u.val - 1, by omega⟩
  else .outside ⟨u.val - 15, by have := u.isLt; omega⟩

@[simp] theorem regionOf_root : regionOf rootV = .root := rfl

@[simp] theorem regionOf_nVert (w : Fin 14) : regionOf (nVert w) = .inN w := by
  have h0 : ¬((nVert w).val = 0) := by simp
  have hN : (nVert w).val ≤ 14 := by simp
  unfold regionOf
  rw [dif_neg h0, dif_pos hN]
  congr 1

@[simp] theorem regionOf_outVert (i : Fin 84) : regionOf (outVert i) = .outside i := by
  have h0 : ¬((outVert i).val = 0) := by simp
  have hN : ¬((outVert i).val ≤ 14) := by simp
  unfold regionOf
  rw [dif_neg h0, dif_neg hN]
  congr 1

/-- Every vertex of the frame is the root, an N(0) vertex, or an outside
vertex — the case split all sanity proofs run on. -/
theorem region_cases (u : V99) :
    u = rootV ∨ (∃ w : Fin 14, u = nVert w) ∨ (∃ i : Fin 84, u = outVert i) := by
  have hu := u.isLt
  by_cases h0 : u.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases hN : u.val ≤ 14
    · refine Or.inr (Or.inl ⟨⟨u.val - 1, by omega⟩, Fin.ext ?_⟩)
      change u.val = (u.val - 1) + 1
      omega
    · refine Or.inr (Or.inr ⟨⟨u.val - 15, by omega⟩, Fin.ext ?_⟩)
      change u.val = (u.val - 15) + 15
      omega

/-! ### Skeleton adjacency

`X i j` is the free outside-outside adjacency matrix — the truth values of
the 3,486 free edge variables (only the upper triangle is independent:
`X` is required symmetric and irreflexive).  Everything else is FIXED by
the skeleton, exactly as in `encode.py:build_skeleton_conway99`:

  * root ~ every N(0) vertex, and nothing else;
  * inside N(0): exactly the 7 matched pairs;
  * N(0) vertex `w` ~ outside vertex `15+i` iff `w` is one of the two
    elements of label `i` (`u == a or u == b` in the Python);
  * outside ~ outside: `X`. -/

/-- Adjacency by region — the fixed skeleton, with `X` filling the free
outside-outside block.  All nine region pairs are written out so each case
is a definitional equation. -/
def regAdjB (X : Fin 84 → Fin 84 → Bool) : Region → Region → Bool
  | .root, .root => false
  | .root, .inN _ => true
  | .root, .outside _ => false
  | .inN _, .root => true
  | .inN w, .inN w' => decide (pairOf w = pairOf w' ∧ w ≠ w')
  | .inN w, .outside i => decide (w = (labelAt i).1 ∨ w = (labelAt i).2)
  | .outside _, .root => false
  | .outside i, .inN w => decide (w = (labelAt i).1 ∨ w = (labelAt i).2)
  | .outside i, .outside j => X i j

/-- `regAdjB` is symmetric whenever `X` is. -/
theorem regAdjB_comm (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i) :
    ∀ r r' : Region, regAdjB X r r' = regAdjB X r' r := by
  rintro (_ | w | i) (_ | w' | j) <;> simp only [regAdjB]
  · rw [decide_eq_decide]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  · exact hsymm i j

/-- `regAdjB` is irreflexive whenever `X` is. -/
theorem regAdjB_self (X : Fin 84 → Fin 84 → Bool) (hirrefl : ∀ i, X i i = false) :
    ∀ r : Region, regAdjB X r r = false := by
  rintro (_ | w | i)
  · rfl
  · simp [regAdjB]
  · exact hirrefl i

/-- The skeleton adjacency matrix on `Fin 99` (Bool form). -/
def skeletonAdjB (X : Fin 84 → Fin 84 → Bool) (u v : V99) : Bool :=
  regAdjB X (regionOf u) (regionOf v)

/-- The skeleton adjacency relation on `Fin 99` (Prop form). -/
def skeletonAdj (X : Fin 84 → Fin 84 → Bool) (u v : V99) : Prop :=
  skeletonAdjB X u v = true

theorem skeletonAdjB_comm (X : Fin 84 → Fin 84 → Bool)
    (hsymm : ∀ i j, X i j = X j i) (u v : V99) :
    skeletonAdjB X u v = skeletonAdjB X v u :=
  regAdjB_comm X hsymm _ _

theorem skeletonAdjB_self (X : Fin 84 → Fin 84 → Bool)
    (hirrefl : ∀ i, X i i = false) (u : V99) :
    skeletonAdjB X u u = false :=
  regAdjB_self X hirrefl _

/-- The canonical-skeleton graph: root + fixed N(0) matching + fixed
label attachments, with the free outside-outside block given by `X`.
This is the Lean object corresponding to one total assignment of the
3,486 free edge variables of the SAT instance. -/
def skeletonGraph (X : Fin 84 → Fin 84 → Bool)
    (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false) :
    SimpleGraph V99 where
  Adj := skeletonAdj X
  symm := ⟨fun u v h => (skeletonAdjB_comm X hsymm v u).trans h⟩
  loopless := ⟨fun u h =>
    Bool.false_ne_true ((skeletonAdjB_self X hirrefl u).symm.trans h)⟩

/-- Adjacency in the skeleton graph is decidable (it is a Bool matrix). -/
instance skeletonGraphAdjDecidable (X : Fin 84 → Fin 84 → Bool)
    (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false) :
    DecidableRel (skeletonGraph X hsymm hirrefl).Adj :=
  fun u v => inferInstanceAs (Decidable (skeletonAdjB X u v = true))

theorem skeletonGraph_adj (X : Fin 84 → Fin 84 → Bool)
    (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false) (u v : V99) :
    (skeletonGraph X hsymm hirrefl).Adj u v ↔ skeletonAdjB X u v = true :=
  Iff.rfl

/-! ### Sanity theorems: the fixed part of the skeleton, independent of `X`

These check that `skeletonGraph` really implements the frame the SAT
encoder fixes — for EVERY choice of the free block `X`. -/

section Sanity

variable (X : Fin 84 → Fin 84 → Bool)
variable (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false)

/-- The root is adjacent to exactly the vertices `1..14`, regardless of `X`. -/
theorem root_adj_iff (v : V99) :
    (skeletonGraph X hsymm hirrefl).Adj rootV v ↔ 1 ≤ v.val ∧ v.val ≤ 14 := by
  rcases region_cases v with rfl | ⟨w, rfl⟩ | ⟨i, rfl⟩
  · simp [skeletonGraph_adj, skeletonAdjB, regAdjB]
  · simp [skeletonGraph_adj, skeletonAdjB, regAdjB]
  · simp [skeletonGraph_adj, skeletonAdjB, regAdjB]

/-- The root has degree exactly 14, regardless of `X`. -/
theorem root_degree :
    (skeletonGraph X hsymm hirrefl).degree rootV = 14 := by
  have hset : (skeletonGraph X hsymm hirrefl).neighborFinset rootV =
      Finset.univ.filter (fun v : V99 => 1 ≤ v.val ∧ v.val ≤ 14) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, root_adj_iff]
    simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset]
  decide

/-- Inside N(0) the skeleton induces EXACTLY the 7 matched pairs: two N(0)
vertices are adjacent iff they are distinct members of the same matched
pair — regardless of `X`. -/
theorem nVert_adj_iff (w w' : Fin 14) :
    (skeletonGraph X hsymm hirrefl).Adj (nVert w) (nVert w') ↔
      pairOf w = pairOf w' ∧ w ≠ w' := by
  simp [skeletonGraph_adj, skeletonAdjB, regAdjB]

/-- "Same matched pair, distinct" is the same as "matched partner" —
the bridge to `Conway99.Group`'s `partner`. -/
theorem same_pair_iff_partner :
    ∀ w w' : Fin 14, (pairOf w = pairOf w' ∧ w ≠ w') ↔ partner w = w' := by
  decide

/-- N(0) adjacency, phrased through `partner`: the unique N(0) neighbor of
`w` is its matched partner. -/
theorem nVert_adj_iff_partner (w w' : Fin 14) :
    (skeletonGraph X hsymm hirrefl).Adj (nVert w) (nVert w') ↔ partner w = w' := by
  rw [nVert_adj_iff]
  exact same_pair_iff_partner w w'

/-- The graph induced on N(0) is a perfect matching: every N(0) vertex has
exactly one N(0) neighbor (its partner) — regardless of `X`. -/
theorem nVert_matching (w : Fin 14) :
    ∃! w' : Fin 14, (skeletonGraph X hsymm hirrefl).Adj (nVert w) (nVert w') := by
  refine ⟨partner w, ?_, fun y hy => ?_⟩
  · simp [nVert_adj_iff_partner]
  · simp only [nVert_adj_iff_partner] at hy
    exact hy.symm

/-- Outside vertex `15 + i` is adjacent to N(0) vertex `w` iff `w` is an
element of its label `enumLabel i` — regardless of `X`. -/
theorem outVert_adj_nVert_iff (i : Fin 84) (w : Fin 14) :
    (skeletonGraph X hsymm hirrefl).Adj (outVert i) (nVert w) ↔
      w ∈ (enumLabel i).val := by
  simp [skeletonGraph_adj, skeletonAdjB, regAdjB, enumLabel, Sym2.mem_iff]

/-- Each outside vertex has EXACTLY two neighbors in N(0) — the two
elements of its label — regardless of `X`.  (This is the "every outside
vertex sees μ = 2 vertices of N(0)" half of the skeleton derivation.) -/
theorem outVert_nDegree (i : Fin 84) :
    (Finset.univ.filter fun w : Fin 14 =>
      (skeletonGraph X hsymm hirrefl).Adj (outVert i) (nVert w)).card = 2 := by
  have hset : (Finset.univ.filter fun w : Fin 14 =>
      (skeletonGraph X hsymm hirrefl).Adj (outVert i) (nVert w)) =
      {(labelAt i).1, (labelAt i).2} := by
    ext w
    simp [outVert_adj_nVert_iff, enumLabel, Sym2.mem_iff]
  rw [hset, Finset.card_insert_of_notMem (by simpa using (labelAt_lt i).ne),
    Finset.card_singleton]

end Sanity

/-! ### The WLOG theorem, stage 1 -/

/-- EASY direction of the WLOG, recorded for the record: if some completion
of the canonical skeleton is an srg(99,14,1,2), then an srg(99,14,1,2)
exists — the completion itself is the witness. -/
theorem srg_exists_of_skeleton (X : Fin 84 → Fin 84 → Bool)
    (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false)
    (h : (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2) :
    ∃ (G : SimpleGraph V99) (_ : DecidableRel G.Adj), G.IsSRGWith 99 14 1 2 :=
  ⟨skeletonGraph X hsymm hirrefl, skeletonGraphAdjDecidable X hsymm hirrefl, h⟩

/-- HARD direction of the WLOG (STATEMENT ONLY — this project never commits
sorries, so the unproved claim lives as a named `Prop`, not a theorem):
every srg(99,14,1,2), on any vertex type, is isomorphic to a completion of
the canonical skeleton; equivalently, the SAT search over the 3,486 free
outside-outside variables loses no models.

PROOF PLAN (each step names the existing lemma that supplies it):

1. ROOT CHOICE.  `Fintype.card V = 99 > 0` (`h.card`), so pick any root
   `v₀ : V`.  By `h.regular`, `v₀` has exactly 14 neighbors.

2. THE MATCHING ON N(v₀).  λ = 1 gives `neighborhood_matching`
   (`Conway99.SRG`): every `u ∈ N(v₀)` has a UNIQUE common neighbor `m u`
   with `v₀`; `m u ∈ N(v₀)`, `m u ≠ u` (adjacent vertices are distinct),
   and `m (m u) = u` (uniqueness applied twice).  So `m` is a fixed-point-
   free involution of the 14 neighbors: a perfect matching.  Enumerating
   its 7 pairs yields a bijection `N(v₀) ≃ Fin 14` sending the matching to
   the fixed matching `pairOf`/`partner` of `Conway99.Group` — i.e. to
   vertices 1..14 with pairs (1,2),...,(13,14).

3. THE LABEL BIJECTION.  For any vertex `x` outside `{v₀} ∪ N(v₀)`:
   `v₀ ≁ x`, so μ = 2 (`h.of_not_adj`) gives `x` exactly two neighbors
   `a ≠ b` in N(v₀); the pair {a,b} is NON-matched, else `x` would be a
   second common neighbor of the adjacent pair (a, b) besides `v₀`,
   contradicting λ = 1 (`eq_of_common_adj`, `Conway99.SRG`).  Conversely
   `outside_common_neighbor` (λ = 1, μ = 2; `Conway99.SRG`) gives every
   non-matched pair {a,b} ⊆ N(v₀) EXACTLY ONE common neighbor outside
   `{v₀} ∪ N(v₀)`.  The two maps are mutually inverse, so
   outside-vertices ≃ non-matched pairs = `Label` (84 of them on each
   side: `card_label`, `Conway99.Group`).  Composing with the canonical
   order `labelEquiv : Fin 84 ≃ Label` (this file) sends outside vertices
   to 15..98.

4. TRANSPORT.  Steps 1–3 assemble a vertex bijection `e : V ≃ Fin 99`
   under which every edge touching `{v₀} ∪ N(v₀)` lands exactly on the
   fixed part of `skeletonAdjB` (root_adj_iff / nVert_adj_iff /
   outVert_adj_nVert_iff describe that fixed part).  Define
   `X i j := decide (G.Adj (e.symm (outVert i)) (e.symm (outVert j)))`;
   `hsymm` from `G.symm`, `hirrefl` from `G.loopless`.  Then `e` is a
   graph isomorphism `G ≃g skeletonGraph X hsymm hirrefl`, and
   `IsSRGWith` transports along it: card via `Equiv`, regularity and the
   two common-neighbor counts via the image of neighborhoods under `e`
   (finite counting; `Fintype.card_congr`).

Stages 2–4 are future work, tracked in lean/README.md's informal list. -/
def skeletonWLOG_statement : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.IsSRGWith 99 14 1 2 →
    ∃ (X : Fin 84 → Fin 84 → Bool)
      (hsymm : ∀ i j, X i j = X j i) (hirrefl : ∀ i, X i i = false),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2

end Conway99
