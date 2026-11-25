/-
Conway99.Makhnev — COROLLARY C1: Makhnev's condition (∗) IS canonicality.

CONTEXT.  A. A. Makhnev, "Strongly regular graphs with λ = 1", Mat. Zametki
44(5) (1988) 667–672, isolates the condition

  **(∗)**  any two triangles joined by at least two edges are joined by
           exactly three,

and proves (his Theorem 2) that no srg(99,14,1,2) satisfies it.  Independently,
Keramatipour (arXiv:2604.23037, Definition 12) calls a λ=1, μ=2 graph a
"Paley(9) pattern" graph when every pair of lines through every vertex spans an
induced Paley(9); and this project calls that `Canonical` (the transition system
`M_a(b) = b′` at every root, `CanonicalGeometry.lean`).

`notes/math/local-canonicality-conjecture.md` §2 records, hand-proved, that the
three notions coincide.  **This file machine-checks the Makhnev half:**

  > **COROLLARY C1.**  In any `G.IsSRGWith n k 1 2`,  `MakhnevStar G ↔ Canonical G`.

That is the bridge that lets Makhnev's 1988 theorem, Keramatipour's 2026
pattern and our SAT certificates be quoted about one another.

WHAT IS PROVED HERE.

  * `UniqueTriangle`, `uniqueTriangle_of_srg`, `eq_third_of_adj_two_ut`,
    `cross_at_most_one_ut` — **THE BACKBONE**, stated at its true strength:
    "every edge lies in AT MOST ONE triangle" (`UniqueTriangle`), which λ = 1
    supplies but which many non-SRG graphs also satisfy.  A vertex adjacent to
    two points of a line IS the third point; hence a vertex OFF a line has at
    most one neighbour on it.  This is why the cross edges between two
    vertex-disjoint triangles form a MATCHING.  `eq_third_of_adj_two` and
    `cross_at_most_one` are the srg-hypothesis wrappers, kept because the rest
    of the file uses them.  Weakening the hypothesis is what lets
    `FlagCount.card_fiberOf` be INSTANTIATED on `twoJoin` — see the caveat on
    the m = 2 branch below.
  * `joinSet`, `join_card_le_three` — the join of two vertex-disjoint lines has
    at most 3 edges, i.e. the join count lies in `{0,1,2,3}`.  (λ = 1 only.)
    `join_card_eq_three` / `adj_third_of_join_card` / `two_le_join_card` are the
    three conversions between "the join has k edges" and the explicit matching.
  * `MakhnevStar` — (∗) in the relational style of `Transition.lean`: two
    disjoint lines with two aligned cross edges have the third one too.
  * `MakhnevStarCard` — (∗) in Makhnev's own words, as a CARDINALITY statement:
    `2 ≤ join → join = 3`; and `makhnevStar_iff_card` proves the two agree
    (λ = 1 only).  So the relational rendering is not an editorial choice that
    has to be believed — it is a theorem.
  * `adj_third_of_canonicalAt` — the ⇐ direction, and it is **LOCAL**: only
    canonicality at the ROOT `p′` (one endpoint of the first cross edge) is
    used.
  * `canonicalAt_of_makhnevStar` — the ⇒ direction, at an arbitrary root.
  * `makhnevStar_iff_canonical`, `makhnevStarCard_iff_canonical` — **COROLLARY
    C1**, generic in `n, k`; `makhnevStar_iff_canonical_99` is the v = 99
    instance, which is the one the paper cites Makhnev's Theorem 2 against.
  * `lines_meet_once`, `lines_through_point_no_cross` — why (∗) may be stated
    for vertex-DISJOINT triangles with no loss: two distinct lines meet in at
    most one point, and two lines through a common point have NO edge between
    their residual pairs.
  * `paley9_makhnevStar`, `paley9_makhnevStarCard`, `paley9_prism` — non-vacuity.

WHAT IS *NOT* PROVED HERE — read this before quoting anything.

  * **Makhnev's Theorem 2 is NOT proved and NOT assumed.**  Nothing in this file
    says anything about the existence of an srg(99,14,1,2).  C1 is a
    translation lemma: it says two hypotheses are the same hypothesis.
  * **THEOREM C — the counting identity `n₁ = (1/6)·Σ_x D(x)`,
    `n₃ = (1/2)·Σ_x (2r(r−1) − D(x))` — is not formalized IN THIS FILE.**  Only
    its corollary C1 is, and C1 is proved DIRECTLY (from the backbone plus the
    label lemmas), not by specialising the identity to `n₃ = 0`.  The identity
    itself is PROVED, in `Conway99/FlagCount.lean` (`theoremC_n1`,
    `theoremC_n3`, log 047) — it is no longer hand-proved-only, and this file
    should not be read as saying otherwise.  `notes/math/theorem_c_check.py`
    remains the independent Python arbiter on the STATEMENT.
  * No count is formalized: `n₁`, `n₃`, `D(x)` do not appear.  `joinSet` counts
    the edges of ONE join, never a sum over the graph.
  * The equivalence is with the vertex-DISJOINT reading of (∗).  What licenses
    that reading is `lines_meet_once` + `lines_through_point_no_cross`
    (distinct triangles meet in ≤ 1 point, and then their residual pairs carry
    no edge), which is proved; but Makhnev's own sentence quantifies over all
    pairs of triangles, and rendering "joined by" for a pair sharing a vertex is
    a reading, not a theorem.
  * `MakhnevStar` is about triangles = lines (λ = 1 makes those coincide); the
    file never uses μ = 2 for the backbone, only for C1 itself (both directions
    need it — the ⇒ direction through `label_unique`, the ⇐ direction through
    `exists_label`).
-/
import Mathlib
import Conway99.SRG
import Conway99.Transition
import Conway99.CanonicalGeometry

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-! ### M0 — the backbone: the join of two disjoint triangles is a matching

The backbone needs LESS than λ = 1.  All it needs is that every edge lies in at
most one triangle — `UniqueTriangle` below — which an srg with λ = 1 supplies
(`uniqueTriangle_of_srg`) but which plenty of non-regular graphs satisfy too.
Stating it at that strength is not tidiness: it is what allows
`FlagCount.card_fiberOf` to be applied to `twoJoin` and hence what supplies the
only in-Lean witness for the m = 2 (2-join) fibre. -/

/-- **UNIQUE TRIANGLE** — every edge lies in AT MOST ONE triangle: if `u` and
`w` are both common neighbours of the adjacent pair `p, q`, then `u = w`.

This is the exact hypothesis the whole join/flag machinery runs on.  λ = 1 gives
it (`uniqueTriangle_of_srg`); regularity and `μ` are never used for it. -/
def UniqueTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ p q u w : V, G.Adj p q → G.Adj p u → G.Adj q u → G.Adj p w → G.Adj q w → u = w

instance decidableUniqueTriangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable (UniqueTriangle G) := by
  unfold UniqueTriangle; infer_instance

/-- λ = 1 ⟹ every edge lies in at most one triangle. -/
theorem uniqueTriangle_of_srg (h : G.IsSRGWith n k 1 μ) : UniqueTriangle G :=
  fun _p _q _u _w hpq hpu hqu hpw hqw =>
    unique_common_of_adj h hpq
      ((mem_commonNeighbors G).mpr ⟨hpu, hqu⟩)
      ((mem_commonNeighbors G).mpr ⟨hpw, hqw⟩)

/-- A vertex adjacent to two points of a line IS the third point of that line.
(The unique-apex property, in the form used everywhere below.) -/
theorem eq_third_of_adj_two_ut (hut : UniqueTriangle G) {p q r u : V}
    (hL : IsLine G p q r) (hup : G.Adj p u) (huq : G.Adj q u) : u = r :=
  hut p q u r hL.1 hup huq hL.2.1 hL.2.2

/-- λ = 1: a vertex adjacent to two points of a line IS the third point of that
line.  (The srg wrapper around `eq_third_of_adj_two_ut`.) -/
theorem eq_third_of_adj_two (h : G.IsSRGWith n k 1 μ) {p q r u : V}
    (hL : IsLine G p q r) (hup : G.Adj p u) (huq : G.Adj q u) : u = r :=
  eq_third_of_adj_two_ut (uniqueTriangle_of_srg h) hL hup huq

/-- **THE BACKBONE** (unique triangles only).  A vertex OFF a line is adjacent
to AT MOST ONE of its three points: if it had two it would be the third point,
hence on the line.

This is the whole reason the cross edges between two vertex-disjoint triangles
form a matching, and therefore the reason the join count lies in `{0,1,2,3}`.
Both directions of Corollary C1 run on it, as does `FlagCount.card_fiberOf`. -/
theorem cross_at_most_one_ut (hut : UniqueTriangle G) {p q r u : V}
    (hL : IsLine G p q r) (hu : u ∉ ({p, q, r} : Finset V))
    {v w : V} (hv : v ∈ ({p, q, r} : Finset V)) (hw : w ∈ ({p, q, r} : Finset V))
    (huv : G.Adj u v) (huw : G.Adj u w) : v = w := by
  by_contra hne
  obtain ⟨t, hLt, hset⟩ := line_pair_form hL hv hw hne
  have hut' : u = t := eq_third_of_adj_two_ut hut hLt huv.symm huw.symm
  subst hut'
  exact hu (by rw [hset]; simp)

/-- **THE BACKBONE**, srg wrapper (λ = 1 only). -/
theorem cross_at_most_one (h : G.IsSRGWith n k 1 μ) {p q r u : V}
    (hL : IsLine G p q r) (hu : u ∉ ({p, q, r} : Finset V))
    {v w : V} (hv : v ∈ ({p, q, r} : Finset V)) (hw : w ∈ ({p, q, r} : Finset V))
    (huv : G.Adj u v) (huw : G.Adj u w) : v = w :=
  cross_at_most_one_ut (uniqueTriangle_of_srg h) hL hu hv hw huv huw

/-- Two distinct lines meet in at most one point: if they share two, they share
the third (λ = 1 — this is `apex_unique`). -/
theorem lines_meet_once (h : G.IsSRGWith n k 1 μ) {p q r s : V}
    (hL : IsLine G p q r) (hL' : IsLine G p q s) : r = s :=
  apex_unique h hL hL'

/-- **WHY (∗) MAY BE READ ON VERTEX-DISJOINT TRIANGLES** (λ = 1 only).  Two
lines through a common point `x` whose residual pairs are disjoint have NO edge
between those residual pairs — `Γ[N(x)]` is a perfect matching, and the two
pairs are two of its edges.  Together with `lines_meet_once` (distinct lines
meet in ≤ 1 point) this says: a pair of distinct triangles carrying cross edges
away from a shared vertex is vertex-disjoint. -/
theorem lines_through_point_no_cross (h : G.IsSRGWith n k 1 μ) {x a a' b b' : V}
    (hLa : IsLine G x a a') (hLb : IsLine G x b b')
    (h1 : a ≠ b) (h2 : a ≠ b') (h3 : a' ≠ b) (h4 : a' ≠ b') :
    ¬ G.Adj a b ∧ ¬ G.Adj a b' ∧ ¬ G.Adj a' b ∧ ¬ G.Adj a' b' := by
  have hpb : IsPartner G x b b' := ⟨hLb.1, hLb.2.1, hLb.2.2⟩
  obtain ⟨c1, c2⟩ := not_adj_of_ne_class h hpb hLa.1 h1 h2
  obtain ⟨c3, c4⟩ := not_adj_of_ne_class h hpb hLa.2.1 h3 h4
  exact ⟨c1, c2, c3, c4⟩

omit [Fintype V] in
/-- A convenience: nine `≠`s make two triples disjoint as `Finset`s. -/
theorem disjoint_triple {a b c d e f : V}
    (h1 : a ≠ d) (h2 : a ≠ e) (h3 : a ≠ f)
    (h4 : b ≠ d) (h5 : b ≠ e) (h6 : b ≠ f)
    (h7 : c ≠ d) (h8 : c ≠ e) (h9 : c ≠ f) :
    Disjoint ({a, b, c} : Finset V) ({d, e, f} : Finset V) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  rcases hz with rfl | rfl | rfl <;> tauto

/-! ### M1 — the join, and the `{0,1,2,3}` lemma -/

/-- The **JOIN** of two vertex sets: the cross edges, as ordered pairs. -/
def joinSet (G : SimpleGraph V) [DecidableRel G.Adj] (T T' : Finset V) :
    Finset (V × V) :=
  (T ×ˢ T').filter fun e => G.Adj e.1 e.2

omit [Fintype V] [DecidableEq V] in
theorem mem_joinSet {T T' : Finset V} {e : V × V} :
    e ∈ joinSet G T T' ↔ e.1 ∈ T ∧ e.2 ∈ T' ∧ G.Adj e.1 e.2 := by
  simp [joinSet, and_assoc]

/-- **THE JOIN COUNT LIES IN `{0,1,2,3}`** (λ = 1 only): the cross edges from a
triple to a vertex-disjoint LINE form a matching, so there are at most three of
them.  Only the second triangle has to be a line. -/
theorem join_card_le_three (h : G.IsSRGWith n k 1 μ) {p q r p' q' r' : V}
    (hL' : IsLine G p' q' r')
    (hdisj : Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V)) :
    (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card ≤ 3 := by
  have hmain : (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card ≤
      ({p, q, r} : Finset V).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro e he
      exact (mem_joinSet.mp he).1
    · intro e1 he1 e2 he2 hfst
      simp only [Finset.mem_coe] at he1 he2
      obtain ⟨hu1, hv1, ha1⟩ := mem_joinSet.mp he1
      obtain ⟨-, hv2, ha2⟩ := mem_joinSet.mp he2
      have hnot : e1.1 ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj hu1
      have hsnd : e1.2 = e2.2 := by
        refine cross_at_most_one h hL' hnot hv1 hv2 ha1 ?_
        rw [hfst]; exact ha2
      exact Prod.ext hfst hsnd
  have a1 := Finset.card_insert_le p ({q, r} : Finset V)
  have a2 := Finset.card_insert_le q ({r} : Finset V)
  have a3 : ({r} : Finset V).card = 1 := Finset.card_singleton r
  omega

/-- Two aligned cross edges give a join of at least two. -/
theorem two_le_join_card {p q r p' q' r' : V} (hL : IsLine G p q r)
    (h1 : G.Adj p p') (h2 : G.Adj q q') :
    2 ≤ (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card := by
  have hsub : ({(p, p'), (q, q')} : Finset (V × V)) ⊆
      joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_joinSet.mpr ⟨by simp, by simp, h1⟩
    · exact mem_joinSet.mpr ⟨by simp, by simp, h2⟩
  have hc : ({(p, p'), (q, q')} : Finset (V × V)).card = 2 :=
    Finset.card_pair (by simp [Prod.ext_iff, hL.1.ne])
  have := Finset.card_le_card hsub
  omega

/-- A perfect matching between two disjoint lines is a join of exactly three. -/
theorem join_card_eq_three (h : G.IsSRGWith n k 1 μ) {p q r p' q' r' : V}
    (hL : IsLine G p q r) (hL' : IsLine G p' q' r')
    (hdisj : Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V))
    (h1 : G.Adj p p') (h2 : G.Adj q q') (h3 : G.Adj r r') :
    (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card = 3 := by
  have hsub : ({(p, p'), (q, q'), (r, r')} : Finset (V × V)) ⊆
      joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact mem_joinSet.mpr ⟨by simp, by simp, h1⟩
    · exact mem_joinSet.mpr ⟨by simp, by simp, h2⟩
    · exact mem_joinSet.mpr ⟨by simp, by simp, h3⟩
  have hc : ({(p, p'), (q, q'), (r, r')} : Finset (V × V)).card = 3 :=
    Finset.card_eq_three.mpr ⟨(p, p'), (q, q'), (r, r'),
      by simp [Prod.ext_iff, hL.1.ne], by simp [Prod.ext_iff, hL.2.1.ne],
      by simp [Prod.ext_iff, hL.2.2.ne], rfl⟩
  have hge := Finset.card_le_card hsub
  have hle := join_card_le_three h hL' hdisj
  omega

/-- **THE THIRD EDGE IS FORCED BY THE COUNT**: two disjoint lines with two
aligned cross edges and a join of exactly three are joined by the matching
edge `r r′` as well.  (λ = 1 only: without the third edge the join is contained
in the two known ones.) -/
theorem adj_third_of_join_card (h : G.IsSRGWith n k 1 μ) {p q r p' q' r' : V}
    (hL : IsLine G p q r) (hL' : IsLine G p' q' r')
    (hdisj : Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V))
    (h1 : G.Adj p p') (h2 : G.Adj q q')
    (hcard : (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card = 3) :
    G.Adj r r' := by
  by_contra hrr'
  have hpn : p ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj (by simp)
  have hqn : q ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj (by simp)
  have hp'n : p' ∉ ({p, q, r} : Finset V) := Finset.disjoint_right.mp hdisj (by simp)
  have hq'n : q' ∉ ({p, q, r} : Finset V) := Finset.disjoint_right.mp hdisj (by simp)
  have hsub : joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V) ⊆
      {(p, p'), (q, q')} := by
    rintro ⟨u, v⟩ he
    obtain ⟨hu, hv, hadj⟩ := mem_joinSet.mp he
    simp only at hu hv hadj
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, cross_at_most_one h hL' hpn hv (by simp) hadj h1⟩
    · exact Or.inr ⟨rfl, cross_at_most_one h hL' hqn hv (by simp) hadj h2⟩
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact absurd (cross_at_most_one h hL hp'n (by simp) (by simp)
          hadj.symm h1.symm) hL.2.1.ne'
      · exact absurd (cross_at_most_one h hL hq'n (by simp) (by simp)
          hadj.symm h2.symm) hL.2.2.ne'
      · exact hrr' hadj
  have hle := Finset.card_le_card hsub
  have h2card : ({(p, p'), (q, q')} : Finset (V × V)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  omega

/-! ### M2 — Makhnev's condition (∗), in two renderings -/

/-- **MAKHNEV'S CONDITION (∗)**, relational form (the style of
`Transition.lean`): any two vertex-disjoint triangles joined by two edges are
joined by the third.

Reading it: `IsLine G p q r` and `IsLine G p' q' r'` are the two triangles,
`Disjoint` is "vertex-disjoint", and `G.Adj p p'`, `G.Adj q q'` present the two
known cross edges ALIGNED — which is no loss, because by `cross_at_most_one`
the cross edges form a matching, so any two of them are of this shape after
renaming the points of each triangle.  `makhnevStar_iff_card` proves exactly
that: this definition is equivalent to the literal cardinality statement. -/
def MakhnevStar (G : SimpleGraph V) : Prop :=
  ∀ p q r p' q' r' : V, IsLine G p q r → IsLine G p' q' r' →
    Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V) →
    G.Adj p p' → G.Adj q q' → G.Adj r r'

/-- **MAKHNEV'S CONDITION (∗)**, literal form — his own sentence: any two
vertex-disjoint triangles joined by AT LEAST TWO edges are joined by EXACTLY
THREE. -/
def MakhnevStarCard (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ p q r p' q' r' : V, IsLine G p q r → IsLine G p' q' r' →
    Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V) →
    2 ≤ (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card →
    (joinSet G ({p, q, r} : Finset V) ({p', q', r'} : Finset V)).card = 3

/-- **THE TWO RENDERINGS AGREE** (λ = 1 only).  So the relational form used
below is not an editorial choice about what Makhnev meant: it is his statement.
The forward direction is where the backbone does its work — from `2 ≤ join` one
must produce two cross edges that are aligned, and that is exactly the matching
property. -/
theorem makhnevStar_iff_card (h : G.IsSRGWith n k 1 μ) :
    MakhnevStar G ↔ MakhnevStarCard G := by
  constructor
  · intro hstar p q r p' q' r' hL hL' hdisj hge
    obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.mp hge
    obtain ⟨hu1, hv1, ha1⟩ := mem_joinSet.mp he1
    obtain ⟨hu2, hv2, ha2⟩ := mem_joinSet.mp he2
    have hune : e1.1 ≠ e2.1 := by
      intro hh
      have hnot : e1.1 ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj hu1
      refine hne (Prod.ext hh (cross_at_most_one h hL' hnot hv1 hv2 ha1 ?_))
      rw [hh]; exact ha2
    have hvne : e1.2 ≠ e2.2 := by
      intro hh
      have hnot : e1.2 ∉ ({p, q, r} : Finset V) := Finset.disjoint_right.mp hdisj hv1
      refine hne (Prod.ext ?_ hh)
      refine cross_at_most_one h hL hnot hu1 hu2 ha1.symm ?_
      rw [hh]; exact ha2.symm
    obtain ⟨w, hLw, hTeq⟩ := line_pair_form hL hu1 hu2 hune
    obtain ⟨w', hLw', hT'eq⟩ := line_pair_form hL' hv1 hv2 hvne
    rw [hTeq, hT'eq] at hdisj ⊢
    have ha2' : G.Adj e2.1 e2.2 := ha2
    exact join_card_eq_three h hLw hLw' hdisj ha1 ha2'
      (hstar _ _ _ _ _ _ hLw hLw' hdisj ha1 ha2')
  · intro hcard p q r p' q' r' hL hL' hdisj h1 h2
    exact adj_third_of_join_card h hL hL' hdisj h1 h2
      (hcard p q r p' q' r' hL hL' hdisj (two_le_join_card hL h1 h2))

/-! ### M3 — COROLLARY C1 -/

/-- **C1, the ⇐ direction, and it is LOCAL.**  Canonicality AT THE SINGLE ROOT
`p′` already forces the third cross edge of any pair of vertex-disjoint lines
joined by two edges, one of which lands on `p′`.

The proof is the flag argument of `notes/math/local-canonicality-conjecture.md`
§2 read backwards.  With `x := p′`: `{q′, r′}` is a matched pair of `N(x)`
(they are the other two points of the line through `x`), `p ∈ N(x)` lies
outside that class, and `q` is the label vertex `z_{p,q′}` — it is adjacent to
`p` and to `q′`, misses `x`, and is not adjacent to `x` (else `x` would be a
second common neighbour of the edge `p q`).  Canonicality at `x` says
`z_{p,q′} ~ z_{p,r′}`; then `z_{p,r′}` is adjacent to both ends of the edge
`p q`, so λ = 1 identifies it with `r`, and `r ~ r′` is its label adjacency. -/
theorem adj_third_of_canonicalAt (h : G.IsSRGWith n k 1 2) {p q r p' q' r' : V}
    (hL : IsLine G p q r) (hL' : IsLine G p' q' r')
    (hdisj : Disjoint ({p, q, r} : Finset V) ({p', q', r'} : Finset V))
    (hcan : CanonicalAt G p') (h1 : G.Adj p p') (h2 : G.Adj q q') :
    G.Adj r r' := by
  have hpn : p ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj (by simp)
  have hqn : q ∉ ({p', q', r'} : Finset V) := Finset.disjoint_left.mp hdisj (by simp)
  have hp'n : p' ∉ ({p, q, r} : Finset V) := Finset.disjoint_right.mp hdisj (by simp)
  -- the matched pair of `N(p′)` cut out by the second line
  have hpart : IsPartner G p' q' r' := ⟨hL'.1, hL'.2.1, hL'.2.2⟩
  have hxp : G.Adj p' p := h1.symm
  have hpq' : p ≠ q' := by rintro rfl; exact hpn (by simp)
  have hpr' : p ≠ r' := by rintro rfl; exact hpn (by simp)
  -- `q` is the label vertex `z_{p,q′}`
  have hqx : q ≠ p' := by rintro rfl; exact hp'n (by simp)
  have hnxq : ¬ G.Adj p' q := by
    intro hadj
    exact hL.1.ne (cross_at_most_one h hL hp'n (by simp) (by simp) hxp hadj)
  have hlab1 : IsLabel G p' p q' q := ⟨hL.1, h2.symm, hqx, hnxq⟩
  -- the label vertex `z_{p,r′}` exists (μ = 2)
  have hnprr : ¬ G.Adj p r' := by
    intro hadj
    exact hL'.2.1.ne (cross_at_most_one h hL' hpn (by simp) (by simp) h1 hadj)
  obtain ⟨w, hlab2⟩ := exists_label h hxp hL'.2.1 hnprr hpr'
  -- canonicality at `p′`, then λ = 1 on the edge `p q`
  have hqw : G.Adj q w := hcan p q' r' q w hxp hpart hpq' hpr' hlab1 hlab2
  have hwr : w = r := eq_third_of_adj_two h hL hlab2.1 hqw
  exact (hwr ▸ hlab2.2.1).symm

/-! #### The flag construction

A *transition* at `x` is the data (root `x`, neighbour `a`, matched pair
`{b,b′}` of `N(x)` with `a ∉ {b,b′}`) together with its label vertices.  The
map of Theorem C sends it to the pair of lines `{a, z_ab, y}` (`y` = the apex
of the edge `a z_ab`, which exists by λ = 1) and `{x, b, b′}`.  These two
lemmas are the two facts about that pair which both halves of C1 use.
-/

/-- **THE FLAG'S TWO TRIANGLES ARE VERTEX-DISJOINT** (λ = 1 only). -/
theorem flag_disjoint (h : G.IsSRGWith n k 1 μ) {x a b b' zab y : V}
    (hxa : G.Adj x a) (hpb : IsPartner G x b b') (hab : a ≠ b) (hab' : a ≠ b')
    (hzab : IsLabel G x a b zab) (hy : IsApex G a zab y) :
    Disjoint ({a, zab, y} : Finset V) ({x, b, b'} : Finset V) := by
  obtain ⟨hnab, hnab'⟩ := not_adj_of_ne_class h hpb hxa hab hab'
  exact disjoint_triple hxa.ne' hab hab' hzab.2.2.1 hzab.2.1.ne'
    (fun hh => hnab' (hh ▸ hzab.1))
    (fun hh => hzab.2.2.2 ((hh ▸ hy.2.2).symm))
    (fun hh => hnab (hh ▸ hy.2.1)) (fun hh => hnab' (hh ▸ hy.2.1))

/-- **THE THIRD CROSS EDGE IS CANONICALITY** (λ = 1, μ = 2).  If the flag's two
triangles carry the third cross edge `y b′`, then the apex `y` IS the second
label vertex `z_ab′` — so `z_ab ~ z_ab′`, i.e. the transition is canonical.
(`y ≁ x`: otherwise `y` and `b` would be two common neighbours of the ADJACENT
pair `{x, b′}`, and λ = 1 would force `y = b`, which disjointness forbids.) -/
theorem apex_eq_label_of_adj (h : G.IsSRGWith n k 1 2) {x a b b' zab zab' y : V}
    (hxa : G.Adj x a) (hpb : IsPartner G x b b') (hab : a ≠ b) (hab' : a ≠ b')
    (hzab : IsLabel G x a b zab) (hzab' : IsLabel G x a b' zab')
    (hy : IsApex G a zab y) (hyb' : G.Adj y b') : y = zab' := by
  obtain ⟨hnab, hnab'⟩ := not_adj_of_ne_class h hpb hxa hab hab'
  have hyxne : y ≠ x := fun hh => hzab.2.2.2 ((hh ▸ hy.2.2).symm)
  have hybne : y ≠ b := fun hh => hnab (hh ▸ hy.2.1)
  have hnxy : ¬ G.Adj x y := by
    intro hadj
    exact hybne (unique_common_of_adj h hpb.2.1
      ((mem_commonNeighbors G).mpr ⟨hadj, hyb'.symm⟩)
      ((mem_commonNeighbors G).mpr ⟨hpb.1, hpb.2.2.symm⟩))
  exact label_unique h hxa hpb.2.1 hnab' hab' ⟨hy.2.1, hyb'.symm, hyxne, hnxy⟩ hzab'

/-- **C1, the ⇒ direction.**  Makhnev's (∗) gives canonicality at EVERY root.

Apply (∗) to the flag's two vertex-disjoint lines `{a, z_ab, y}` and
`{x, b, b′}`, which carry the two cross edges `a x` and `z_ab b`; (∗) supplies
the third, `y b′`; `apex_eq_label_of_adj` turns that into `y = z_ab′`, and the
apex adjacency `z_ab ~ y` is the canonicality demanded. -/
theorem canonicalAt_of_makhnevStar (h : G.IsSRGWith n k 1 2)
    (hstar : MakhnevStar G) (x : V) : CanonicalAt G x := by
  intro a b b' zab zab' hxa hpb hab hab' hzab hzab'
  obtain ⟨y, hy, -⟩ := exists_apex h hzab.1
  have hyb'adj : G.Adj y b' :=
    hstar a zab y x b b' ⟨hy.1, hy.2.1, hy.2.2⟩ ⟨hpb.1, hpb.2.1, hpb.2.2⟩
      (flag_disjoint h hxa hpb hab hab' hzab hy) hxa.symm hzab.2.1.symm
  exact apex_eq_label_of_adj h hxa hpb hab hab' hzab hzab' hy hyb'adj ▸ hy.2.2

/-- **A NON-CANONICAL TRANSITION EXHIBITS A 2-JOIN** — the local content of the
`n₃` half of Theorem C, and the sharp form of the ⇒ direction: if
`z_ab ≁ z_ab′` then the flag's two lines are vertex-disjoint and joined by
EXACTLY two edges.  (≥ 2 from the two cross edges the flag always carries;
≤ 3 from the backbone; ≠ 3 because a third edge would force canonicality.)

This is where Makhnev's `n₃ > 0` and our "some transition is not canonical"
become the same sentence about the same object.  It does NOT count anything:
`n₃` as a number does not appear here (see the header). -/
theorem join_card_eq_two_of_not_canonical (h : G.IsSRGWith n k 1 2)
    {x a b b' zab zab' y : V}
    (hxa : G.Adj x a) (hpb : IsPartner G x b b') (hab : a ≠ b) (hab' : a ≠ b')
    (hzab : IsLabel G x a b zab) (hzab' : IsLabel G x a b' zab')
    (hy : IsApex G a zab y) (hnadj : ¬ G.Adj zab zab') :
    Disjoint ({a, zab, y} : Finset V) ({x, b, b'} : Finset V) ∧
      (joinSet G ({a, zab, y} : Finset V) ({x, b, b'} : Finset V)).card = 2 := by
  have hLT : IsLine G a zab y := ⟨hy.1, hy.2.1, hy.2.2⟩
  have hLT' : IsLine G x b b' := ⟨hpb.1, hpb.2.1, hpb.2.2⟩
  have hdisj := flag_disjoint h hxa hpb hab hab' hzab hy
  refine ⟨hdisj, ?_⟩
  have hge := two_le_join_card hLT hxa.symm hzab.2.1.symm (r' := b')
  have hle := join_card_le_three h hLT' hdisj
  have hne3 : (joinSet G ({a, zab, y} : Finset V) ({x, b, b'} : Finset V)).card ≠ 3 := by
    intro hh
    refine hnadj ?_
    have hyb' := adj_third_of_join_card h hLT hLT' hdisj hxa.symm hzab.2.1.symm hh
    exact apex_eq_label_of_adj h hxa hpb hab hab' hzab hzab' hy hyb' ▸ hy.2.2
  omega

/-- **COROLLARY C1.**  In any srg(n,k,1,2), Makhnev's condition (∗) is
EQUIVALENT to canonicality at every vertex — i.e. to Keramatipour's Paley(9)
pattern, and to `Canonical` as this repo defines it.

This is the bridge sentence of `notes/math/local-canonicality-conjecture.md`
§2: it is what lets Makhnev's Theorem 2 (1988; CITED, not proved here) be
quoted as the every-vertex canonicality exclusion at v = 99, and hence what
makes our one-vertex certificates a strengthening of it rather than a different
statement. -/
theorem makhnevStar_iff_canonical (h : G.IsSRGWith n k 1 2) :
    MakhnevStar G ↔ Canonical G :=
  ⟨fun hs x => canonicalAt_of_makhnevStar h hs x,
   fun hc _ _ _ p' _ _ hL hL' hd h1 h2 =>
     adj_third_of_canonicalAt h hL hL' hd (hc p') h1 h2⟩

/-- **COROLLARY C1, in Makhnev's own words** — the cardinality rendering of (∗)
is equivalent to canonicality. -/
theorem makhnevStarCard_iff_canonical (h : G.IsSRGWith n k 1 2) :
    MakhnevStarCard G ↔ Canonical G :=
  (makhnevStar_iff_card h).symm.trans (makhnevStar_iff_canonical h)

/-- **C1 at v = 99** — the instance the paper cites against Makhnev's Theorem 2
("there is no srg(99,14,1,2) satisfying (∗)", which is CITED and NOT proved
here).  Note what this does and does not say: it identifies two hypotheses.  It
asserts nothing about the existence of an srg(99,14,1,2). -/
theorem makhnevStar_iff_canonical_99 (h : G.IsSRGWith 99 14 1 2) :
    MakhnevStar G ↔ Canonical G :=
  makhnevStar_iff_canonical h

/-- The same at v = 243 (BvLS), where both sides are known to HOLD — the
join distribution computed in log 046 has no 2s. -/
theorem makhnevStar_iff_canonical_243 (h : G.IsSRGWith 243 22 1 2) :
    MakhnevStar G ↔ Canonical G :=
  makhnevStar_iff_canonical h

/-! ### NON-VACUITY — Paley(9)

`MakhnevStar` and `MakhnevStarCard` are ∀-implications, so they would also hold
if no two vertex-disjoint triangles with two cross edges existed.  Paley(9)
settles both halves: it satisfies (∗) (it is canonical — `paley9_canonical`),
AND it contains a concrete pair of vertex-disjoint triangles joined by three
edges, so the premises of both renderings actually FIRE.
-/

/-- Paley(9) satisfies Makhnev's (∗) — via C1 and `paley9_canonical`. -/
theorem paley9_makhnevStar : MakhnevStar paley9 :=
  (makhnevStar_iff_canonical paley9_srg).mpr paley9_canonical

/-- ... in the cardinality rendering too. -/
theorem paley9_makhnevStarCard : MakhnevStarCard paley9 :=
  (makhnevStarCard_iff_canonical paley9_srg).mpr paley9_canonical

/-- **THE PREMISES FIRE.**  Rows 0 and 1 of the 3×3 rook's graph are two
vertex-disjoint triangles, and they are joined by exactly three edges — an
induced triangular PRISM, the object `n₁` counts.  So the hypotheses of
`MakhnevStar` (two lines, disjoint, two aligned cross edges) and of
`MakhnevStarCard` (`2 ≤ join`) are simultaneously satisfiable, `joinSet` is
inhabited, and the bound `join_card_le_three` is ATTAINED. -/
theorem paley9_prism :
    IsLine paley9 ((0 : Fin 3), (0 : Fin 3)) (0, 1) (0, 2) ∧
      IsLine paley9 ((1 : Fin 3), (0 : Fin 3)) (1, 1) (1, 2) ∧
      Disjoint ({((0 : Fin 3), (0 : Fin 3)), (0, 1), (0, 2)} : Finset (Fin 3 × Fin 3))
        ({((1 : Fin 3), (0 : Fin 3)), (1, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) ∧
      paley9.Adj ((0 : Fin 3), (0 : Fin 3)) (1, 0) ∧
      paley9.Adj ((0 : Fin 3), (1 : Fin 3)) (1, 1) ∧
      paley9.Adj ((0 : Fin 3), (2 : Fin 3)) (1, 2) ∧
      (joinSet paley9 ({((0 : Fin 3), (0 : Fin 3)), (0, 1), (0, 2)} : Finset (Fin 3 × Fin 3))
        ({((1 : Fin 3), (0 : Fin 3)), (1, 1), (1, 2)} : Finset (Fin 3 × Fin 3))).card = 3 :=
  ⟨⟨by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide⟩,
   disjoint_triple (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide),
   by decide, by decide, by decide, by decide⟩

/-- **(∗) FIRES ON THAT PRISM**: `paley9_makhnevStar` applied to the two rows
returns the third cross edge, so the implication is used, not merely true. -/
theorem paley9_makhnevStar_fires :
    paley9.Adj ((0 : Fin 3), (2 : Fin 3)) (1, 2) :=
  paley9_makhnevStar (0, 0) (0, 1) (0, 2) (1, 0) (1, 1) (1, 2)
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    (disjoint_triple (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

/-! ### FALSIFIABILITY — the 2-join

Paley(9) shows (∗) is satisfiable and that its premises fire.  The opposite
guard matters just as much: a condition that no graph can violate would make
Corollary C1 an equivalence between two tautologies.  `twoJoin` is the
six-vertex graph consisting of two disjoint triangles joined by exactly TWO
edges — the configuration `n₃` counts — and on it both renderings of (∗) are
FALSE, with the join count taking the value 2 that `join_card_le_three` allows.

`twoJoin` is deliberately NOT an SRG (it is not even regular); it is a witness
about the DEFINITIONS `MakhnevStar` / `MakhnevStarCard` / `joinSet`, which are
stated for arbitrary graphs, not about the λ=1, μ=2 family.  Inside that family
no such witness can be exhibited here — both known members are canonical (log
046), and by C1 a non-canonical one is exactly what nobody has ever produced.

It does satisfy `UniqueTriangle` (`twoJoin_uniqueTriangle`, by `decide`), which
is the only hypothesis `FlagCount.card_fiberOf` needs; that is what turns this
witness from a statement about `MakhnevStar` alone into the m = 2 instance of
the fibre count (`FlagCount.twoJoin_fibre`, log 047).
-/

/-- Adjacency of the 2-join: the triangles `{0,1,2}` and `{3,4,5}` (same
`⌊v/3⌋`), plus the two cross edges `0–3` and `1–4`.  The pair `2–5` is
deliberately absent. -/
def twoJoinAdj (u v : Fin 6) : Prop :=
  (u.val / 3 = v.val / 3 ∧ u ≠ v) ∨
    (u.val + 3 = v.val ∧ u.val ≤ 1) ∨ (v.val + 3 = u.val ∧ v.val ≤ 1)

instance : DecidableRel twoJoinAdj := fun u v =>
  inferInstanceAs (Decidable ((u.val / 3 = v.val / 3 ∧ u ≠ v) ∨
    (u.val + 3 = v.val ∧ u.val ≤ 1) ∨ (v.val + 3 = u.val ∧ v.val ≤ 1)))

/-- **THE 2-JOIN**: two vertex-disjoint triangles joined by exactly two edges. -/
def twoJoin : SimpleGraph (Fin 6) where
  Adj := twoJoinAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel twoJoin.Adj := fun u v =>
  inferInstanceAs (Decidable (twoJoinAdj u v))

/-- Its two triangles really are lines, really are vertex-disjoint, and really
carry the two cross edges `0–3`, `1–4` — while `2–5` is a NON-edge. -/
theorem twoJoin_config :
    IsLine twoJoin 0 1 2 ∧ IsLine twoJoin 3 4 5 ∧
      Disjoint ({0, 1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) ∧
      twoJoin.Adj 0 3 ∧ twoJoin.Adj 1 4 ∧ ¬ twoJoin.Adj 2 5 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
   disjoint_triple (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide),
   by decide, by decide, by decide⟩

/-- The join count of the 2-join is **2** — so the value 2 permitted by
`join_card_le_three` is attained, and `MakhnevStarCard`'s premise `2 ≤ join`
does not already force `join = 3` for formal reasons. -/
theorem twoJoin_join_card :
    (joinSet twoJoin ({0, 1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6))).card = 2 := by
  decide

/-- **`twoJoin` HAS UNIQUE TRIANGLES** — checked by `decide` over all `6⁴`
quadruples.  It is not an SRG (not even regular), but it satisfies the ONLY
hypothesis the join/flag machinery actually needs, so `FlagCount.card_fiberOf`
applies to it.  That is what makes it the m = 2 witness: inside the λ = 1, μ = 2
family no witness with a 2-join can be exhibited, because both known members are
canonical. -/
theorem twoJoin_uniqueTriangle : UniqueTriangle twoJoin := by decide

/-- Paley(9) has unique triangles, from λ = 1. -/
theorem paley9_uniqueTriangle : UniqueTriangle paley9 :=
  uniqueTriangle_of_srg paley9_srg

/-- **`MakhnevStar` IS FALSIFIABLE.** -/
theorem twoJoin_not_makhnevStar : ¬ MakhnevStar twoJoin := by
  intro hs
  exact twoJoin_config.2.2.2.2.2
    (hs 0 1 2 3 4 5 twoJoin_config.1 twoJoin_config.2.1 twoJoin_config.2.2.1
      twoJoin_config.2.2.2.1 twoJoin_config.2.2.2.2.1)

/-- **`MakhnevStarCard` IS FALSIFIABLE**, and by the same witness — its premise
`2 ≤ join` holds there while its conclusion `join = 3` fails. -/
theorem twoJoin_not_makhnevStarCard : ¬ MakhnevStarCard twoJoin := by
  intro hc
  have h3 := hc 0 1 2 3 4 5 twoJoin_config.1 twoJoin_config.2.1 twoJoin_config.2.2.1
    (by rw [twoJoin_join_card])
  rw [twoJoin_join_card] at h3
  exact absurd h3 (by decide)

end Conway99
