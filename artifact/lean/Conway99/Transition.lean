/-
Conway99.Transition — the rooted transition system, and Theorems A, B, C of
`notes/math/thread1-transition-system.md`, formalized.

CONTEXT.  Logs 031–038 rest on a reformulation of the local structure of an
srg(v,k,1,2) at a root `x`:

  * λ = 1 makes `Γ[N(x)]` a perfect matching; write `a′` for the partner of
    `a ∈ N(x)` (`IsPartner`);
  * μ = 2 makes `z ↦ N(z) ∩ N(x)` a bijection from the outside vertices onto
    the NON-matched pairs of `N(x)`; write `z_ab` for the outside vertex
    labelled `{a,b}` (`IsLabel`);
  * λ = 1 applied to `N(a)` therefore pairs up the 12 (in general `k − 2`)
    outside neighbours of `a`, i.e. it defines a perfect matching `M_a` on
    `B_a = N(x) ∖ {a,a′}`, and the family `(M_a)` is the *transition system*
    at `x`.  `M_a(b) = c` is literally the adjacency `z_ab ~ z_ac`.

This file formalizes the setup (T1) and the three theorems the notes grade
PROVED but which had never been machine-checked:

  * `no_three_circuit` — **THEOREM A**: no 3-circuit.  Needs λ = 1 ONLY.
  * `partner_bipartite` — **THEOREM B**: for a matched pair `{a,a′}` the
    bipartite graph between the outside neighbours of `a` and those of `a′`
    is a perfect matching.  Needs λ = 1 and μ = 2.
  * `line_through_of_two_nbrs`, `shared_index_apex`,
    `outside_line_stays_outside`, `line_split_count` — **THE LINE-SPLIT
    THEOREM**: the second subconstituent splits.  The three structural
    statements need λ = 1 only; the arithmetic identity
    `vr = 3(r + 2r(r−1) + 2r(r−1)(r−2)/3)` (at v = 99: 231 = 7 + 84 + 140) is a
    separate pure-ℕ lemma.
    NAMING (2026-08-11).  `notes/math/thread1-transition-system.md` calls this
    "Theorem C"; it is **not** the paper's Theorem C, which is the flag-counting
    identity `6n₁ = Σ_x D(x)` in `Conway99/FlagCount.lean`.  Two distinct
    theorems had the same label; this file uses "line-split theorem" so that
    "THEOREM C" means one thing in the Lean layer and in the arXiv draft.

DESIGN — WHY THERE ARE NO CHOICE FUNCTIONS.  Everything is stated with
*relational* definitions (`IsPartner`, `IsLabel`, `IsApex`, `IsLine`) rather
than with `Classical.choice`-extracted maps `a ↦ a′`, `(a,b) ↦ z_ab`.  Each
relation is proved to be functional (`partner_unique`, `label_unique`,
`apex_unique`), so nothing is lost, and the theorems below then apply to ANY
labelling that a downstream argument happens to have in hand — which is what
`Skeleton.lean` and `CanonicalGeometry.lean` need.  The same discipline as
`Switch2.lean`'s `hspec` form.

SCOPE.  Nothing here is specific to v = 99: every theorem is stated for an
arbitrary `G.IsSRGWith n k 1 μ` (Theorem A and C) or `G.IsSRGWith n k 1 2`
(Theorem B and the label lemmas).  The v = 99 arithmetic appears only in
`line_split_99`.
-/
import Mathlib
import Conway99.SRG

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-! ### μ = 2 bookkeeping

Two utilities used everywhere below: a non-adjacent pair has AT MOST two
common neighbours (`two_common`), and AT LEAST two (`exists_second_common`).
-/

/-- μ = 2, upper half: three common neighbours of a non-adjacent pair cannot
be pairwise distinct. -/
theorem two_common (h : G.IsSRGWith n k 1 2) {u w : V} (hne : u ≠ w)
    (hnadj : ¬ G.Adj u w) {p q r : V}
    (hpu : G.Adj u p) (hpw : G.Adj w p) (hqu : G.Adj u q) (hqw : G.Adj w q)
    (hru : G.Adj u r) (hrw : G.Adj w r) : p = q ∨ p = r ∨ q = r := by
  classical
  have hcard : Fintype.card (G.commonNeighbors u w) = 2 := h.of_not_adj hne hnadj
  have hfin : (G.commonNeighbors u w).toFinset.card = 2 := by
    rw [Set.toFinset_card]; exact hcard
  obtain ⟨s, t, -, hset⟩ := Finset.card_eq_two.mp hfin
  have hmem : ∀ z : V, G.Adj u z → G.Adj w z → z ∈ ({s, t} : Finset V) := by
    intro z h1 h2
    rw [← hset, Set.mem_toFinset, mem_commonNeighbors]
    exact ⟨h1, h2⟩
  have hp := hmem p hpu hpw
  have hq := hmem q hqu hqw
  have hr := hmem r hru hrw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
  rcases hp with rfl | rfl <;> rcases hq with h2 | h2 <;> rcases hr with h3 | h3 <;>
    subst h2 <;> subst h3 <;> tauto

/-- μ = 2, lower half: a non-adjacent pair with one known common neighbour
has a second one. -/
theorem exists_second_common (h : G.IsSRGWith n k 1 2) {u w : V} (hne : u ≠ w)
    (hnadj : ¬ G.Adj u w) {p : V} (hpu : G.Adj u p) (hpw : G.Adj w p) :
    ∃ q, q ≠ p ∧ G.Adj u q ∧ G.Adj w q := by
  have hcard : Fintype.card (G.commonNeighbors u w) = 2 := h.of_not_adj hne hnadj
  obtain ⟨⟨q, hq⟩, hqne⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num)
      (⟨p, (mem_commonNeighbors G).mpr ⟨hpu, hpw⟩⟩ : G.commonNeighbors u w)
  rw [mem_commonNeighbors] at hq
  exact ⟨q, fun hh => hqne (Subtype.ext hh), hq.1, hq.2⟩

/-! ### T1 — the setting: partners, labels, apexes, lines -/

/-- `a′` is the partner of `a` in the perfect matching `Γ[N(x)]`: both are
neighbours of the root `x`, and they are adjacent. -/
def IsPartner (G : SimpleGraph V) (x a a' : V) : Prop :=
  G.Adj x a ∧ G.Adj x a' ∧ G.Adj a a'

/-- `z` is the outside vertex LABELLED `{a,b}`: it is a common neighbour of
`a` and `b`, and it lies outside `N[x]`. -/
def IsLabel (G : SimpleGraph V) (x a b z : V) : Prop :=
  G.Adj a z ∧ G.Adj b z ∧ z ≠ x ∧ ¬ G.Adj x z

/-- `t` is the APEX of the edge `{u,w}`: the third point of the unique line
(triangle) through that edge. -/
def IsApex (G : SimpleGraph V) (u w t : V) : Prop :=
  G.Adj u w ∧ G.Adj u t ∧ G.Adj w t

/-- A *line* is a triangle — by λ = 1 the unique one on each of its edges. -/
def IsLine (G : SimpleGraph V) (p q r : V) : Prop :=
  G.Adj p q ∧ G.Adj p r ∧ G.Adj q r

theorem IsPartner.symm {x a a' : V} (hp : IsPartner G x a a') :
    IsPartner G x a' a :=
  ⟨hp.2.1, hp.1, hp.2.2.symm⟩

/-- The label `{a,b}` is an unordered pair. -/
theorem IsLabel.symm {x a b z : V} (hz : IsLabel G x a b z) : IsLabel G x b a z :=
  ⟨hz.2.1, hz.1, hz.2.2.1, hz.2.2.2⟩

/-- λ = 1: every neighbour of the root has a partner. -/
theorem exists_unique_partner (h : G.IsSRGWith n k 1 μ) {x a : V}
    (hxa : G.Adj x a) : ∃! a', IsPartner G x a a' := by
  obtain ⟨w, hw, huniq⟩ := neighborhood_matching h hxa
  exact ⟨w, ⟨hxa, hw.1, hw.2⟩, fun y hy => huniq y ⟨hy.2.1, hy.2.2⟩⟩

/-- λ = 1: the partner is unique — `a ↦ a′` really is a function. -/
theorem partner_unique (h : G.IsSRGWith n k 1 μ) {x a a₁ a₂ : V}
    (h1 : IsPartner G x a a₁) (h2 : IsPartner G x a a₂) : a₁ = a₂ :=
  unique_common_of_adj h h1.1
    ((mem_commonNeighbors G).mpr ⟨h1.2.1, h1.2.2⟩)
    ((mem_commonNeighbors G).mpr ⟨h2.2.1, h2.2.2⟩)

/-- λ = 1: the matching is a matching — two neighbours of `x` with a common
partner coincide. -/
theorem partner_injective (h : G.IsSRGWith n k 1 μ) {x a b c : V}
    (h1 : IsPartner G x a c) (h2 : IsPartner G x b c) : a = b :=
  partner_unique h h1.symm h2.symm

/-- λ = 1: the apex is unique — an edge lies in exactly one line. -/
theorem apex_unique (h : G.IsSRGWith n k 1 μ) {u w t t' : V}
    (h1 : IsApex G u w t) (h2 : IsApex G u w t') : t = t' :=
  unique_common_of_adj h h1.1
    ((mem_commonNeighbors G).mpr ⟨h1.2.1, h1.2.2⟩)
    ((mem_commonNeighbors G).mpr ⟨h2.2.1, h2.2.2⟩)

/-- λ = 1: every edge HAS an apex — the triangle on an edge EXISTS (and is
unique by `apex_unique`), so `IsApex` really is a total function on edges.
This is what discharges the apex hypotheses of
`CanonicalGeometry.exists_far_corner`; without it "the far corner exists" is
only conditional on somebody handing over the two apexes. -/
theorem exists_apex (h : G.IsSRGWith n k 1 μ) {u w : V} (huw : G.Adj u w) :
    ∃! t, IsApex G u w t := by
  obtain ⟨t, ht, huniq⟩ := neighborhood_matching h huw
  exact ⟨t, ⟨huw, ht.1, ht.2⟩, fun y hy => huniq y ⟨hy.2.1, hy.2.2⟩⟩

/-- λ = 1, μ = 2: every NON-matched pair of neighbours of `x` carries a label
vertex.  (This is `SRG.outside_common_neighbor` in `IsLabel` clothing.) -/
theorem exists_label (h : G.IsSRGWith n k 1 2) {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : ¬ G.Adj a b) (hne : a ≠ b) :
    ∃ z, IsLabel G x a b z := by
  obtain ⟨w, ⟨hwx, hwa, hwb, hwadj⟩, -⟩ := outside_common_neighbor h hxa hxb hab hne
  exact ⟨w, hwa, hwb, hwx, hwadj⟩

/-- λ = 1, μ = 2: the label vertex is unique — `{a,b} ↦ z_ab` is a function.
-/
theorem label_unique (h : G.IsSRGWith n k 1 2) {x a b z z' : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : ¬ G.Adj a b) (hne : a ≠ b)
    (hz : IsLabel G x a b z) (hz' : IsLabel G x a b z') : z = z' := by
  rcases two_common h hne hab hxa.symm hxb.symm hz.1 hz.2.1 hz'.1 hz'.2.1 with
    hc | hc | hc
  · exact absurd hc.symm hz.2.2.1
  · exact absurd hc.symm hz'.2.2.1
  · exact hc

/-- The label of an outside vertex is a NON-matched pair: no outside vertex
is adjacent to both ends of a matched pair.  (λ = 1: the edge `a a′` already
lies in the triangle `{x,a,a′}`.) -/
theorem label_not_matched (h : G.IsSRGWith n k 1 μ) {x a a' z : V}
    (hp : IsPartner G x a a') (haz : G.Adj a z) (hzx : z ≠ x) : ¬ G.Adj a' z := by
  intro hz
  exact hzx (unique_common_of_adj h hp.2.2
    ((mem_commonNeighbors G).mpr ⟨haz, hz⟩)
    ((mem_commonNeighbors G).mpr ⟨hp.1.symm, hp.2.1.symm⟩))

/-- Two label vertices at `a` with matched second indices are distinct
(`z_ab ≠ z_ab′`) — otherwise the common vertex would be adjacent to both ends
of the matched pair `{b,b′}`. -/
theorem label_ne_of_partner (h : G.IsSRGWith n k 1 μ) {x a b b' z z' : V}
    (hp : IsPartner G x b b') (hz : IsLabel G x a b z) (hz' : IsLabel G x a b' z') :
    z ≠ z' := by
  rintro rfl
  exact label_not_matched h hp hz.2.1 hz.2.2.1 hz'.2.1

/-! ### T2 — THEOREM A: no 3-circuits

A 3-circuit is `M_a(b) = c`, `M_b(a) = c`, `M_c(a) = b`, i.e. the three label
vertices `z_ab`, `z_ac`, `z_bc` pairwise adjacent.  Then the edge
`z_ab z_ac` lies in the triangle with `a` AND in the triangle with `z_bc`;
λ = 1 forces `z_bc = a`, absurd because `a ~ x` while `z_bc ≁ x`.
-/

/-- **THEOREM A, core form** (λ = 1 only, no labels): if two outside
neighbours `zab`, `zac` of `a ∈ N(x)` are adjacent, then no vertex outside
`N[x]` is adjacent to both — their apex is `a` itself. -/
theorem no_three_circuit_core (h : G.IsSRGWith n k 1 μ) {x a zab zac zbc : V}
    (hxa : G.Adj x a) (haab : G.Adj a zab) (haac : G.Adj a zac)
    (hedge : G.Adj zab zac) (h1 : G.Adj zab zbc) (h2 : G.Adj zac zbc)
    (hout : ¬ G.Adj x zbc) : False := by
  have hzbc : zbc = a := unique_common_of_adj h hedge
    ((mem_commonNeighbors G).mpr ⟨h1, h2⟩)
    ((mem_commonNeighbors G).mpr ⟨haab.symm, haac.symm⟩)
  exact hout (hzbc ▸ hxa)

/-- **THEOREM A — NO 3-CIRCUITS.**  For `a, b, c ∈ N(x)` pairwise
non-matched, the transitions `M_a(b) = c`, `M_b(a) = c`, `M_c(a) = b` cannot
all hold: in label form, `z_ab`, `z_ac`, `z_bc` are not pairwise adjacent.
Consequently every circuit of the transition system has length ≥ 4.

Only λ = 1 is used (μ = 2 enters only through the existence of the labels,
which is a hypothesis here). -/
theorem no_three_circuit (h : G.IsSRGWith n k 1 μ) {x a b c zab zac zbc : V}
    (hxa : G.Adj x a)
    (hab : IsLabel G x a b zab) (hac : IsLabel G x a c zac)
    (hbc : IsLabel G x b c zbc) :
    ¬ (G.Adj zab zac ∧ G.Adj zab zbc ∧ G.Adj zac zbc) := by
  rintro ⟨e1, e2, e3⟩
  exact no_three_circuit_core h hxa hab.1 hac.1 e1 e2 e3 hbc.2.2.2

/-! ### T3 — THEOREM B: the `a`/`a′` bipartite structure is a perfect matching
-/

/-- **THEOREM B.**  Let `{a,a′}` be a matched pair of `N(x)` and let `z` be an
outside vertex adjacent to `a` (so `z ≁ a′` by λ = 1).  Then `z` has EXACTLY
ONE outside neighbour that is adjacent to `a′`.

Since the statement is symmetric in `a` and `a′`, the bipartite graph induced
between `N(a) ∖ N[x]` and `N(a′) ∖ N[x]` is a perfect matching — Theorem B of
the transition-system note.

Proof: `a′ ≁ z`, and `a` is one of their two (μ = 2) common neighbours; the
other, `w`, cannot be `x` (`x ≁ z`) and cannot be a neighbour of `x` (else
`w` and `a` would be two common neighbours of the ADJACENT pair `{x,a′}`,
contradicting λ = 1). -/
theorem partner_bipartite (h : G.IsSRGWith n k 1 2) {x a a' z : V}
    (hp : IsPartner G x a a') (haz : G.Adj a z) (hzx : z ≠ x)
    (hzout : ¬ G.Adj x z) :
    ∃! w, (w ≠ x ∧ ¬ G.Adj x w) ∧ G.Adj a' w ∧ G.Adj z w := by
  have hna : ¬ G.Adj a' z := label_not_matched h hp haz hzx
  have hne : a' ≠ z := by rintro rfl; exact hzout hp.2.1
  -- `a` is a common neighbour of the non-adjacent pair `{a′, z}`
  have ha1 : G.Adj a' a := hp.2.2.symm
  have ha2 : G.Adj z a := haz.symm
  obtain ⟨w, hwa, hw1, hw2⟩ := exists_second_common h hne hna ha1 ha2
  have hwx : w ≠ x := by rintro rfl; exact hzout hw2.symm
  have hwout : ¬ G.Adj x w := by
    intro hxw
    exact hwa (unique_common_of_adj h hp.2.1
      ((mem_commonNeighbors G).mpr ⟨hxw, hw1⟩)
      ((mem_commonNeighbors G).mpr ⟨hp.1, ha1⟩))
  refine ⟨w, ⟨⟨hwx, hwout⟩, hw1, hw2⟩, ?_⟩
  rintro y ⟨⟨hyx, hyout⟩, hy1, hy2⟩
  rcases two_common h hne hna ha1 ha2 hw1 hw2 hy1 hy2 with hc | hc | hc
  · exact absurd hc.symm hwa
  · exact absurd (hc ▸ hp.1) hyout
  · exact hc.symm

/-! ### T4 — THE LINE-SPLIT THEOREM: the second subconstituent splits

(Called "Theorem C" in `notes/math/thread1-transition-system.md`.  NOT the
paper's Theorem C — that is the counting identity in `FlagCount.lean`.)

Relative to a root `x`, the lines of `Γ` fall into exactly three classes:
those through `x`; those missing `x` but meeting `N(x)`; and those disjoint
from `N[x]`.  The content is that the second class meets `N(x)` in exactly
ONE point (`line_through_of_two_nbrs`), that the lines on an index-sharing
("D-") edge of the second subconstituent are of the second kind
(`shared_index_apex`), and that the lines on a disjoint-label edge are of the
third kind (`outside_line_stays_outside`).  At v = 99 the three classes have
sizes 7, 84, 140 — `line_split_count` / `line_split_99`.
-/

/-- **LINE SPLIT, step 1** (λ = 1).  A line meeting `N(x)` in two points passes
through `x`.  Equivalently: a line NOT through `x` meets `N(x)` at most once.
-/
theorem line_through_of_two_nbrs (h : G.IsSRGWith n k 1 μ) {x p q r : V}
    (hL : IsLine G p q r) (hxp : G.Adj x p) (hxq : G.Adj x q) : x = r :=
  unique_common_of_adj h hL.1
    ((mem_commonNeighbors G).mpr ⟨hxp.symm, hxq.symm⟩)
    ((mem_commonNeighbors G).mpr ⟨hL.2.1, hL.2.2⟩)

/-- **LINE SPLIT, step 1'** — the trichotomy in the form used downstream: a
line `{p,q,r}` missing `x` meets `N(x)` in AT MOST ONE of its three points. -/
theorem line_off_root_meets_once (h : G.IsSRGWith n k 1 μ) {x p q r : V}
    (hL : IsLine G p q r) (hp : x ≠ p) (hq : x ≠ q) (hr : x ≠ r) :
    ¬ (G.Adj x p ∧ G.Adj x q) ∧ ¬ (G.Adj x p ∧ G.Adj x r) ∧
      ¬ (G.Adj x q ∧ G.Adj x r) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩; exact hr (line_through_of_two_nbrs h hL h1 h2)
  · rintro ⟨h1, h2⟩
    exact hq (line_through_of_two_nbrs h ⟨hL.2.1, hL.1, hL.2.2.symm⟩ h1 h2)
  · rintro ⟨h1, h2⟩
    exact hp (line_through_of_two_nbrs h ⟨hL.2.2, hL.1.symm, hL.2.1.symm⟩ h1 h2)

/-- **LINE SPLIT, step 2** (λ = 1).  If two outside vertices `z`, `w` are
adjacent and share the index `a ∈ N(x)`, then `a` is the apex of the edge
`{z,w}`: the line through an index-sharing edge is `{a, z, w}`. -/
theorem shared_index_apex (h : G.IsSRGWith n k 1 μ) {a z w t : V}
    (haz : G.Adj a z) (haw : G.Adj a w) (hzw : G.Adj z w)
    (hzt : G.Adj z t) (hwt : G.Adj w t) : t = a :=
  unique_common_of_adj h hzw
    ((mem_commonNeighbors G).mpr ⟨hzt, hwt⟩)
    ((mem_commonNeighbors G).mpr ⟨haz.symm, haw.symm⟩)

/-- **LINE SPLIT, step 2'** — the form the note states: an index-sharing edge
of the second subconstituent lies in NO triangle inside the second
subconstituent. -/
theorem shared_index_no_outside_triangle (h : G.IsSRGWith n k 1 μ)
    {x a z w t : V} (hxa : G.Adj x a)
    (haz : G.Adj a z) (haw : G.Adj a w) (hzw : G.Adj z w)
    (hzt : G.Adj z t) (hwt : G.Adj w t) (htout : ¬ G.Adj x t) : False :=
  htout ((shared_index_apex h haz haw hzw hzt hwt) ▸ hxa)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **LINE SPLIT, step 3** (no SRG axioms needed).  An edge of the second
subconstituent whose two endpoints have DISJOINT labels — no neighbour of `x`
is adjacent to both — has its whole line inside the second subconstituent. -/
theorem outside_line_stays_outside {x z w t : V}
    (hzout : ¬ G.Adj x z) (hzt : G.Adj z t) (hwt : G.Adj w t)
    (hdisj : ∀ u, G.Adj x u → G.Adj u z → G.Adj u w → False) :
    t ≠ x ∧ ¬ G.Adj x t := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact hzout hzt.symm
  · intro hxt; exact hdisj t hxt hzt.symm hwt.symm

/-- **LINE SPLIT, the count** (pure arithmetic).  Write `r = k/2`, so that
`v = 1 + 2r²`.  A vertex is on `r` lines, so there are `vr/3` lines in all;
`r` of them pass through the root `x`, `2r(r−1)` meet `N(x)` without passing
through `x` (each of the `2r` points of `N(x)` is on `r − 1` lines other than
its own line through `x`), and the rest lie entirely outside `N[x]`.  The
identity says the three classes account for every line, with no slack:

  `v·r = 3·r + 3·(2r(r−1)) + 2r(r−1)(r−2)`.

Stated multiplicatively (both sides times 3) to stay inside ℕ.  At `r = 7`:
`99·7 = 693 = 3·(7 + 84 + 140)`. -/
theorem line_split_count (r : ℕ) (hr : 2 ≤ r) :
    (1 + 2 * r ^ 2) * r =
      3 * r + 3 * (2 * r * (r - 1)) + 2 * r * (r - 1) * (r - 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h1 : s + 2 - 1 = s + 1 := by omega
  have h2 : s + 2 - 2 = s := by omega
  rw [h1, h2]
  ring

/-- **LINE SPLIT at v = 99**: the 231 lines split as 7 + 84 + 140. -/
theorem line_split_99 :
    (1 + 2 * 7 ^ 2) = 99 ∧ 99 * 7 = 3 * 231 ∧ (231 : ℕ) = 7 + 84 + 140 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The same split at v = 243 (`r = 11`): 891 = 11 + 220 + 660 — the figure
`notes/math/thread1-transition-system.md` records for BvLS(243). -/
theorem line_split_243 :
    (1 + 2 * 11 ^ 2) = 243 ∧ 243 * 11 = 3 * 891 ∧ (891 : ℕ) = 11 + 220 + 660 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Conway99
