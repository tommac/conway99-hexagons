/-
Conway99.FlagCount — **THEOREM C**: the flag-counting identity that converts our
SAT certificates into the literature's currency (prisms and 2-joins).

CONTEXT.  `notes/math/local-canonicality-conjecture.md` §2 states, hand-proved:

  > **THEOREM C.**  In any srg(1+2r², 2r, 1, 2), with `D(x)` the number of
  > canonical transitions at `x` (max `2r(r−1)`), `n₁` the number of induced
  > triangular prisms and `n₃` the number of pairs of vertex-disjoint triangles
  > joined by exactly two edges,
  >     `n₁ = (1/6)·Σ_x D(x)`   and   `n₃ = (1/2)·Σ_x (2r(r−1) − D(x))`.

That was the one load-bearing new result of the forthcoming paper with no
machine-checked proof.  This file supplies it, in the division-free form

  `theoremC_n1 : 6 * n1 G = ∑ x, D G x`
  `theoremC_n3 : 2 * n3 G = ∑ x, (2 * r * (r - 1) - D G x)`   (hypothesis `k = 2r`)

THE ARGUMENT, and where each constant lives.  A **flag** is a triple `(x,a,b)`
with `a, b ∈ N(x)` in different matched classes (`IsFlag`); there are `k(k−2)`
of them at each root (`card_flagsAt`), two per transition (`card_image_classOf`).
The flag map sends `(x,a,b)` to the ordered pair of triangles
`T = {a, z_ab, y}` (`y` = the apex of the edge `a z_ab`) and `T′ = {x, b, b′}`
(`FlagImage`); the pair is vertex-disjoint and its join count is 3 exactly when
the flag is canonical, 2 otherwise (`flagImage_join_three`/`flagImage_join_two`).
The fibre over an ordered pair whose join has `m` edges is `m² − m`
(`card_fiberOf`) — the flag is determined by the ordered pair of distinct CROSS
ENDS `(x,b)` in `T′`, and the cross ends biject with the join because the cross
edges form a matching.  So `m = 3` gives 6 flags per ORDERED prism pair (12 per
unordered prism) and `m = 2` gives 2 per ordered 2-join pair (4 per unordered) —
log 046's "12 and 4", confirmed, with the factor 2 between them made explicit
rather than divided away.

WHAT IS PROVED HERE (all sorry-free, no `native_decide`).

  * `card_fiberOf` — the fibre count `m² − m`, the whole content of the identity.
    Its hypothesis is `UniqueTriangle G` ("every edge lies in at most one
    triangle"), NOT the srg axioms; λ = 1 supplies it.
  * `theoremC_n1`, `theoremC_n3` — Theorem C.
  * `reimbayev_prop5` — `12·n₁ + 4·n₃ = n·k·(k−2)`, i.e. Reimbayev's published
    Prop. 5(6) `3n₁ + n₃ = ¼nk(k−2)` (arXiv:2409.10620), DERIVED here, with the
    `Σ D` terms cancelling identically.
  * `n3_eq_zero_iff_canonical`, `n3_eq_zero_iff_makhnevStar` — `n₃ = 0` iff
    canonical at every vertex iff Makhnev's (∗).  This re-proves Corollary C1 by
    counting; `Makhnev.lean` proves it directly.
  * `canonicalAt_iff_forall_flag`, `D_eq_card_transitionsAt`, `D_le`,
    `card_transitionsAt` — the bridge between `D` and `CanonicalAt`:
    `D(x) ≤ 2r(r−1)` always, with equality iff `CanonicalAt G x`.
  * `conway99_n1_le`, `conway99_n3_ge` — at `v = 99`, FROM the hypothesis
    `D(x) ≤ 77`: `n₁ ≤ 1270` and `n₃ ≥ 348`.  The divisibility refinement
    (`Σ D ≤ 7620`, not 7623) is automatic: `Σ D = 6·n₁`.
  * §F15 `paley9_prism_fibre = 6`, `twoJoin_fibre = 2`, `paley9_flagsAt_card = 8`,
    `paley9_canonFlagsAt_card = 8`, `paley9_D_computed = 4` — NON-VACUITY THAT
    CAN FAIL: each is a `decide` straight off the definitions, on a graph where
    the answer is known independently, and each is stated ALONGSIDE the value
    the theorems predict.  BOTH fibre branches are covered, `m = 3` on Paley(9)
    and `m = 2` on `twoJoin`.
  * `paley9_n1 = 6`, `paley9_n3 = 0` — the identity's PREDICTION on the one small
    member of the family.  These agree with the brute-force counts of
    `notes/math/theorem_c_check.py`, but the agreement is checked OUTSIDE Lean:
    both are derived from the theorems above and so cannot falsify them.  §F15
    is where the falsifiable checks live.

WHERE THE CONSTANTS ARE ARBITRATED, and by what.

  * INSIDE Lean, falsifiably: §F15's `decide` computations (above).
  * INSIDE Lean, but NOT an arbiter: `reimbayev_prop5`.  It is DERIVED from
    `card_canonFlagSet_n1`, `card_badFlagSet_n3` and the total flag count — the
    very lemmas one would want it to check — so it cannot fail; Lean proves no
    false statements.  Its force is real but EXTERNAL: a reader must compare
    `12·n₁ + 4·n₃ = n·k·(k−2)` with Reimbayev's published
    `3n₁ + n₃ = ¼nk(k−2)`, and our `n₁`, `n₃` with his.  That comparison was
    performed numerically (18 = 18 on Paley(9); 26,730 = 26,730 on BvLS(243))
    and it holds; it also PINS the unordered reading — the ordered one gives
    36 ≠ 18 — which is why `n1`/`n3` are `edgeFinset` counts here.
  * OUTSIDE Lean: `notes/math/theorem_c_check.py` (121 checks over ten λ=1
    graphs, 0 failures), which counts `n₁`, `n₃` and every fibre by brute
    force.  Note which graphs there actually carry the "4": only the random
    partial Steiner systems.  Paley(9), BvLS(243), H(3,3), H(4,3), GQ(2,2) and
    GQ(2,4) all have `n₃ = 0` and are ZERO-POWER against the 2-join constant.

WHAT IS *NOT* PROVED HERE — read this before quoting anything.

  * **`D(x) ≤ 77` IS NOT A THEOREM OF THIS FILE.**  It enters `conway99_n1_le`
    and `conway99_n3_ge` as an explicit hypothesis `hD`.  It is the SAT/DRAT
    certificate of logs 031–032 (`D ≥ 78` refuted; drat-trim + cake_lpr
    VERIFIED), not a Lean proof.  Nothing here says an srg(99,14,1,2) does or
    does not exist; `conway99_n1_le` is a statement about a hypothetical graph.
  * **`n₁` and `n₃` are counts of PAIRS OF TRIANGLES**, namely edge counts of the
    graphs `joinGraph G 3` and `joinGraph G 2` on `Finset V`.  That such a pair
    spans an induced prism (resp. 2-join) is immediate — the join count counts
    ALL cross edges — but the converse reading, "every induced prism subgraph
    arises from exactly one such pair", is NOT proved here.  It needs "a prism
    contains exactly two triangles", which is true in a λ=1 graph and is not
    formalized.
  * **Reimbayev's Theorem 2 (the hexagon count) is not formalized**, so the
    hexagon corollary `≥ 209,634` of the note is NOT available here.  Only
    Prop. 5(6) is, and it is proved rather than cited.
  * The `μ ≠ 2` generalisation `12n₁ + 4n₃ = nk(k−2)(μ−1)` is not stated; every
    theorem below with a `n₃` in it assumes `μ = 2` (labels must be unique).
  * `theoremC_n3` takes `k = 2r` as a hypothesis; it does NOT prove `k` is even,
    nor `n = 1 + 2r²`.  Feasibility is not touched.
  * **The 2-join half has no witness INSIDE the family, and cannot have one.**
    `flagImage_join_two`, `card_badFlagSet`, `card_badFlagSet_n3` and
    `theoremC_n3` all carry `G.IsSRGWith n k 1 2`, and are never instantiated at
    a concrete graph anywhere in this library — both known members of the family
    are canonical, so both have `n₃ = 0`.  What §F15 supplies is the fibre
    branch `m = 2` on `twoJoin`, which is the arithmetic content ("4 flags per
    2-join") but not those SRG-specific lemmas.  Their external evidence is
    `notes/math/theorem_c_check.py`'s random partial Steiner systems (9,775
    2-joins, fibre 4 on every one; 1,196 non-canonical transitions), which live
    outside Lean.
  * No `Classical.choice`-extracted flag map: `FlagImage` is a relation, proved
    functional (`exists_flagImage` + `flagImage_unique`), in the style of
    `Transition.lean` and `Switch2.lean`.  `classOf` is likewise choice-free.
-/
import Mathlib
import Conway99.SRG
import Conway99.Transition
import Conway99.CanonicalGeometry
import Conway99.Makhnev

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-! ### F0 — triangles as `Finset`s, the join, and its endpoint set -/

/-- A 3-clique is a line, written out. -/
theorem isNClique_three_iff {T : Finset V} :
    G.IsNClique 3 T ↔ ∃ p q r, IsLine G p q r ∧ T = {p, q, r} := by
  rw [SimpleGraph.is3Clique_iff]
  constructor
  · rintro ⟨a, b, c, h1, h2, h3, rfl⟩; exact ⟨a, b, c, ⟨h1, h2, h3⟩, rfl⟩
  · rintro ⟨a, b, c, ⟨h1, h2, h3⟩, rfl⟩; exact ⟨a, b, c, h1, h2, h3, rfl⟩

theorem isNClique_three_of_line {p q r : V} (hL : IsLine G p q r) :
    G.IsNClique 3 ({p, q, r} : Finset V) :=
  isNClique_three_iff.mpr ⟨p, q, r, hL, rfl⟩

/-- **THE BACKBONE, `Finset` form**: a vertex off a triangle has at most one
neighbour on it.  Hypothesis is `UniqueTriangle` — "every edge lies in at most
one triangle" — NOT the srg axioms; λ = 1 supplies it (`uniqueTriangle_of_srg`)
and so do non-regular graphs such as `twoJoin`. -/
theorem cross_at_most_one_finset (hut : UniqueTriangle G) {T : Finset V}
    (hT : G.IsNClique 3 T) {u : V} (hu : u ∉ T) {v w : V} (hv : v ∈ T) (hw : w ∈ T)
    (huv : G.Adj u v) (huw : G.Adj u w) : v = w := by
  obtain ⟨p, q, r, hL, rfl⟩ := isNClique_three_iff.mp hT
  exact cross_at_most_one_ut hut hL hu hv hw huv huw

/-- The join count is symmetric. -/
theorem joinSet_card_comm (T T' : Finset V) :
    (joinSet G T T').card = (joinSet G T' T).card := by
  refine Finset.card_nbij' (fun e => (e.2, e.1)) (fun e => (e.2, e.1)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, mem_joinSet] at he ⊢
    exact ⟨he.2.1, he.1, he.2.2.symm⟩
  · intro e he
    simp only [Finset.mem_coe, mem_joinSet] at he ⊢
    exact ⟨he.2.1, he.1, he.2.2.symm⟩
  · intro e _; simp
  · intro e _; simp

/-- The **CROSS ENDS** of the pair `(T, T')`: the points of `T'` that carry a
cross edge to `T`.  By the backbone this set is in bijection with the join. -/
def crossEnds (G : SimpleGraph V) [DecidableRel G.Adj] (T T' : Finset V) : Finset V :=
  T'.filter fun w => ∃ u ∈ T, G.Adj u w

theorem mem_crossEnds {T T' : Finset V} {w : V} :
    w ∈ crossEnds G T T' ↔ w ∈ T' ∧ ∃ u ∈ T, G.Adj u w := by
  simp [crossEnds]

/-- **THE CROSS EDGES ARE A MATCHING, counted**: the number of cross ends in `T'`
equals the join count.  (Unique triangles only, through
`cross_at_most_one_finset`.) -/
theorem card_crossEnds (hut : UniqueTriangle G) {T T' : Finset V}
    (hT : G.IsNClique 3 T) (hdisj : Disjoint T T') :
    (crossEnds G T T').card = (joinSet G T T').card := by
  refine (Finset.card_nbij (fun e => e.2) ?_ ?_ ?_).symm
  · intro e he
    simp only [Finset.mem_coe, mem_joinSet] at he
    simp only [Finset.mem_coe, mem_crossEnds]
    exact ⟨he.2.1, e.1, he.1, he.2.2⟩
  · intro e1 h1 e2 h2 hsnd
    simp only [Finset.mem_coe, mem_joinSet] at h1 h2
    have hsnd' : e1.2 = e2.2 := hsnd
    have hnot : e1.2 ∉ T := Finset.disjoint_right.mp hdisj h1.2.1
    have hfst : e1.1 = e2.1 := by
      refine cross_at_most_one_finset hut hT hnot h1.1 h2.1 h1.2.2.symm ?_
      rw [hsnd']; exact h2.2.2.symm
    exact Prod.ext hfst hsnd'
  · intro w hw
    simp only [Finset.mem_coe, mem_crossEnds] at hw
    obtain ⟨hwT', u, huT, huw⟩ := hw
    exact ⟨(u, w), by simp only [Finset.mem_coe, mem_joinSet]; exact ⟨huT, hwT', huw⟩, rfl⟩

/-! ### F1 — flags, canonical flags, and the flag map -/

/-- A **FLAG** at the root `x`: an ordered pair `(a,b)` of neighbours of `x`
lying in DIFFERENT matched classes of `Γ[N(x)]`.  (For `a, b ∈ N(x)`, "different
classes" is exactly `a ≠ b ∧ a ≁ b` — `not_adj_of_ne_class`.)  There are
`k(k−2) = 4r(r−1)` flags at each root, two for each of the `2r(r−1)`
transitions. -/
def IsFlag (G : SimpleGraph V) (x a b : V) : Prop :=
  G.Adj x a ∧ G.Adj x b ∧ a ≠ b ∧ ¬ G.Adj a b

/-- A flag is **CANONICAL** when the transition it names is: `z_ab ~ z_ab′`.
This is `CanonicalAt` localised at the single transition `(a, {b,b′})`; see
`canonicalAt_iff_forall_flag`. -/
def IsCanonFlag (G : SimpleGraph V) (x a b : V) : Prop :=
  ∃ b' z z', IsPartner G x b b' ∧ IsLabel G x a b z ∧ IsLabel G x a b' z' ∧ G.Adj z z'

/-- **THE FLAG MAP**, relationally (the style of `Transition.lean` — no
`Classical.choice`-extracted functions).  The flag `(x,a,b)` is sent to the
ordered pair of triangles `T = {a, z_ab, y}` (`y` = apex of the edge `a z_ab`)
and `T′ = {x, b, b′}` (the line through `x` and `b`).  `flagImage_unique` proves
this really is a function on flags. -/
def FlagImage (G : SimpleGraph V) (x a b : V) (T T' : Finset V) : Prop :=
  ∃ z y b', IsLabel G x a b z ∧ IsApex G a z y ∧ IsPartner G x b b' ∧
    T = {a, z, y} ∧ T' = {x, b, b'}

/-- The data attached to a flag: partner, both label vertices, and the apex.
Everything downstream is a consequence of this one existence lemma. -/
theorem flag_data (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b) :
    ∃ b' z y z', IsPartner G x b b' ∧ a ≠ b' ∧ ¬ G.Adj a b' ∧
      IsLabel G x a b z ∧ IsApex G a z y ∧ IsLabel G x a b' z' := by
  obtain ⟨b', hp, -⟩ := exists_unique_partner h hf.2.1
  have hab' : a ≠ b' := by
    rintro rfl; exact hf.2.2.2 hp.2.2.symm
  obtain ⟨-, hnab'⟩ := not_adj_of_ne_class h hp hf.1 hf.2.2.1 hab'
  obtain ⟨z, hz⟩ := exists_label h hf.1 hf.2.1 hf.2.2.2 hf.2.2.1
  obtain ⟨z', hz'⟩ := exists_label h hf.1 hp.2.1 hnab' hab'
  obtain ⟨y, hy, -⟩ := exists_apex h hz.1
  exact ⟨b', z, y, z', hp, hab', hnab', hz, hy, hz'⟩

/-- Every flag HAS an image pair. -/
theorem exists_flagImage (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b) :
    ∃ T T', FlagImage G x a b T T' := by
  obtain ⟨b', z, y, z', hp, -, -, hz, hy, -⟩ := flag_data h hf
  exact ⟨{a, z, y}, {x, b, b'}, z, y, b', hz, hy, hp, rfl, rfl⟩

/-- The image pair is UNIQUE — the flag map is a function.  (Partner, label and
apex are each unique: `partner_unique`, `label_unique`, `apex_unique`.) -/
theorem flagImage_unique (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b)
    {T₁ T₁' T₂ T₂' : Finset V} (h1 : FlagImage G x a b T₁ T₁')
    (h2 : FlagImage G x a b T₂ T₂') : T₁ = T₂ ∧ T₁' = T₂' := by
  obtain ⟨z₁, y₁, b₁, hz₁, hy₁, hp₁, rfl, rfl⟩ := h1
  obtain ⟨z₂, y₂, b₂, hz₂, hy₂, hp₂, rfl, rfl⟩ := h2
  have hb : b₁ = b₂ := partner_unique h hp₁ hp₂
  subst hb
  have hz : z₁ = z₂ := label_unique h hf.1 hf.2.1 hf.2.2.2 hf.2.2.1 hz₁ hz₂
  subst hz
  have hy : y₁ = y₂ := apex_unique h hy₁ hy₂
  subst hy
  exact ⟨rfl, rfl⟩

/-- Both members of an image pair are triangles. -/
theorem flagImage_cliques {x a b : V} {T T' : Finset V}
    (him : FlagImage G x a b T T') : G.IsNClique 3 T ∧ G.IsNClique 3 T' := by
  obtain ⟨z, y, b', hz, hy, hp, rfl, rfl⟩ := him
  exact ⟨isNClique_three_of_line ⟨hy.1, hy.2.1, hy.2.2⟩,
    isNClique_three_of_line ⟨hp.1, hp.2.1, hp.2.2⟩⟩

/-- An image pair is vertex-disjoint (`Makhnev.flag_disjoint`). -/
theorem flagImage_disjoint (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b)
    {T T' : Finset V} (him : FlagImage G x a b T T') : Disjoint T T' := by
  obtain ⟨z, y, b', hz, hy, hp, rfl, rfl⟩ := him
  obtain ⟨b₀, z₀, y₀, z₀', hp₀, hab', -, -, -, -⟩ := flag_data h hf
  have : b' = b₀ := partner_unique h hp hp₀
  subst this
  exact flag_disjoint h hf.1 hp hf.2.2.1 hab' hz hy

/-- **CANONICALITY IS THE THIRD CROSS EDGE, first half**: for a canonical flag
the apex `y` of the edge `a z_ab` IS the second label vertex `z_ab′`. -/
theorem canonFlag_apex_isLabel (h : G.IsSRGWith n k 1 2) {x a b b' z y : V}
    (hf : IsFlag G x a b) (hp : IsPartner G x b b') (hz : IsLabel G x a b z)
    (hy : IsApex G a z y) (hcan : IsCanonFlag G x a b) : IsLabel G x a b' y := by
  obtain ⟨b₂, z₂, z', hp₂, hz₂, hz', hadj⟩ := hcan
  have hb : b₂ = b' := partner_unique h hp₂ hp
  subst hb
  have hzz : z₂ = z := label_unique h hf.1 hf.2.1 hf.2.2.2 hf.2.2.1 hz₂ hz
  subst hzz
  have : z' = y :=
    unique_common_of_adj h hz.1
      ((mem_commonNeighbors G).mpr ⟨hz'.1, hadj⟩)
      ((mem_commonNeighbors G).mpr ⟨hy.2.1, hy.2.2⟩)
  exact this ▸ hz'

/-- **A CANONICAL FLAG'S IMAGE IS A PRISM**: join count 3. -/
theorem flagImage_join_three (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b)
    {T T' : Finset V} (him : FlagImage G x a b T T') (hcan : IsCanonFlag G x a b) :
    (joinSet G T T').card = 3 := by
  have hdisj := flagImage_disjoint h hf him
  obtain ⟨z, y, b', hz, hy, hp, rfl, rfl⟩ := him
  have hlab' : IsLabel G x a b' y := canonFlag_apex_isLabel h hf hp hz hy hcan
  exact join_card_eq_three h ⟨hy.1, hy.2.1, hy.2.2⟩ ⟨hp.1, hp.2.1, hp.2.2⟩ hdisj
    hf.1.symm hz.2.1.symm hlab'.2.1.symm

/-- **A NON-CANONICAL FLAG'S IMAGE IS A 2-JOIN**: join count 2.
(`Makhnev.join_card_eq_two_of_not_canonical`.) -/
theorem flagImage_join_two (h : G.IsSRGWith n k 1 2) {x a b : V} (hf : IsFlag G x a b)
    {T T' : Finset V} (him : FlagImage G x a b T T') (hcan : ¬ IsCanonFlag G x a b) :
    (joinSet G T T').card = 2 := by
  obtain ⟨z, y, b', hz, hy, hp, rfl, rfl⟩ := him
  obtain ⟨b₀, z₀, y₀, z₀', hp₀, hab', -, hz₀, -, hz₀'⟩ := flag_data h hf
  have hb : b' = b₀ := partner_unique h hp hp₀
  subst hb
  have hzz : z = z₀ := label_unique h hf.1 hf.2.1 hf.2.2.2 hf.2.2.1 hz hz₀
  subst hzz
  have hnadj : ¬ G.Adj z z₀' := fun hh => hcan ⟨b', z, z₀', hp, hz, hz₀', hh⟩
  exact (join_card_eq_two_of_not_canonical h hf.1 hp hf.2.2.1 hab' hz hz₀' hy hnadj).2

/-! ### F2 — decidability, so that everything below is a `Finset` -/

instance decidableIsPartner (G : SimpleGraph V) [DecidableRel G.Adj] (x a a' : V) :
    Decidable (IsPartner G x a a') := by unfold IsPartner; infer_instance

instance decidableIsLabel (G : SimpleGraph V) [DecidableRel G.Adj] (x a b z : V) :
    Decidable (IsLabel G x a b z) := by unfold IsLabel; infer_instance

instance decidableIsApex (G : SimpleGraph V) [DecidableRel G.Adj] (u w t : V) :
    Decidable (IsApex G u w t) := by unfold IsApex; infer_instance

instance decidableIsFlag (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V) :
    Decidable (IsFlag G x a b) := by unfold IsFlag; infer_instance

instance decidableIsCanonFlag (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V) :
    Decidable (IsCanonFlag G x a b) := by unfold IsCanonFlag; infer_instance

instance decidableFlagImage (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V)
    (T T' : Finset V) : Decidable (FlagImage G x a b T T') := by
  unfold FlagImage; infer_instance

/-! ### F3 — THE FIBRE: `m² − m` flags over a pair whose join has `m` edges -/

/-- The flags whose image pair is `(T, T')`. -/
def fiberOf (G : SimpleGraph V) [DecidableRel G.Adj] (T T' : Finset V) :
    Finset (V × V × V) :=
  Finset.univ.filter fun f => IsFlag G f.1 f.2.1 f.2.2 ∧ FlagImage G f.1 f.2.1 f.2.2 T T'

theorem mem_fiberOf {T T' : Finset V} {f : V × V × V} :
    f ∈ fiberOf G T T' ↔ IsFlag G f.1 f.2.1 f.2.2 ∧ FlagImage G f.1 f.2.1 f.2.2 T T' := by
  simp [fiberOf]

/-- **THE FIBRE COUNT**.  Over an ordered pair of vertex-disjoint triangles whose
join has `m` edges there are exactly `m² − m` flags: the flag is determined by
the ordered pair `(x, b)` of distinct CROSS ENDS in `T'`, and both `a` (the cross
partner of `x`) and the rest of the data are then forced.

At `m = 3` (a prism) this is 6; at `m = 2` (a 2-join) it is 2.  Those are the two
fibre sizes of Theorem C, and they are the whole content of the identity.

**Hypothesis: `UniqueTriangle G` only** — every edge in at most one triangle.
No regularity, no `μ`, no λ = 1 as such (λ = 1 is one way to get it,
`uniqueTriangle_of_srg`).  That matters for evidence, not elegance: it is why
both branches can be instantiated on concrete graphs in §F15 — `m = 3` on
Paley(9) and `m = 2` on `twoJoin`, which is not an SRG.  Inside the srg(1+2r²,
2r, 1, 2) family the `m = 2` branch has no witness at all, because both known
members are canonical. -/
theorem card_fiberOf (hut : UniqueTriangle G) {T T' : Finset V}
    (hT : G.IsNClique 3 T) (hT' : G.IsNClique 3 T') (hdisj : Disjoint T T') :
    (fiberOf G T T').card =
      (joinSet G T T').card * (joinSet G T T').card - (joinSet G T T').card := by
  rw [← card_crossEnds hut hT hdisj, ← Finset.offDiag_card]
  refine Finset.card_nbij (fun f => (f.1, f.2.2)) ?_ ?_ ?_
  · -- maps into the off-diagonal of the cross ends
    intro f hf
    simp only [Finset.mem_coe, mem_fiberOf] at hf
    obtain ⟨hflag, z, y, b', hz, hy, hp, hTeq, hT'eq⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_offDiag]
    refine ⟨?_, ?_, hflag.2.1.ne⟩
    · exact mem_crossEnds.mpr ⟨by rw [hT'eq]; simp, f.2.1, by rw [hTeq]; simp, hflag.1.symm⟩
    · exact mem_crossEnds.mpr ⟨by rw [hT'eq]; simp, z, by rw [hTeq]; simp, hz.2.1.symm⟩
  · -- injective: `a` is the unique neighbour of `x` on `T`
    intro f1 h1 f2 h2 heq
    simp only [Finset.mem_coe, mem_fiberOf] at h1 h2
    obtain ⟨hflag1, z1, y1, b1, hz1, hy1, hp1, hTeq1, hT'eq1⟩ := h1
    obtain ⟨hflag2, z2, y2, b2, hz2, hy2, hp2, hTeq2, hT'eq2⟩ := h2
    have hx : f1.1 = f2.1 := by simpa using congrArg Prod.fst heq
    have hb : f1.2.2 = f2.2.2 := by simpa using congrArg Prod.snd heq
    have hxT : f1.1 ∉ T := by
      refine Finset.disjoint_right.mp hdisj ?_
      rw [hT'eq1]; simp
    have ha : f1.2.1 = f2.2.1 := by
      refine cross_at_most_one_finset hut hT hxT (by rw [hTeq1]; simp) (by rw [hTeq2]; simp)
        hflag1.1 ?_
      rw [hx]; exact hflag2.1
    exact Prod.ext hx (Prod.ext ha hb)
  · -- surjective: every ordered pair of distinct cross ends comes from a flag
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_offDiag, mem_crossEnds] at hp
    obtain ⟨⟨hxT', a, haT, hax⟩, ⟨hbT', z, hzT, hzb⟩, hxb⟩ := hp
    obtain ⟨u1, u2, u3, hLT, rfl⟩ := isNClique_three_iff.mp hT
    obtain ⟨w1, w2, w3, hLT', rfl⟩ := isNClique_three_iff.mp hT'
    have haT'not : a ∉ ({w1, w2, w3} : Finset V) := Finset.disjoint_left.mp hdisj haT
    have hznot : z ∉ ({w1, w2, w3} : Finset V) := Finset.disjoint_left.mp hdisj hzT
    have hxnot : p.1 ∉ ({u1, u2, u3} : Finset V) := Finset.disjoint_right.mp hdisj hxT'
    have hbnot : p.2 ∉ ({u1, u2, u3} : Finset V) := Finset.disjoint_right.mp hdisj hbT'
    have haz : a ≠ z := by
      rintro rfl
      exact hxb (cross_at_most_one_ut hut hLT' haT'not hxT' hbT' hax hzb)
    obtain ⟨y, hLine, hTeq⟩ := line_pair_form hLT haT hzT haz
    obtain ⟨b', hLine', hT'eq⟩ := line_pair_form hLT' hxT' hbT' hxb
    -- the flag data
    have hnxz : ¬ G.Adj p.1 z := fun hh =>
      haz (cross_at_most_one_ut hut hLT hxnot haT hzT hax.symm hh)
    have hnab : ¬ G.Adj a p.2 := fun hh =>
      hxb (cross_at_most_one_ut hut hLT' haT'not hxT' hbT' hax hh)
    have hzx : z ≠ p.1 := fun hh => hxnot (hh ▸ hzT)
    have hab : a ≠ p.2 := fun hh => hbnot (hh ▸ haT)
    have hflag : IsFlag G p.1 a p.2 := ⟨hax.symm, hLine'.1, hab, hnab⟩
    refine ⟨(p.1, a, p.2), ?_, rfl⟩
    simp only [Finset.mem_coe, mem_fiberOf]
    exact ⟨hflag, z, y, b',
      ⟨hLine.1, hzb.symm, hzx, hnxz⟩, ⟨hLine.1, hLine.2.1, hLine.2.2⟩,
      ⟨hLine'.1, hLine'.2.1, hLine'.2.2⟩, hTeq, hT'eq⟩

/-! ### F4 — the two pair sets, as graphs on triangles -/

/-- **THE `m`-JOIN GRAPH** on the vertex set `Finset V`: two vertex-disjoint
triangles are adjacent when their join has exactly `m` edges.  `m = 3` is the
PRISM graph (`n₁` = its number of edges), `m = 2` the 2-JOIN graph (`n₃`).

Using a `SimpleGraph` here is what makes `n₁`, `n₃` counts of UNORDERED pairs
with no division anywhere: `SimpleGraph.two_mul_card_edgeFinset` converts
between the edge count and the ordered-pair count. -/
def joinGraph (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : SimpleGraph (Finset V) where
  Adj T T' := G.IsNClique 3 T ∧ G.IsNClique 3 T' ∧ Disjoint T T' ∧ (joinSet G T T').card = m
  symm := ⟨by
    rintro T T' ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3.symm, by rw [joinSet_card_comm]; exact h4⟩⟩
  loopless := ⟨by
    rintro T ⟨h1, -, h3, -⟩
    have hT : T = ∅ := Finset.bot_eq_empty ▸ disjoint_self.mp h3
    rw [hT] at h1
    simpa using h1.card_eq⟩

theorem joinGraph_adj {m : ℕ} {T T' : Finset V} :
    (joinGraph G m).Adj T T' ↔ G.IsNClique 3 T ∧ G.IsNClique 3 T' ∧ Disjoint T T' ∧
      (joinSet G T T').card = m := Iff.rfl

instance decidableJoinGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    DecidableRel (joinGraph G m).Adj := fun T T' =>
  inferInstanceAs (Decidable (G.IsNClique 3 T ∧ G.IsNClique 3 T' ∧ Disjoint T T' ∧
    (joinSet G T T').card = m))

/-- **`n₁`** — the number of induced triangular prisms: unordered pairs of
vertex-disjoint triangles joined by three edges.  (The join count is the count of
ALL cross edges, so "joined by exactly three" already says the 6-point subgraph
is the prism, INDUCED.) -/
def n1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := (joinGraph G 3).edgeFinset.card

/-- **`n₃`** — the number of unordered pairs of vertex-disjoint triangles joined
by exactly two edges. -/
def n3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := (joinGraph G 2).edgeFinset.card

/-- The ORDERED pairs counted by `joinGraph G m`. -/
def ordJoinPairs (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    Finset (Finset V × Finset V) :=
  Finset.univ.filter fun p => (joinGraph G m).Adj p.1 p.2

theorem mem_ordJoinPairs {m : ℕ} {p : Finset V × Finset V} :
    p ∈ ordJoinPairs G m ↔ G.IsNClique 3 p.1 ∧ G.IsNClique 3 p.2 ∧ Disjoint p.1 p.2 ∧
      (joinSet G p.1 p.2).card = m := by
  simp [ordJoinPairs, joinGraph_adj]

/-- Ordered pairs are twice unordered pairs — `SimpleGraph.two_mul_card_edgeFinset`,
which is where the factor 2 on the triangle side comes from. -/
theorem card_ordJoinPairs (m : ℕ) :
    (ordJoinPairs G m).card = 2 * (joinGraph G m).edgeFinset.card := by
  rw [SimpleGraph.two_mul_card_edgeFinset]
  apply Finset.card_nbij id
  · intro p hp
    simp only [Finset.mem_coe, ordJoinPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    exact hp
  · intro p _ q _ hpq; exact hpq
  · intro p hp
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simp only [ordJoinPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp

/-! ### F5 — THE DOUBLE COUNT -/

/-- **THE DOUBLE COUNT**, once and for all.  If `S` is exactly the set of flags
whose image pair has join count `m`, then `#S = (m² − m)·#(ordered m-join pairs)`:
each flag has ONE image pair, each pair has `m² − m` flags. -/
theorem flag_double_count (h : G.IsSRGWith n k 1 2) {m : ℕ} {S : Finset (V × V × V)}
    (hS : ∀ f : V × V × V, f ∈ S ↔ (IsFlag G f.1 f.2.1 f.2.2 ∧
      ∀ T T' : Finset V, FlagImage G f.1 f.2.1 f.2.2 T T' → (joinSet G T T').card = m)) :
    S.card = (m * m - m) * (ordJoinPairs G m).card := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun (f : V × V × V) (p : Finset V × Finset V) => FlagImage G f.1 f.2.1 f.2.2 p.1 p.2)
      (s := S) (t := ordJoinPairs G m)
  have hL : ∀ f ∈ S, ((ordJoinPairs G m).bipartiteAbove
      (fun (f : V × V × V) (p : Finset V × Finset V) =>
        FlagImage G f.1 f.2.1 f.2.2 p.1 p.2) f).card = 1 := by
    intro f hf
    obtain ⟨hflag, hjoin⟩ := (hS f).mp hf
    obtain ⟨T, T', him⟩ := exists_flagImage h hflag
    rw [Finset.card_eq_one]
    refine ⟨(T, T'), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
    · refine (Finset.mem_bipartiteAbove _).mpr ⟨mem_ordJoinPairs.mpr ?_, him⟩
      exact ⟨(flagImage_cliques him).1, (flagImage_cliques him).2,
        flagImage_disjoint h hflag him, hjoin T T' him⟩
    · intro q hq
      obtain ⟨-, him2⟩ := (Finset.mem_bipartiteAbove _).mp hq
      obtain ⟨e1, e2⟩ := flagImage_unique h hflag him2 him
      exact Prod.ext e1 e2
  have hR : ∀ p ∈ ordJoinPairs G m, (S.bipartiteBelow
      (fun (f : V × V × V) (p : Finset V × Finset V) =>
        FlagImage G f.1 f.2.1 f.2.2 p.1 p.2) p).card = m * m - m := by
    intro p hp
    obtain ⟨hT, hT', hdisj, hjoin⟩ := mem_ordJoinPairs.mp hp
    have hfib : S.bipartiteBelow
        (fun (f : V × V × V) (p : Finset V × Finset V) =>
          FlagImage G f.1 f.2.1 f.2.2 p.1 p.2) p = fiberOf G p.1 p.2 := by
      ext f
      rw [Finset.mem_bipartiteBelow _, mem_fiberOf]
      constructor
      · rintro ⟨hfS, him⟩
        exact ⟨((hS f).mp hfS).1, him⟩
      · rintro ⟨hflag, him⟩
        refine ⟨(hS f).mpr ⟨hflag, ?_⟩, him⟩
        intro T T' him2
        obtain ⟨e1, e2⟩ := flagImage_unique h hflag him2 him
        rw [e1, e2]; exact hjoin
    rw [hfib, card_fiberOf (uniqueTriangle_of_srg h) hT hT' hdisj, hjoin]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at key
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at key
  rw [key, mul_comm]

/-! ### F6 — the two instances: canonical flags ↦ prisms, bad flags ↦ 2-joins -/

/-- All canonical flags of `G`, over all roots. -/
def canonFlagSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V × V) :=
  Finset.univ.filter fun f => IsFlag G f.1 f.2.1 f.2.2 ∧ IsCanonFlag G f.1 f.2.1 f.2.2

/-- All NON-canonical flags of `G`, over all roots. -/
def badFlagSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V × V) :=
  Finset.univ.filter fun f => IsFlag G f.1 f.2.1 f.2.2 ∧ ¬ IsCanonFlag G f.1 f.2.1 f.2.2

/-- **12 FLAGS PER PRISM**, in ordered form: `#canonical flags = 6 · #ordered
prism pairs`.  (An unordered prism carries 12 flags; that is this statement
composed with `card_ordJoinPairs`.) -/
theorem card_canonFlagSet (h : G.IsSRGWith n k 1 2) :
    (canonFlagSet G).card = 6 * (ordJoinPairs G 3).card := by
  have := flag_double_count (m := 3) (S := canonFlagSet G) h ?_
  · simpa using this
  · intro f
    simp only [canonFlagSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hflag, hcan⟩
      exact ⟨hflag, fun T T' him => flagImage_join_three h hflag him hcan⟩
    · rintro ⟨hflag, hall⟩
      refine ⟨hflag, ?_⟩
      by_contra hcan
      obtain ⟨T, T', him⟩ := exists_flagImage h hflag
      have h2 := flagImage_join_two h hflag him hcan
      have h3 := hall T T' him
      omega

/-- **4 FLAGS PER 2-JOIN**, in ordered form: `#bad flags = 2 · #ordered 2-join
pairs`. -/
theorem card_badFlagSet (h : G.IsSRGWith n k 1 2) :
    (badFlagSet G).card = 2 * (ordJoinPairs G 2).card := by
  have := flag_double_count (m := 2) (S := badFlagSet G) h ?_
  · simpa using this
  · intro f
    simp only [badFlagSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hflag, hcan⟩
      exact ⟨hflag, fun T T' him => flagImage_join_two h hflag him hcan⟩
    · rintro ⟨hflag, hall⟩
      refine ⟨hflag, ?_⟩
      intro hcan
      obtain ⟨T, T', him⟩ := exists_flagImage h hflag
      have h3 := flagImage_join_three h hflag him hcan
      have h2 := hall T T' him
      omega

/-- **THEOREM C, prism half, in flags**: `#canonical flags = 12·n₁`. -/
theorem card_canonFlagSet_n1 (h : G.IsSRGWith n k 1 2) :
    (canonFlagSet G).card = 12 * n1 G := by
  rw [card_canonFlagSet h, card_ordJoinPairs, n1]; ring

/-- **THEOREM C, 2-join half, in flags**: `#non-canonical flags = 4·n₃`. -/
theorem card_badFlagSet_n3 (h : G.IsSRGWith n k 1 2) :
    (badFlagSet G).card = 4 * n3 G := by
  rw [card_badFlagSet h, card_ordJoinPairs, n3]; ring

/-! ### F7 — slicing by the root -/

/-- The flags at a single root. -/
def flagsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset (V × V) :=
  Finset.univ.filter fun p => IsFlag G x p.1 p.2

/-- The canonical flags at a single root. -/
def canonFlagsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset (V × V) :=
  Finset.univ.filter fun p => IsFlag G x p.1 p.2 ∧ IsCanonFlag G x p.1 p.2

/-- The non-canonical flags at a single root. -/
def badFlagsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset (V × V) :=
  Finset.univ.filter fun p => IsFlag G x p.1 p.2 ∧ ¬ IsCanonFlag G x p.1 p.2

/-- Slicing a set of flags by its root. -/
theorem card_eq_sum_slices (S : Finset (V × V × V)) (Sat : V → Finset (V × V))
    (hmem : ∀ x a b : V, (x, a, b) ∈ S ↔ (a, b) ∈ Sat x) :
    S.card = ∑ x : V, (Sat x).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.card_nbij' (fun f => f.2) (fun p => (x, p.1, p.2)) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter] at hf
    have hfe : (x, f.2.1, f.2.2) = f := by rw [← hf.2]
    exact (hmem x f.2.1 f.2.2).mp (by rw [hfe]; exact hf.1)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    exact ⟨(hmem x p.1 p.2).mpr hp, by trivial⟩
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter] at hf
    rw [← hf.2]
  · intro p _; rfl

theorem card_canonFlagSet_slices :
    (canonFlagSet G).card = ∑ x : V, (canonFlagsAt G x).card :=
  card_eq_sum_slices _ _ fun x a b => by simp [canonFlagSet, canonFlagsAt]

theorem card_badFlagSet_slices :
    (badFlagSet G).card = ∑ x : V, (badFlagsAt G x).card :=
  card_eq_sum_slices _ _ fun x a b => by simp [badFlagSet, badFlagsAt]

/-- Canonical + non-canonical = all, at each root. -/
theorem card_flagsAt_split (x : V) :
    (canonFlagsAt G x).card + (badFlagsAt G x).card = (flagsAt G x).card := by
  have h1 : canonFlagsAt G x = (flagsAt G x).filter fun p => IsCanonFlag G x p.1 p.2 := by
    ext p; simp [canonFlagsAt, flagsAt, and_comm]
  have h2 : badFlagsAt G x = (flagsAt G x).filter fun p => ¬ IsCanonFlag G x p.1 p.2 := by
    ext p; simp [badFlagsAt, flagsAt, and_comm]
  rw [h1, h2, Finset.card_filter_add_card_filter_not]

/-! ### F8 — from flags to TRANSITIONS: the factor 2 on the root side -/

/-- The matched CLASS of `b` in `N(x)`, defined WITHOUT choice: `b` together with
the common neighbours of `x` and `b`.  By λ = 1 that set is `{b′}`, so
`classOf G x b = {b, b′}` (`classOf_eq`). -/
def classOf (G : SimpleGraph V) [DecidableRel G.Adj] (x b : V) : Finset V :=
  insert b (Finset.univ.filter fun w => G.Adj x w ∧ G.Adj b w)

theorem classOf_eq (h : G.IsSRGWith n k 1 μ) {x b b' : V} (hp : IsPartner G x b b') :
    classOf G x b = {b, b'} := by
  have hsing : (Finset.univ.filter fun w => G.Adj x w ∧ G.Adj b w) = {b'} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨by simp [hp.2.1, hp.2.2], fun w hw => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact unique_common_of_adj h hp.1 ((mem_commonNeighbors G).mpr ⟨hw.1, hw.2⟩)
      ((mem_commonNeighbors G).mpr ⟨hp.2.1, hp.2.2⟩)
  rw [classOf, hsing]

/-- The two members of a class name the same class — this is the 2-to-1 step. -/
theorem classOf_partner (h : G.IsSRGWith n k 1 μ) {x b b' : V} (hp : IsPartner G x b b') :
    classOf G x b = classOf G x b' := by
  rw [classOf_eq h hp, classOf_eq h hp.symm, Finset.pair_comm]

/-- Swapping `b` for its partner keeps a flag a flag. -/
theorem isFlag_partner (h : G.IsSRGWith n k 1 2) {x a b b' : V} (hf : IsFlag G x a b)
    (hp : IsPartner G x b b') : IsFlag G x a b' := by
  obtain ⟨b₀, z, y, z', hp₀, hab', hnab', -, -, -⟩ := flag_data h hf
  have : b' = b₀ := partner_unique h hp hp₀
  subst this
  exact ⟨hf.1, hp.2.1, hab', hnab'⟩

/-- ... and keeps a CANONICAL flag canonical: canonicality is a property of the
transition `(a, {b,b′})`, not of the chosen representative `b`. -/
theorem isCanonFlag_partner (h : G.IsSRGWith n k 1 2) {x a b b' : V}
    (hp : IsPartner G x b b') (hcan : IsCanonFlag G x a b) : IsCanonFlag G x a b' := by
  obtain ⟨b₂, z, z', hp₂, hz, hz', hadj⟩ := hcan
  have : b₂ = b' := partner_unique h hp₂ hp
  subst this
  exact ⟨b, z', z, hp.symm, hz', hz, hadj.symm⟩

/-- **THE 2-TO-1 COUNT**: a set of flags at `x` closed under `b ↦ b′` has exactly
twice as many elements as its set of transitions. -/
theorem card_image_classOf (h : G.IsSRGWith n k 1 2) (x : V) (S : Finset (V × V))
    (hflag : ∀ p ∈ S, IsFlag G x p.1 p.2)
    (hclosed : ∀ a b b' : V, (a, b) ∈ S → IsPartner G x b b' → (a, b') ∈ S) :
    S.card = 2 * (S.image fun p => (p.1, classOf G x p.2)).card := by
  have hcard : ∀ t ∈ (S.image fun p => (p.1, classOf G x p.2)),
      (S.filter fun q => (q.1, classOf G x q.2) = t).card = 2 := by
    intro t ht
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b', hp', -⟩ := exists_unique_partner h (hflag p hpS).2.1
    have hbne : p.2 ≠ b' := hp'.2.2.ne
    have hfil : (S.filter fun q => (q.1, classOf G x q.2) = (p.1, classOf G x p.2))
        = {p, (p.1, b')} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hqS, heq⟩
        rw [Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        have hmem : q.2 ∈ ({p.2, b'} : Finset V) := by
          rw [← classOf_eq h hp', ← h2, classOf]
          exact Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h3 | h3
        · exact Or.inl (Prod.ext h1 h3)
        · exact Or.inr (Prod.ext h1 h3)
      · rintro (rfl | rfl)
        · exact ⟨hpS, rfl⟩
        · exact ⟨hclosed p.1 p.2 b' hpS hp', by simp [(classOf_partner h hp').symm]⟩
    rw [hfil, Finset.card_pair (by simp [Prod.ext_iff, hbne])]
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : V × V => (p.1, classOf G x p.2))
      (t := S.image fun p => (p.1, classOf G x p.2))
      (fun p hp => Finset.mem_image_of_mem _ hp),
    Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The **TRANSITIONS** at `x`: pairs `(a, {b,b′})` with `a ∈ N(x)` and `{b,b′}` a
matched class of `N(x)` not containing `a`.  (Presented as the image of the flag
set, which is the same thing by `mem_transitionsAt`.) -/
def transitionsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset (V × Finset V) :=
  (flagsAt G x).image fun p => (p.1, classOf G x p.2)

/-- The CANONICAL transitions at `x`. -/
def canonTransitionsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset (V × Finset V) :=
  (canonFlagsAt G x).image fun p => (p.1, classOf G x p.2)

/-- **`D(x)`** — the number of CANONICAL transitions at the root `x`.  This is the
counter of logs 031–032 and of `notes/math/local-canonicality-conjecture.md`:
`D(x) = 2r(r−1)` iff `CanonicalAt G x`, and the SAT certificates bound it. -/
def D (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℕ := (canonTransitionsAt G x).card

theorem mem_transitionsAt {x : V} {t : V × Finset V} :
    t ∈ transitionsAt G x ↔ ∃ b, IsFlag G x t.1 b ∧ t.2 = classOf G x b := by
  simp only [transitionsAt, Finset.mem_image, flagsAt, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp, rfl⟩
  · rintro ⟨b, hb, hteq⟩
    exact ⟨(t.1, b), hb, by rw [← hteq]⟩

theorem mem_canonTransitionsAt {x : V} {t : V × Finset V} :
    t ∈ canonTransitionsAt G x ↔
      ∃ b, IsFlag G x t.1 b ∧ IsCanonFlag G x t.1 b ∧ t.2 = classOf G x b := by
  simp only [canonTransitionsAt, Finset.mem_image, canonFlagsAt, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp.1, hp.2, rfl⟩
  · rintro ⟨b, hb, hcb, hteq⟩
    exact ⟨(t.1, b), ⟨hb, hcb⟩, by rw [← hteq]⟩

/-- **TWO FLAGS PER TRANSITION**, canonical version: `#canonical flags at x = 2·D(x)`. -/
theorem card_canonFlagsAt (h : G.IsSRGWith n k 1 2) (x : V) :
    (canonFlagsAt G x).card = 2 * D G x := by
  refine card_image_classOf h x _ (fun p hp => ?_) (fun a b b' hab hp => ?_)
  · exact (by simpa [canonFlagsAt] using hp : IsFlag G x p.1 p.2 ∧ _).1
  · simp only [canonFlagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    exact ⟨isFlag_partner h hab.1 hp, isCanonFlag_partner h hp hab.2⟩

/-- **TWO FLAGS PER TRANSITION**, total version. -/
theorem card_flagsAt_two_mul (h : G.IsSRGWith n k 1 2) (x : V) :
    (flagsAt G x).card = 2 * (transitionsAt G x).card := by
  refine card_image_classOf h x _ (fun p hp => ?_) (fun a b b' hab hp => ?_)
  · simpa [flagsAt] using hp
  · simp only [flagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    exact isFlag_partner h hab hp

/-! ### F9 — how many flags there are at a root: `k(k−2)` -/

theorem card_flagsAt (h : G.IsSRGWith n k 1 μ) (x : V) :
    (flagsAt G x).card = k * (k - 2) := by
  have hdeg : (G.neighborFinset x).card = k := h.regular x
  have hmaps : ∀ p ∈ flagsAt G x, p.1 ∈ G.neighborFinset x := by
    intro p hp
    simp only [flagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa using hp.1
  have hfib : ∀ a ∈ G.neighborFinset x,
      ((flagsAt G x).filter fun p => p.1 = a).card = k - 2 := by
    intro a ha
    have hxa : G.Adj x a := by simpa using ha
    obtain ⟨a', hpa, -⟩ := exists_unique_partner h hxa
    have hne : a ≠ a' := hpa.2.2.ne
    have hsub : ({a, a'} : Finset V) ⊆ G.neighborFinset x := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simpa using hxa
      · simpa using hpa.2.1
    have hbij : ((flagsAt G x).filter fun p => p.1 = a).card
        = ((G.neighborFinset x) \ {a, a'}).card := by
      refine Finset.card_nbij' (fun p => p.2) (fun b => (a, b)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, flagsAt, Finset.mem_univ,
          true_and] at hp
        obtain ⟨⟨-, hxb, hne2, hnadj⟩, rfl⟩ := hp
        simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
          SimpleGraph.mem_neighborFinset]
        refine ⟨hxb, ?_⟩
        rintro (h3 | h3)
        · exact hne2 h3.symm
        · exact hnadj (by rw [h3]; exact hpa.2.2)
      · intro b hb
        simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
          SimpleGraph.mem_neighborFinset] at hb
        obtain ⟨hxb, hnot⟩ := hb
        simp only [Finset.mem_coe, Finset.mem_filter, flagsAt, Finset.mem_univ, true_and]
        refine ⟨⟨hxa, hxb, fun hh => hnot (by rw [← hh]; simp), fun hadj => ?_⟩,
          by trivial⟩
        exact hnot (Or.inr (partner_unique h ⟨hxa, hxb, hadj⟩ hpa))
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter] at hp
        rw [← hp.2]
      · intro b _; rfl
    rw [hbij, Finset.card_sdiff_of_subset hsub, hdeg, Finset.card_pair hne]
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    hdeg, smul_eq_mul]

/-! ### F10 — `D(x)` versus `CanonicalAt` -/

/-- `CanonicalAt x` is exactly "every flag at `x` is canonical".  This is what
identifies the counter `D` with the object logs 031–032 bound. -/
theorem canonicalAt_iff_forall_flag (h : G.IsSRGWith n k 1 2) (x : V) :
    CanonicalAt G x ↔ ∀ a b : V, IsFlag G x a b → IsCanonFlag G x a b := by
  constructor
  · intro hcan a b hf
    obtain ⟨b', z, y, z', hp, hab', -, hz, -, hz'⟩ := flag_data h hf
    exact ⟨b', z, z', hp, hz, hz', hcan a b b' z z' hf.1 hp hf.2.2.1 hab' hz hz'⟩
  · intro hall a b b' zab zab' hxa hpb hab hab' hzab hzab'
    obtain ⟨hnab, hnab'⟩ := not_adj_of_ne_class h hpb hxa hab hab'
    obtain ⟨b₂, z, z', hp₂, hz, hz', hadj⟩ := hall a b ⟨hxa, hpb.1, hab, hnab⟩
    have hb2 : b₂ = b' := partner_unique h hp₂ hpb
    subst hb2
    have e1 : z = zab := label_unique h hxa hpb.1 hnab hab hz hzab
    have e2 : z' = zab' := label_unique h hxa hpb.2.1 hnab' hab' hz' hzab'
    subst e1; subst e2; exact hadj

theorem canonFlagsAt_eq_flagsAt (h : G.IsSRGWith n k 1 2) {x : V} (hcan : CanonicalAt G x) :
    canonFlagsAt G x = flagsAt G x := by
  ext p
  simp only [canonFlagsAt, flagsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hp => hp.1,
    fun hp => ⟨hp, (canonicalAt_iff_forall_flag h x).mp hcan p.1 p.2 hp⟩⟩

/-- At a canonical root, EVERY transition is canonical. -/
theorem D_eq_card_transitionsAt (h : G.IsSRGWith n k 1 2) {x : V} (hcan : CanonicalAt G x) :
    D G x = (transitionsAt G x).card := by
  rw [D, canonTransitionsAt, transitionsAt, canonFlagsAt_eq_flagsAt h hcan]

/-! ### F11 — the arithmetic of `k = 2r`, and `D(x) = 2r(r−1) ⟺ CanonicalAt` -/

/-- `k(k−2) = 2·(2r(r−1))` when `k = 2r` — the flag count is twice the
transition count, and the transition count is `2r(r−1)`.  (True in ℕ for `r = 0`
too, where both sides are 0.) -/
theorem flag_arith (r : ℕ) : 2 * r * (2 * r - 2) = 2 * (2 * r * (r - 1)) := by
  cases r with
  | zero => simp
  | succ s =>
    have h1 : 2 * (s + 1) - 2 = 2 * s := by omega
    have h2 : (s + 1) - 1 = s := by omega
    rw [h1, h2]; ring

/-- **THE NUMBER OF TRANSITIONS AT A ROOT IS `2r(r−1)`** (`= 84` at `v = 99`). -/
theorem card_transitionsAt (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) (x : V) :
    (transitionsAt G x).card = 2 * r * (r - 1) := by
  have h1 := card_flagsAt_two_mul h x
  have h2 : (flagsAt G x).card = 2 * (2 * r * (r - 1)) := by
    rw [card_flagsAt h x, hk]; exact flag_arith r
  omega

/-- `D(x) ≤ 2r(r−1)`: the canonical transitions are among all of them. -/
theorem D_le (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) (x : V) :
    D G x ≤ 2 * r * (r - 1) := by
  rw [← card_transitionsAt h hk x]
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro p hp
  simp only [canonFlagsAt, flagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.1

/-- **THE CONVERSE**: a root with the maximum count `D(x) = 2r(r−1)` IS
canonical.  (`canonTransitionsAt ⊆ transitionsAt` with equal cards, so the two
sets coincide; then every flag's transition has a canonical representative, and
canonicality passes between the two representatives of a class.) -/
theorem canonicalAt_of_D_eq (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) {x : V}
    (hD : D G x = 2 * r * (r - 1)) : CanonicalAt G x := by
  have hDdef : D G x = (canonTransitionsAt G x).card := rfl
  have hsub : canonTransitionsAt G x ⊆ transitionsAt G x := by
    refine Finset.image_subset_image ?_
    intro p hp
    simp only [canonFlagsAt, flagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  have heq : canonTransitionsAt G x = transitionsAt G x := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    have hct : (transitionsAt G x).card = D G x := by rw [card_transitionsAt h hk x, hD]
    omega
  rw [canonicalAt_iff_forall_flag h x]
  intro a b hf
  obtain ⟨b', hp, -⟩ := exists_unique_partner h hf.2.1
  have hmem : (a, classOf G x b) ∈ canonTransitionsAt G x := by
    rw [heq]; exact mem_transitionsAt.mpr ⟨b, hf, rfl⟩
  obtain ⟨b₂, -, hc₂', he₂'⟩ := mem_canonTransitionsAt.mp hmem
  have hc₂ : IsCanonFlag G x a b₂ := hc₂'
  have he₂ : classOf G x b = classOf G x b₂ := he₂'
  have hmem2 : b₂ ∈ ({b, b'} : Finset V) := by
    rw [← classOf_eq h hp, he₂, classOf]
    exact Finset.mem_insert_self _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem2
  rcases hmem2 with rfl | rfl
  · exact hc₂
  · exact isCanonFlag_partner h hp.symm hc₂

/-- **`D(x) = 2r(r−1) ⟺ `CanonicalAt G x`** — the counter and the geometric
property are the same statement.  This is what lets log 031's certificate
("`D = 84` is refuted") be quoted as "no vertex is canonical". -/
theorem D_eq_iff_canonicalAt (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) (x : V) :
    D G x = 2 * r * (r - 1) ↔ CanonicalAt G x :=
  ⟨fun hD => canonicalAt_of_D_eq h hk hD,
   fun hcan => by rw [D_eq_card_transitionsAt h hcan, card_transitionsAt h hk x]⟩

/-! ### F12 — **THEOREM C** -/

/-- **THEOREM C, prism half.**  In any srg(n,k,1,2),
`6·n₁ = Σ_x D(x)` — stated multiplicatively, no division. -/
theorem theoremC_n1 (h : G.IsSRGWith n k 1 2) : 6 * n1 G = ∑ x : V, D G x := by
  have h1 := card_canonFlagSet_n1 h
  rw [card_canonFlagSet_slices, Finset.sum_congr rfl (fun x _ => card_canonFlagsAt h x),
    ← Finset.mul_sum] at h1
  omega

/-- **THEOREM C, 2-join half.**  In any srg(1+2r², 2r, 1, 2) — in fact in any
srg(n, 2r, 1, 2) — `2·n₃ = Σ_x (2r(r−1) − D(x))`. -/
theorem theoremC_n3 (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) :
    2 * n3 G = ∑ x : V, (2 * r * (r - 1) - D G x) := by
  have hbad : ∀ x : V, (badFlagsAt G x).card = 2 * (2 * r * (r - 1) - D G x) := by
    intro x
    have h1 := card_flagsAt_split (G := G) x
    have h2 := card_canonFlagsAt h x
    have h3 : (flagsAt G x).card = 2 * (2 * r * (r - 1)) := by
      rw [card_flagsAt h x, hk]; exact flag_arith r
    omega
  have h1 := card_badFlagSet_n3 h
  rw [card_badFlagSet_slices, Finset.sum_congr rfl (fun x _ => hbad x), ← Finset.mul_sum] at h1
  omega

/-- **REIMBAYEV, Prop. 5(6)** (arXiv:2409.10620), reproduced as a consequence of
the fibre counts: `12·n₁ + 4·n₃ = n·k·(k−2)`, i.e. — dividing by 4 —
`3n₁ + n₃ = ¼·n·k·(k−2)`.  Both `Σ_x D(x)` terms cancel identically: the total
flag count is `n·k(k−2)` and every flag lands on a prism or on a 2-join.

**This is proved here, not cited — and that is exactly why it is not an arbiter
INSIDE Lean.**  It is derived from `card_canonFlagSet_n1`, `card_badFlagSet_n3`
and `card_flagsAt`, i.e. from the very lemmas one would want it to check, so it
cannot fail; Lean proves no false statements.  The check it embodies is
EXTERNAL: a reader must compare this statement with Reimbayev's published
Prop. 5(6), and these `n₁`, `n₃` with his.  Performed numerically that
comparison holds (18 = 18 at v = 9; 26,730 = 26,730 at v = 243) and it FORCES
the unordered reading of `n₁`, `n₃` — the ordered reading gives 36 ≠ 18.  The
in-Lean falsifiable checks on the constants are the `decide` computations of
§F15. -/
theorem reimbayev_prop5 (h : G.IsSRGWith n k 1 2) :
    12 * n1 G + 4 * n3 G = n * (k * (k - 2)) := by
  have hc := card_canonFlagSet_n1 h
  have hb := card_badFlagSet_n3 h
  have hsum : (canonFlagSet G).card + (badFlagSet G).card = n * (k * (k - 2)) := by
    rw [card_canonFlagSet_slices, card_badFlagSet_slices, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ => card_flagsAt_split (G := G) x),
      Finset.sum_congr rfl (fun x _ => card_flagsAt h x), Finset.sum_const,
      Finset.card_univ, h.card, smul_eq_mul]
  omega

/-- **COROLLARY: `n₃ = 0` ⟺ canonical at every vertex** — and hence, by
`Makhnev.makhnevStar_iff_canonical`, ⟺ Makhnev's condition (∗).  This is the
counting proof of C1 (the direct proof is in `Makhnev.lean`). -/
theorem n3_eq_zero_iff_canonical (h : G.IsSRGWith n k 1 2) : n3 G = 0 ↔ Canonical G := by
  constructor
  · intro h0
    have hcard : (badFlagSet G).card = 0 := by rw [card_badFlagSet_n3 h, h0]
    intro x
    rw [canonicalAt_iff_forall_flag h x]
    intro a b hf
    by_contra hcan
    have hmem : (x, a, b) ∈ badFlagSet G := by
      simp only [badFlagSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hf, hcan⟩
    exact absurd (Finset.card_eq_zero.mp hcard ▸ hmem) (by simp)
  · intro hcan
    have hempty : badFlagSet G = ∅ := by
      ext f
      simp only [badFlagSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_and, not_not]
      exact fun hf => (canonicalAt_iff_forall_flag h f.1).mp (hcan f.1) f.2.1 f.2.2 hf
    have := card_badFlagSet_n3 h
    rw [hempty] at this
    simp only [Finset.card_empty] at this
    omega

/-- ... in Makhnev's own words. -/
theorem n3_eq_zero_iff_makhnevStar (h : G.IsSRGWith n k 1 2) :
    n3 G = 0 ↔ MakhnevStar G :=
  (n3_eq_zero_iff_canonical h).trans (makhnevStar_iff_canonical h).symm

/-! ### F13 — **v = 99**: the certified rung `D(x) ≤ 77` turned into `n₁`, `n₃`

`hD` below is **NOT a Lean theorem**: it is the SAT/DRAT certificate of logs
031–032 (`D ≥ 78` refuted, drat-trim + cake_lpr VERIFIED), imported here as an
explicit hypothesis.  Everything else in this section is proved. -/

theorem conway99_sum_D_le (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 77) :
    ∑ x : V, D G x ≤ 7623 := by
  have hle : ∑ x : V, D G x ≤ ∑ _x : V, 77 := Finset.sum_le_sum fun x _ => hD x
  rwa [Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul] at hle

/-- **COROLLARY C2, first half**: `n₁ ≤ 1270`.  The divisibility refinement is
automatic here — `6·n₁ = Σ D ≤ 7623` forces `n₁ ≤ 1270`, i.e. `Σ D ≤ 7620`. -/
theorem conway99_n1_le (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 77) :
    n1 G ≤ 1270 := by
  have h1 := theoremC_n1 h
  have h2 := conway99_sum_D_le h hD
  omega

/-- The divisibility refinement itself: `Σ_x D(x) ≤ 7620`, not merely 7623. -/
theorem conway99_sum_D_le' (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 77) :
    ∑ x : V, D G x ≤ 7620 := by
  have h1 := theoremC_n1 h
  have h2 := conway99_n1_le h hD
  omega

/-- **COROLLARY C2, second half**: `n₃ ≥ 348`. -/
theorem conway99_n3_ge (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 77) :
    348 ≤ n3 G := by
  have hDle : ∀ x : V, D G x ≤ 84 := by
    intro x
    have := D_le h (r := 7) (by norm_num) x
    omega
  have hsplit : (∑ x : V, (84 - D G x)) + ∑ x : V, D G x = 8316 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ => by have := hDle x; omega : ∀ x ∈ Finset.univ,
        (84 - D G x) + D G x = 84),
      Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul]
  have h3 := theoremC_n3 h (r := 7) (by norm_num)
  have h3' : 2 * n3 G = ∑ x : V, (84 - D G x) := by
    rw [h3]
  have h4 := conway99_sum_D_le' h hD
  omega

/-! ### F14 — NON-VACUITY: Paley(9), where the identity is checkable by hand

Paley(9) is canonical (`paley9_canonical`), so `D(x) = 2r(r−1) = 4` at each of
its 9 vertices and the identity predicts `n₁ = 36/6 = 6`, `n₃ = 0`.

**Read the grade carefully.**  Everything in THIS section is derived FROM the
lemmas above — `paley9_D` from `D_eq_card_transitionsAt`, `paley9_n1` from
`theoremC_n1`, `paley9_n3` from `n3_eq_zero_iff_canonical`.  So none of it can
detect a wrong constant: if `card_fiberOf` read `2(m² − m)`, Lean would prove
`paley9_n1 = 3` here just as happily.  The comparison with the brute-force
counts of `notes/math/theorem_c_check.py` (6 and 0) happens OUTSIDE Lean, in a
reader's head.  The checks that CAN fail are in §F15. -/

theorem paley9_D (x : Fin 3 × Fin 3) : D paley9 x = 4 := by
  rw [D_eq_card_transitionsAt paley9_srg (paley9_canonical x),
    card_transitionsAt paley9_srg (r := 2) (by norm_num) x]

theorem paley9_sum_D : ∑ x : Fin 3 × Fin 3, D paley9 x = 36 := by
  rw [Finset.sum_congr rfl (fun x _ => paley9_D x), Finset.sum_const, Finset.card_univ]
  norm_num

/-- **Paley(9) has exactly 6 induced prisms** — the identity's PREDICTION.  (The
brute-force count is 6 too, but that comparison is external; see the section
header and §F15.) -/
theorem paley9_n1 : n1 paley9 = 6 := by
  have := theoremC_n1 paley9_srg
  rw [paley9_sum_D] at this
  omega

/-- ... and no 2-joins. -/
theorem paley9_n3 : n3 paley9 = 0 :=
  (n3_eq_zero_iff_canonical paley9_srg).mpr paley9_canonical

/-! ### F15 — THE CHECKS THAT CAN FAIL: both fibre branches, by `decide`

§F14's numbers are consequences of the theorems above and therefore cannot
falsify them.  This section is the opposite: every statement here is proved by
KERNEL COMPUTATION from the definitions (`decide`), so it pins the Lean
definitions — `IsFlag`, `FlagImage`, `fiberOf`, `flagsAt`, `classOf`, `D` — to
the intended combinatorial objects on graphs where the answer is known
independently.  If `fiberOf` counted the wrong thing, or if `card_fiberOf`'s
`m² − m` were (say) `2(m² − m)`, the pairs of theorems below would be
inconsistent and this file would not compile.

Both branches are covered, which is the point:

  * `m = 3` on **Paley(9)** — 6 flags over one ordered prism pair, hence 12 per
    unordered prism.
  * `m = 2` on **`twoJoin`** — 2 flags over the ordered 2-join pair, hence 4 per
    unordered 2-join.  `twoJoin` is not an SRG; it is admissible here only
    because `card_fiberOf`'s hypothesis is `UniqueTriangle`
    (`twoJoin_uniqueTriangle`, itself by `decide`).  **No member of the
    srg(1+2r², 2r, 1, 2) family can play this role**: both known members are
    canonical, so both have `n₃ = 0`.  This is the ONLY in-Lean instance of the
    2-join fibre anywhere in the library.
-/

/-- The two rows of the 3×3 rook's graph used as the concrete prism
(`Makhnev.paley9_prism`). -/
abbrev paley9Row0 : Finset (Fin 3 × Fin 3) := {((0 : Fin 3), (0 : Fin 3)), (0, 1), (0, 2)}

/-- ... and the second row. -/
abbrev paley9Row1 : Finset (Fin 3 × Fin 3) := {((1 : Fin 3), (0 : Fin 3)), (1, 1), (1, 2)}

set_option maxRecDepth 400000 in
/-- **THE m = 3 FIBRE, COMPUTED.**  Six flags lie over the ordered prism pair
(rows 0, 1) of Paley(9) — hence 12 over the unordered prism.  Kernel
computation from the definitions; independent of everything above. -/
theorem paley9_prism_fibre : (fiberOf paley9 paley9Row0 paley9Row1).card = 6 := by decide

/-- ... and the same number as `card_fiberOf` PREDICTS it, `3·3 − 3`.  Holding
both this and `paley9_prism_fibre` is what makes the constant falsifiable. -/
theorem paley9_prism_fibre_pred :
    (fiberOf paley9 paley9Row0 paley9Row1).card = 3 * 3 - 3 := by
  rw [card_fiberOf paley9_uniqueTriangle
      (isNClique_three_of_line paley9_prism.1) (isNClique_three_of_line paley9_prism.2.1)
      paley9_prism.2.2.1,
    paley9_prism.2.2.2.2.2.2]

set_option maxRecDepth 40000 in
/-- **THE m = 2 FIBRE, COMPUTED.**  Two flags lie over the ordered 2-join pair of
`twoJoin` — hence 4 over the unordered 2-join.  This is the "4" of Theorem C,
and this is the only place in the library where it is instantiated. -/
theorem twoJoin_fibre :
    (fiberOf twoJoin ({0, 1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6))).card = 2 := by
  decide

/-- ... and the same number as `card_fiberOf` predicts it, `2·2 − 2`. -/
theorem twoJoin_fibre_pred :
    (fiberOf twoJoin ({0, 1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6))).card
      = 2 * 2 - 2 := by
  rw [card_fiberOf twoJoin_uniqueTriangle
      (isNClique_three_of_line twoJoin_config.1) (isNClique_three_of_line twoJoin_config.2.1)
      twoJoin_config.2.2.1,
    twoJoin_join_card]

set_option maxRecDepth 100000 in
/-- **THE OTHER FACTOR OF 2, COMPUTED**: `k(k−2) = 4·2 = 8` flags at a root of
Paley(9).  Pins `card_flagsAt`. -/
theorem paley9_flagsAt_card : (flagsAt paley9 ((0 : Fin 3), (0 : Fin 3))).card = 8 := by decide

set_option maxRecDepth 100000 in
/-- ... all of them canonical, since Paley(9) is.  Pins `card_canonFlagsAt`. -/
theorem paley9_canonFlagsAt_card :
    (canonFlagsAt paley9 ((0 : Fin 3), (0 : Fin 3))).card = 8 := by decide

set_option maxRecDepth 100000 in
/-- **`D` ITSELF, COMPUTED** — `D(x) = 4 = 2r(r−1)` at a root of Paley(9), from
the definition of `canonTransitionsAt` and nothing else.  Compare `paley9_D`,
which derives the same number from `D_eq_card_transitionsAt`: the two agree, and
the agreement is a check on `classOf` and on the flags↦transitions 2-to-1
count. -/
theorem paley9_D_computed : D paley9 ((0 : Fin 3), (0 : Fin 3)) = 4 := by decide

end Conway99
