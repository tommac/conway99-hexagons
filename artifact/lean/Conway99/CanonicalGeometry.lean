/-
Conway99.CanonicalGeometry — the plane/grid geometry of a CANONICAL
srg(v,k,1,2), and the well-definedness of the Steiner completion.

CONTEXT.  Log 031 certifies (SAT, drat-trim + cake_lpr) that no Conway
99-graph is *canonical* at any vertex, where canonical means the transition
system at the root is `M_a(b) = b′` — the unique `G`-invariant one, and the
one both known members of the λ=1, μ=2 family realise at every root.  Logs
033–035 then developed the geometry that canonicality buys, in
`notes/math/hall-analogue.md` and log 035's "NEW RESULT 1/2".  Those results
were graded PROVED in markdown and had never been machine-checked.  This file
checks them.

WHAT IS PROVED HERE.

  * `CanonicalAt` (C1) — the definition, in the relational style of
    `Transition.lean` (no choice functions); `CanonicalAt.transfer` — it is a
    property of the abstract graph, transported by any isomorphism.
  * `not_adj_of_ne_class`, `canonical_class_rule` — the class rule
    (`hall-analogue.md` Lemma 2): two neighbours of `x` in different matched
    classes are non-adjacent; and under canonicality two label vertices
    sharing an index are adjacent ONLY IF their other indices are matched.
  * `corner_unique`, `plane_set_unique` (C2) — **PLANE UNIQUENESS**.  The
    plane through two intersecting lines is unique, and this needs ONLY μ = 2
    — canonicality is what makes the nine points a *grid*, not what makes
    them unique.
  * `common_neighbors_not_adj`, `chordless_quadrangle` — the induced
    4-cycle behind `hall-analogue.md` Theorem 1(3).
  * `IsGrid`, `gridPt`, `grid_of_canonical` — **THE PLANE EXISTS**
    (`hall-analogue.md` Lemma 1): canonicality at `x` makes the nine points
    spanned by two lines through `x` induce Paley(9).
  * `IsFarCorner`, `exists_far_corner`, `far_corner_unique`,
    `far_corner_well_defined`, `far_corner_well_defined_of_canonical` (C3) —
    **THE FAR CORNER IS WELL DEFINED**, log 035's NEW RESULT 1: the far
    corner computed at one common neighbour of a non-adjacent pair equals the
    far corner computed at the other.  This is what makes the STS block
    `{x, y, x∘y}` a function of `{x,y}` alone.  The `_of_canonical` form has
    the grid hypothesis discharged and is the one to quote.
  * `IsBlock`, `sts_exact_cover` (C4a) — **THE STS COMPLETION**,
    `hall-analogue.md` Theorem 2.  The block set is
    `{graph lines} ∪ {{x, y, x∘y} : x ≁ y}` and every pair of distinct points
    lies in EXACTLY ONE block; `block_card` says every block has exactly
    three points.  Supporting: `IsDiagonal.symm`/`IsDiagonal.rotate` (the
    block is a well-defined 3-SET — any two of its points determine it),
    `IsDiagonal.pairwise` (a diagonal block is a co-triangle, so lines and
    diagonals never compete for a pair), `diagonal_unique` (= far-corner
    well-definedness in block form), `IsDiagonal.in_plane` (every diagonal
    block is a diagonal of a plane).
  * `ag23`, `plane_blocks_*` (C4b) — **EACH PLANE CARRIES THE 12-BLOCK
    AG(2,3) DESIGN**: 6 graph lines (rows and columns) + 6 diagonals, twelve
    distinct blocks, covering each of the plane's 36 point pairs exactly once
    (`ag23_exact_cover`, by `decide` at the index level), and the plane is
    CLOSED — the design's block through any two of its points is one of the
    twelve (`plane_blocks_closed`).
  * `sts_blocks_per_point`, `sts_block_count` (C4c) — the counting
    identity `r lines + 2·C(r,2) diagonals = r² blocks per point` that makes
    the Steiner completion close with no slack and no overlap.
  * `hall_fraction` (C5) — log 035's NEW RESULT 2, exactly: canonicality
    certifies `6·C(r,2)` of the `C(r²,2)` pairs of blocks at a point, i.e.
    the fraction `6/(r(r+1))`, which tends to 0.
  * `family_not_power_of_three` (C6) — **UNBOUNDED**: none of 99, 6273,
    494019 is `3ⁿ`, for ANY `n`, by two independent elementary routes
    (`not_pow_three_of_between`, `not_pow_three_of_not_dvd` with the
    verified factorisations `family_factorisations`).  This is the statement
    the Hall route would consume, and it carries no bound.
  * `diophantine_finite_check`, `diophantine_of_exp_le` (C6) — the general
    `1 + 2r² = 3ⁿ ⇒ r ∈ {0,1,2,11}` restricted to `n ≤ 12`.  This is a FINITE
    VERIFICATION by `decide`, exactly like `C3.lean`'s `c3_trace_core`, NOT a
    proof of the general Diophantine statement, which is Ramanujan–Nagell-type
    and CITED (see lean/README.md).

WHAT IS *NOT* PROVED HERE — read this before quoting anything.

  * The completion is proved as a DESIGN (exact cover by 3-sets), not as an
    ALGEBRA.  There is no Steiner operation `∘` as a function, hence no
    quasigroup/idempotence/`u ∘ (u ∘ w) = w` statements as equations — the
    file works relationally throughout (see `Transition.lean`'s design note),
    and total symmetry appears as `IsDiagonal.rotate`.  Nor is the number of
    blocks derived: `sts_block_count` is an arithmetic identity, and there is
    no double-counting layer proving `#blocks = v(v−1)/6` from the cover.
  * The AG(2,3) identification is "carries the 12-block design `ag23`", where
    `ag23` is the affine plane's block set written out on `Fin 3 × Fin 3`.
    There is no Lean model of `AG(2,3)` over `GF(3)` and no design-isomorphism
    statement.
  * `hall_fraction` is an ARITHMETIC identity.  It does not prove that the
    certified pairs are exactly the ones counted, only that the counts the
    note derives satisfy `6·C(r,2)/C(r²,2) = 6/(r(r+1))`.
  * The general Diophantine `1 + 2r² = 3ⁿ ⇒ r ∈ {0,1,2,11}` is NOT proved
    (only checked for `n ≤ 12`).  It is not needed: the application uses
    `family_not_power_of_three`, which is unbounded.
  * Nothing here bears on v = 99 by itself.  Log 031's exclusion of the
    canonical case is a SAT certificate; this file formalizes the geometry
    that surrounds it, not the certificate.  Nor does anything here prove
    that a canonical graph exists at any order — the closing section's
    Paley(9) witness is a witness for the HYPOTHESES (so that no theorem
    above is vacuous), not evidence about v = 99.
-/
import Mathlib
import Conway99.SRG
import Conway99.Transition

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-! ### C1 — canonicality at a root -/

/-- **CANONICAL AT `x`** — the transition system at the root `x` is the
canonical one, `M_a(b) = b′`.

Spelled out: for every `a ∈ N(x)` and every matched pair `{b,b′}` of `N(x)`
with `a ∉ {b,b′}`, the two label vertices `z_ab` and `z_ab′` are adjacent.
(By `not_adj_of_ne_class` below, `a ∉ {b,b′}` already forces `a ≁ b` and
`a ≁ b′`, so `z_ab` and `z_ab′` exist by `Transition.exists_label`.)

Equivalently — the reading used in `notes/math/hall-analogue.md` — any two
lines through `x` span an induced Paley(9). -/
def CanonicalAt (G : SimpleGraph V) (x : V) : Prop :=
  ∀ a b b' zab zab' : V, G.Adj x a → IsPartner G x b b' → a ≠ b → a ≠ b' →
    IsLabel G x a b zab → IsLabel G x a b' zab' → G.Adj zab zab'

/-- **CANONICALITY IS A GRAPH PROPERTY, NOT A LABELLING ARTEFACT.**  It
transports along any adjacency-preserving bijection: if `G` is canonical at
`x` and `f` is an isomorphism onto `G'`, then `G'` is canonical at `f x`.
(Used below to lift `paley9_canonicalAt` from one root to all nine by
translation — and it is the reason the definition may be quoted as a property
of the abstract graph.) -/
theorem CanonicalAt.transfer {W : Type*} {G' : SimpleGraph W} (f : V ≃ W)
    (hf : ∀ p q : V, G'.Adj (f p) (f q) ↔ G.Adj p q) {x : V}
    (hx : CanonicalAt G x) : CanonicalAt G' (f x) := by
  have hb : ∀ p q : W, G.Adj (f.symm p) (f.symm q) ↔ G'.Adj p q := by
    intro p q; rw [← hf (f.symm p) (f.symm q)]; simp
  intro a b b' zab zab' hxa hp hab hab' hz hz'
  have key := hx (f.symm a) (f.symm b) (f.symm b') (f.symm zab) (f.symm zab')
    ((hf x (f.symm a)).mp (by simpa using hxa))
    ⟨(hf x (f.symm b)).mp (by simpa using hp.1),
      (hf x (f.symm b')).mp (by simpa using hp.2.1), (hb b b').mpr hp.2.2⟩
    (fun he => hab (by simpa using congrArg f he))
    (fun he => hab' (by simpa using congrArg f he))
    ⟨(hb a zab).mpr hz.1, (hb b zab).mpr hz.2.1,
      (fun he => hz.2.2.1 (by simpa using congrArg f he)),
      (fun ha => hz.2.2.2 (by simpa using (hf x (f.symm zab)).mpr ha))⟩
    ⟨(hb a zab').mpr hz'.1, (hb b' zab').mpr hz'.2.1,
      (fun he => hz'.2.2.1 (by simpa using congrArg f he)),
      (fun ha => hz'.2.2.2 (by simpa using (hf x (f.symm zab')).mpr ha))⟩
  exact (hb zab zab').mp key

/-- **THE CLASS RULE, first half** (λ = 1 only).  A neighbour `a` of `x`
outside the matched class `{b,b′}` is adjacent to neither `b` nor `b′`:
`Γ[N(x)]` is a perfect *matching*, so its only edges are the classes. -/
theorem not_adj_of_ne_class (h : G.IsSRGWith n k 1 μ) {x a b b' : V}
    (hp : IsPartner G x b b') (hxa : G.Adj x a) (hab : a ≠ b) (hab' : a ≠ b') :
    ¬ G.Adj a b ∧ ¬ G.Adj a b' := by
  constructor
  · intro hadj
    exact hab' (partner_unique h (⟨hp.1, hxa, hadj.symm⟩ : IsPartner G x b a) hp)
  · intro hadj
    exact hab (partner_unique h (⟨hp.2.1, hxa, hadj.symm⟩ : IsPartner G x b' a) hp.symm)

/-- **THE CLASS RULE, second half** (λ = 1, plus canonicality at `x`).  Two
label vertices sharing the index `a` are adjacent ONLY IF their other indices
are matched: `z_ab ~ z_ac ⇒ z_ac = z_ab′`.

Proof: canonicality gives `z_ab ~ z_ab′`, so `z_ac` and `z_ab′` are two
common neighbours of the ADJACENT pair `{a, z_ab}`; λ = 1 identifies them. -/
theorem canonical_class_rule (h : G.IsSRGWith n k 1 μ) {x : V}
    (hcan : CanonicalAt G x) {a b b' c zab zab' zac : V}
    (hxa : G.Adj x a) (hpb : IsPartner G x b b') (hab : a ≠ b) (hab' : a ≠ b')
    (hzab : IsLabel G x a b zab) (hzab' : IsLabel G x a b' zab')
    (hzac : IsLabel G x a c zac) (hadj : G.Adj zab zac) : zac = zab' :=
  unique_common_of_adj h hzab.1
    ((mem_commonNeighbors G).mpr ⟨hzac.1, hadj⟩)
    ((mem_commonNeighbors G).mpr ⟨hzab'.1, hcan a b b' zab zab' hxa hpb hab hab' hzab hzab'⟩)

/-! ### C2 — plane uniqueness (μ = 2 only) -/

/-- **PLANE UNIQUENESS, the corner lemma** (μ = 2; NO canonicality).  Two
neighbours `c`, `d` of `x` in different matched classes are non-adjacent, so
they have exactly two common neighbours, one of which is `x`.  Hence the
other — the corner of the grid spanned by the lines through `c` and `d` — is
UNIQUE. -/
theorem corner_unique (h : G.IsSRGWith n k 1 2) {x c d z w : V}
    (hxc : G.Adj x c) (hxd : G.Adj x d) (hcd : ¬ G.Adj c d) (hne : c ≠ d)
    (hz : z ≠ x) (hz1 : G.Adj c z) (hz2 : G.Adj d z)
    (hw : w ≠ x) (hw1 : G.Adj c w) (hw2 : G.Adj d w) : z = w := by
  rcases two_common h hne hcd hxc.symm hxd.symm hz1 hz2 hw1 hw2 with hc | hc | hc
  · exact absurd hc.symm hz
  · exact absurd hc.symm hw
  · exact hc

/-- **PLANE UNIQUENESS**, set form.  Two nine-point configurations spanned by
the SAME pair of intersecting lines `{x,a,a′}`, `{x,b,b′}` are equal: the four
corners are pinned by μ = 2, so `Π(L,M)` is the only candidate.  This is
`notes/math/hall-analogue.md` Theorem 1(2), and — as the note stresses — it
uses no canonicality whatsoever. -/
theorem plane_set_unique (h : G.IsSRGWith n k 1 2) {x a a' b b' : V}
    (hpa : IsPartner G x a a') (hpb : IsPartner G x b b')
    (hab : a ≠ b) (hab' : a ≠ b') (ha'b : a' ≠ b) (ha'b' : a' ≠ b')
    {z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : V}
    (hz₁ : IsLabel G x a b z₁) (hz₂ : IsLabel G x a b' z₂)
    (hz₃ : IsLabel G x a' b z₃) (hz₄ : IsLabel G x a' b' z₄)
    (hw₁ : IsLabel G x a b w₁) (hw₂ : IsLabel G x a b' w₂)
    (hw₃ : IsLabel G x a' b w₃) (hw₄ : IsLabel G x a' b' w₄) :
    ({x, a, a', b, b', z₁, z₂, z₃, z₄} : Finset V) =
      ({x, a, a', b, b', w₁, w₂, w₃, w₄} : Finset V) := by
  obtain ⟨hnab, hnab'⟩ := not_adj_of_ne_class h hpb hpa.1 hab hab'
  obtain ⟨hna'b, hna'b'⟩ := not_adj_of_ne_class h hpb hpa.2.1 ha'b ha'b'
  have e₁ : z₁ = w₁ := corner_unique h hpa.1 hpb.1 hnab hab
    hz₁.2.2.1 hz₁.1 hz₁.2.1 hw₁.2.2.1 hw₁.1 hw₁.2.1
  have e₂ : z₂ = w₂ := corner_unique h hpa.1 hpb.2.1 hnab' hab'
    hz₂.2.2.1 hz₂.1 hz₂.2.1 hw₂.2.2.1 hw₂.1 hw₂.2.1
  have e₃ : z₃ = w₃ := corner_unique h hpa.2.1 hpb.1 hna'b ha'b
    hz₃.2.2.1 hz₃.1 hz₃.2.1 hw₃.2.2.1 hw₃.1 hw₃.2.1
  have e₄ : z₄ = w₄ := corner_unique h hpa.2.1 hpb.2.1 hna'b' ha'b'
    hz₄.2.2.1 hz₄.1 hz₄.2.1 hw₄.2.2.1 hw₄.1 hw₄.2.1
  rw [e₁, e₂, e₃, e₄]

/-! ### The chordless quadrangle -/

/-- λ = 1: two DISTINCT common neighbours of a pair `{u,w}` with `u ≠ w` are
themselves non-adjacent — otherwise the edge between them would lie in two
triangles. -/
theorem common_neighbors_not_adj (h : G.IsSRGWith n k 1 μ) {u w p q : V}
    (hne : u ≠ w) (hpu : G.Adj p u) (hpw : G.Adj p w)
    (hqu : G.Adj q u) (hqw : G.Adj q w) : ¬ G.Adj p q := by
  intro hpq
  exact hne (unique_common_of_adj h hpq
    ((mem_commonNeighbors G).mpr ⟨hpu, hqu⟩)
    ((mem_commonNeighbors G).mpr ⟨hpw, hqw⟩))

/-- **THE CHORDLESS QUADRANGLE** (λ = 1, μ = 2) — the configuration behind
`notes/math/hall-analogue.md` Theorem 1(3).  If `x ≠ y` have two distinct
common neighbours `u ≠ w`, then `x–u–y–w–x` is an INDUCED 4-cycle: `u ≁ w`,
`x ≁ y`, the common neighbours of `u` and `w` are exactly `x` and `y`, and
the common neighbours of `x` and `y` are exactly `u` and `w`. -/
theorem chordless_quadrangle (h : G.IsSRGWith n k 1 2) {x y u w : V}
    (hxy : x ≠ y) (huw : u ≠ w)
    (hux : G.Adj u x) (huy : G.Adj u y) (hwx : G.Adj w x) (hwy : G.Adj w y) :
    ¬ G.Adj u w ∧ ¬ G.Adj x y ∧
      (∀ t, G.Adj u t → G.Adj w t → t = x ∨ t = y) ∧
      (∀ t, G.Adj x t → G.Adj y t → t = u ∨ t = w) := by
  have h1 : ¬ G.Adj u w := common_neighbors_not_adj h hxy hux huy hwx hwy
  have h2 : ¬ G.Adj x y :=
    common_neighbors_not_adj h huw hux.symm hwx.symm huy.symm hwy.symm
  refine ⟨h1, h2, ?_, ?_⟩
  · intro t hut hwt
    rcases two_common h huw h1 hux hwx huy hwy hut hwt with hc | hc | hc
    · exact absurd hc hxy
    · exact Or.inl hc.symm
    · exact Or.inr hc.symm
  · intro t hxt hyt
    rcases two_common h hxy h2 hux.symm huy.symm hwx.symm hwy.symm hxt hyt with
      hc | hc | hc
    · exact absurd hc huw
    · exact Or.inl hc.symm
    · exact Or.inr hc.symm

/-! ### C3 — the grid, and the far corner

The *plane* of `notes/math/hall-analogue.md` is a 3×3 grid (= Paley(9) = the
rook's graph): nine distinct points in which two are adjacent exactly when
they share a row or a column.  `IsGrid` records that, with the six lines
being the three rows and the three columns.

Under `CanonicalAt G x` the nine points

    x    b    b′
    a    z_ab   z_ab′
    a′   z_a′b  z_a′b′

form such a grid — that is Lemma 1 of the note, and it is NOT formalized
here; `IsGrid` is a hypothesis below.  Non-vacuity is settled by the Paley(9)
witness at the end of the file.
-/

/-- A 3×3 **GRID** inside `G`, given by its nine points `pt i j`: the points
are distinct, points sharing a row or a column are adjacent, and points
sharing neither are non-adjacent. -/
structure IsGrid (G : SimpleGraph V) (pt : Fin 3 → Fin 3 → V) : Prop where
  /-- the nine points are pairwise distinct -/
  inj : ∀ i j i' j', pt i j = pt i' j' → i = i' ∧ j = j'
  /-- each row is a line -/
  row : ∀ i j j', j ≠ j' → G.Adj (pt i j) (pt i j')
  /-- each column is a line -/
  col : ∀ i i' j, i ≠ i' → G.Adj (pt i j) (pt i' j)
  /-- points in different rows AND different columns are non-adjacent -/
  off : ∀ i j i' j', i ≠ i' → j ≠ j' → ¬ G.Adj (pt i j) (pt i' j')

/-- The nine points of the plane spanned by the lines `{x,a,a′}` and
`{x,b,b′}`, laid out as

    x    b     b′
    a    z_ab  z_ab′
    a′   z_a′b z_a′b′
-/
def gridPt (x b b' a z₁ z₂ a' z₃ z₄ : V) (i j : Fin 3) : V :=
  ![![x, b, b'], ![a, z₁, z₂], ![a', z₃, z₄]] i j

/-- **THE PLANE EXISTS** — `notes/math/hall-analogue.md` Lemma 1.  If `G` is
canonical at `x`, then any two lines `{x,a,a′}`, `{x,b,b′}` through `x` span
a GRID: the nine points above induce Paley(9), with the three rows and three
columns as its six lines.

Together with `plane_set_unique` (which needs only μ = 2) this says the plane
through two intersecting lines exists and is unique — and with
`far_corner_well_defined` it discharges the `IsGrid` hypothesis there for any
canonical graph. -/
theorem grid_of_canonical (h : G.IsSRGWith n k 1 2) {x a a' b b' z₁ z₂ z₃ z₄ : V}
    (hcan : CanonicalAt G x)
    (hpa : IsPartner G x a a') (hpb : IsPartner G x b b')
    (hab : a ≠ b) (hab' : a ≠ b') (ha'b : a' ≠ b) (ha'b' : a' ≠ b')
    (hz₁ : IsLabel G x a b z₁) (hz₂ : IsLabel G x a b' z₂)
    (hz₃ : IsLabel G x a' b z₃) (hz₄ : IsLabel G x a' b' z₄) :
    IsGrid G (gridPt x b b' a z₁ z₂ a' z₃ z₄) := by
  -- ADJACENCIES: the six lines
  have Axb : G.Adj x b := hpb.1
  have Axb' : G.Adj x b' := hpb.2.1
  have Abb' : G.Adj b b' := hpb.2.2
  have Axa : G.Adj x a := hpa.1
  have Axa' : G.Adj x a' := hpa.2.1
  have Aaa' : G.Adj a a' := hpa.2.2
  have Aaz₁ : G.Adj a z₁ := hz₁.1
  have Aaz₂ : G.Adj a z₂ := hz₂.1
  have Az₁z₂ : G.Adj z₁ z₂ := hcan a b b' z₁ z₂ hpa.1 hpb hab hab' hz₁ hz₂
  have Aa'z₃ : G.Adj a' z₃ := hz₃.1
  have Aa'z₄ : G.Adj a' z₄ := hz₄.1
  have Az₃z₄ : G.Adj z₃ z₄ := hcan a' b b' z₃ z₄ hpa.2.1 hpb ha'b ha'b' hz₃ hz₄
  have Abz₁ : G.Adj b z₁ := hz₁.2.1
  have Abz₃ : G.Adj b z₃ := hz₃.2.1
  have Az₁z₃ : G.Adj z₁ z₃ :=
    hcan b a a' z₁ z₃ hpb.1 hpa hab.symm ha'b.symm hz₁.symm hz₃.symm
  have Ab'z₂ : G.Adj b' z₂ := hz₂.2.1
  have Ab'z₄ : G.Adj b' z₄ := hz₄.2.1
  have Az₂z₄ : G.Adj z₂ z₄ :=
    hcan b' a a' z₂ z₄ hpb.2.1 hpa hab'.symm ha'b'.symm hz₂.symm hz₄.symm
  -- NON-ADJACENCIES
  have Nxz₁ : ¬ G.Adj x z₁ := hz₁.2.2.2
  have Nxz₂ : ¬ G.Adj x z₂ := hz₂.2.2.2
  have Nxz₃ : ¬ G.Adj x z₃ := hz₃.2.2.2
  have Nxz₄ : ¬ G.Adj x z₄ := hz₄.2.2.2
  obtain ⟨Nab, Nab'⟩ := not_adj_of_ne_class h hpb hpa.1 hab hab'
  obtain ⟨Na'b, Na'b'⟩ := not_adj_of_ne_class h hpb hpa.2.1 ha'b ha'b'
  have Naz₃ : ¬ G.Adj a z₃ := label_not_matched h hpa.symm hz₃.1 hz₃.2.2.1
  have Naz₄ : ¬ G.Adj a z₄ := label_not_matched h hpa.symm hz₄.1 hz₄.2.2.1
  have Na'z₁ : ¬ G.Adj a' z₁ := label_not_matched h hpa hz₁.1 hz₁.2.2.1
  have Na'z₂ : ¬ G.Adj a' z₂ := label_not_matched h hpa hz₂.1 hz₂.2.2.1
  have Nbz₂ : ¬ G.Adj b z₂ := label_not_matched h hpb.symm hz₂.2.1 hz₂.2.2.1
  have Nbz₄ : ¬ G.Adj b z₄ := label_not_matched h hpb.symm hz₄.2.1 hz₄.2.2.1
  have Nb'z₁ : ¬ G.Adj b' z₁ := label_not_matched h hpb hz₁.2.1 hz₁.2.2.1
  have Nb'z₃ : ¬ G.Adj b' z₃ := label_not_matched h hpb hz₃.2.1 hz₃.2.2.1
  -- the two DIAGONAL non-adjacencies — the only ones that need work
  have Ez₁z₂ : z₁ ≠ z₂ := label_ne_of_partner h hpb hz₁ hz₂
  have Ez₃z₄ : z₃ ≠ z₄ := label_ne_of_partner h hpb hz₃ hz₄
  have Eaz₄ : a ≠ z₄ := by rintro rfl; exact Nxz₄ Axa
  have Eaz₃ : a ≠ z₃ := by rintro rfl; exact Nxz₃ Axa
  have Nz₁z₄ : ¬ G.Adj z₁ z₄ := by
    intro hadj
    rcases two_common h Eaz₄ Naz₄ Aaa' Aa'z₄.symm Aaz₂ Az₂z₄.symm Aaz₁ hadj.symm
      with hc | hc | hc
    · exact Nxz₂ (hc ▸ Axa')
    · exact Nxz₁ (hc ▸ Axa')
    · exact Ez₁z₂ hc.symm
  have Nz₂z₃ : ¬ G.Adj z₂ z₃ := by
    intro hadj
    rcases two_common h Eaz₃ Naz₃ Aaa' Aa'z₃.symm Aaz₁ Az₁z₃.symm Aaz₂ hadj.symm
      with hc | hc | hc
    · exact Nxz₁ (hc ▸ Axa')
    · exact Nxz₂ (hc ▸ Axa')
    · exact Ez₁z₂ hc
  -- DISTINCTNESS of the nine points
  have Exb : x ≠ b := Axb.ne
  have Exb' : x ≠ b' := Axb'.ne
  have Ebb' : b ≠ b' := Abb'.ne
  have Exa : x ≠ a := Axa.ne
  have Exa' : x ≠ a' := Axa'.ne
  have Eaa' : a ≠ a' := Aaa'.ne
  have Eaz₁ : a ≠ z₁ := Aaz₁.ne
  have Eaz₂ : a ≠ z₂ := Aaz₂.ne
  have Ea'z₃ : a' ≠ z₃ := Aa'z₃.ne
  have Ea'z₄ : a' ≠ z₄ := Aa'z₄.ne
  have Ebz₁ : b ≠ z₁ := Abz₁.ne
  have Ebz₃ : b ≠ z₃ := Abz₃.ne
  have Ez₁z₃ : z₁ ≠ z₃ := Az₁z₃.ne
  have Eb'z₂ : b' ≠ z₂ := Ab'z₂.ne
  have Eb'z₄ : b' ≠ z₄ := Ab'z₄.ne
  have Ez₂z₄ : z₂ ≠ z₄ := Az₂z₄.ne
  have Exz₁ : x ≠ z₁ := Ne.symm hz₁.2.2.1
  have Exz₂ : x ≠ z₂ := Ne.symm hz₂.2.2.1
  have Exz₃ : x ≠ z₃ := Ne.symm hz₃.2.2.1
  have Exz₄ : x ≠ z₄ := Ne.symm hz₄.2.2.1
  have Ea'z₁ : a' ≠ z₁ := by rintro rfl; exact Nxz₁ Axa'
  have Ea'z₂ : a' ≠ z₂ := by rintro rfl; exact Nxz₂ Axa'
  have Ebz₂ : b ≠ z₂ := by rintro rfl; exact Nxz₂ Axb
  have Ebz₄ : b ≠ z₄ := by rintro rfl; exact Nxz₄ Axb
  have Eb'z₁ : b' ≠ z₁ := by rintro rfl; exact Nxz₁ Axb'
  have Eb'z₃ : b' ≠ z₃ := by rintro rfl; exact Nxz₃ Axb'
  have Ez₁z₄ : z₁ ≠ z₄ := by rintro rfl; exact Na'z₁ Aa'z₄
  have Ez₂z₃ : z₂ ≠ z₃ := by rintro rfl; exact Na'z₂ Aa'z₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j i' j'
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      simp only [gridPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact fun _ => ⟨rfl, rfl⟩
        | (intro he; exact absurd he (by assumption))
        | (intro he; exact absurd he.symm (by assumption))
        | (intro _; trivial)
        | (intro _; exact ⟨rfl, rfl⟩)
  · intro i j j' hj
    fin_cases i <;> fin_cases j <;> fin_cases j' <;>
      simp only [gridPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hj
        | assumption
        | exact (by assumption : G.Adj _ _).symm
  · intro i i' j hi
    fin_cases i <;> fin_cases i' <;> fin_cases j <;>
      simp only [gridPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hi
        | assumption
        | exact (by assumption : G.Adj _ _).symm
  · intro i j i' j' hi hj
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      simp only [gridPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hi
        | exact absurd rfl hj
        | assumption
        | exact fun hadj => (by assumption : ¬ G.Adj _ _) hadj.symm

/-- `F` is the **FAR CORNER** of the pair `{x,y}` computed at their common
neighbour `u`: writing `p`, `q` for the apexes of the edges `ux`, `uy` (the
third points of the lines `ux`, `uy`), `F` is a common neighbour of `p` and
`q` other than `u`.  In the grid at `u`

    u   y   q
    x   ·   ·
    p   ·   F

`F` is the point diagonally opposite `u`, and `{x, y, F}` is the Steiner
block through the non-adjacent pair `{x,y}`. -/
def IsFarCorner (G : SimpleGraph V) (u x y F : V) : Prop :=
  ∃ p q, IsApex G u x p ∧ IsApex G u y q ∧ G.Adj p F ∧ G.Adj q F ∧ F ≠ u

/-- The far corner is symmetric in `x` and `y` — commutativity of the Steiner
operation, immediate from the definition. -/
theorem IsFarCorner.symm {u x y F : V} (hF : IsFarCorner G u x y F) :
    IsFarCorner G u y x F := by
  obtain ⟨p, q, hp, hq, hpF, hqF, hne⟩ := hF
  exact ⟨q, p, hq, hp, hqF, hpF, hne⟩

/-- The two apexes at `u` of a NON-adjacent pair `{x,y}` are distinct and
themselves non-adjacent.  (If `p = q` the two lines `ux`, `uy` would share two
points and hence coincide, forcing `x ~ y`; if `p ~ q` then `x` and `q` would
be two common neighbours of the adjacent pair `{u,p}`, again forcing `x ~ y`.)
-/
theorem apexes_not_adj (h : G.IsSRGWith n k 1 μ) {u x y p q : V}
    (hxy : ¬ G.Adj x y) (hne : x ≠ y)
    (hp : IsApex G u x p) (hq : IsApex G u y q) : p ≠ q ∧ ¬ G.Adj p q := by
  have hpq_ne : p ≠ q := by
    rintro rfl
    exact hne (unique_common_of_adj h hp.2.1
      ((mem_commonNeighbors G).mpr ⟨hp.1, hp.2.2.symm⟩)
      ((mem_commonNeighbors G).mpr ⟨hq.1, hq.2.2.symm⟩))
  refine ⟨hpq_ne, ?_⟩
  intro hadj
  -- `x` and `q` are both common neighbours of the adjacent pair `{u,p}`
  have hxq : x = q := unique_common_of_adj h hp.2.1
    ((mem_commonNeighbors G).mpr ⟨hp.1, hp.2.2.symm⟩)
    ((mem_commonNeighbors G).mpr ⟨hq.2.1, hadj⟩)
  subst hxq
  exact hxy hq.2.2.symm

/-- **THE FAR CORNER EXISTS** at every common neighbour of a non-adjacent
pair (μ = 2 applied to the two apexes). -/
theorem exists_far_corner (h : G.IsSRGWith n k 1 2) {u x y p q : V}
    (hxy : ¬ G.Adj x y) (hne : x ≠ y)
    (hp : IsApex G u x p) (hq : IsApex G u y q) :
    ∃ F, IsFarCorner G u x y F := by
  obtain ⟨hpq_ne, hpq⟩ := apexes_not_adj h hxy hne hp hq
  obtain ⟨F, hFu, hF1, hF2⟩ :=
    exists_second_common h hpq_ne hpq hp.2.1.symm hq.2.1.symm
  exact ⟨F, p, q, hp, hq, hF1, hF2, hFu⟩

/-- **THE FAR CORNER IS UNIQUE** at each common neighbour (μ = 2). -/
theorem far_corner_unique (h : G.IsSRGWith n k 1 2) {u x y F F' : V}
    (hxy : ¬ G.Adj x y) (hne : x ≠ y)
    (hF : IsFarCorner G u x y F) (hF' : IsFarCorner G u x y F') : F = F' := by
  obtain ⟨p, q, hp, hq, hpF, hqF, hFne⟩ := hF
  obtain ⟨p', q', hp', hq', hpF', hqF', hFne'⟩ := hF'
  have ep : p' = p := apex_unique h hp' hp
  have eq' : q' = q := apex_unique h hq' hq
  subst ep; subst eq'
  obtain ⟨hpq_ne, hpq⟩ := apexes_not_adj h hxy hne hp hq
  rcases two_common h hpq_ne hpq hp.2.1.symm hq.2.1.symm hpF hqF hpF' hqF'
    with hc | hc | hc
  · exact absurd hc.symm hFne
  · exact absurd hc.symm hFne'
  · exact hc

/-- **THE FAR CORNER EXISTS AND IS UNIQUE — UNCONDITIONALLY.**  The apex
hypotheses of `exists_far_corner` are not an extra assumption: λ = 1 supplies
the apexes (`Transition.exists_apex`).  So for ANY non-adjacent pair `x ≁ y`
and ANY common neighbour `u`, the far corner at `u` is a well-defined point.
This is the form the Steiner completion needs, and it uses NO canonicality. -/
theorem exists_unique_far_corner (h : G.IsSRGWith n k 1 2) {u x y : V}
    (hux : G.Adj u x) (huy : G.Adj u y) (hxy : ¬ G.Adj x y) (hne : x ≠ y) :
    ∃! F, IsFarCorner G u x y F := by
  obtain ⟨p, hp, -⟩ := exists_apex h hux
  obtain ⟨q, hq, -⟩ := exists_apex h huy
  obtain ⟨F, hF⟩ := exists_far_corner h hxy hne hp hq
  exact ⟨F, hF, fun F' hF' => far_corner_unique h hxy hne hF' hF⟩

/-- **THE APEX DEFINITION AGREES WITH THE NOTE'S.**
`hall-analogue.md` Theorem 2 defines `x ∘ y` for `x ≁ y` as *the unique point
of the plane `Π(x,y)` non-adjacent to both*; `IsFarCorner` defines it by the
two apexes.  Inside a grid the two descriptions agree: the only points
non-adjacent to both `pt 1 0` and `pt 0 1` are those two themselves and the
diagonally opposite `pt 2 2`, which is the point `far_corner_well_defined`
pins the far corner to. -/
theorem grid_far_point {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt)
    (i j : Fin 3) (h1 : ¬ G.Adj (pt i j) (pt 1 0))
    (h2 : ¬ G.Adj (pt i j) (pt 0 1)) :
    (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | exact absurd (hgrid.col 0 1 0 (by decide)) h1
      | exact absurd (hgrid.row 0 2 1 (by decide)) h2
      | exact absurd (hgrid.row 1 1 0 (by decide)) h1
      | exact absurd (hgrid.row 1 2 0 (by decide)) h1
      | exact absurd (hgrid.col 2 1 0 (by decide)) h1
      | exact absurd (hgrid.col 2 0 1 (by decide)) h2

/-- **FAR CORNER WELL-DEFINED** — log 035's NEW RESULT 1, machine-checked.

Let `x = pt 1 0` and `y = pt 0 1` be the two points of a grid adjacent to its
corner `u = pt 0 0` but not to each other, and let `w` be any other common
neighbour of `x` and `y`.  Then:

  * μ = 2 forces `w` to be the INNER CORNER `pt 1 1` of the grid — this is
    the step the log describes as "μ = 2 forces `u′` to lie IN that grid";
  * consequently the far corner computed at `u` and the far corner computed
    at `w` are the SAME point, namely `pt 2 2`.

So the Steiner block `{x, y, x∘y}` does not depend on which of the two common
neighbours of `x` and `y` is used to build it. -/
theorem far_corner_well_defined (h : G.IsSRGWith n k 1 2)
    {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) {w Fu Fw : V}
    (hwu : w ≠ pt 0 0) (hwx : G.Adj (pt 1 0) w) (hwy : G.Adj (pt 0 1) w)
    (hFu : IsFarCorner G (pt 0 0) (pt 1 0) (pt 0 1) Fu)
    (hFw : IsFarCorner G w (pt 1 0) (pt 0 1) Fw) :
    w = pt 1 1 ∧ Fu = pt 2 2 ∧ Fw = pt 2 2 := by
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have d10 : (1 : Fin 3) ≠ 0 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  have d20 : (2 : Fin 3) ≠ 0 := by decide
  have d21 : (2 : Fin 3) ≠ 1 := by decide
  -- the two points `x = pt 1 0` and `y = pt 0 1` are distinct and non-adjacent
  have hxy_nadj : ¬ G.Adj (pt 1 0) (pt 0 1) := hgrid.off 1 0 0 1 d10 d01
  have hxy_ne : pt 1 0 ≠ pt 0 1 := fun he => d10 (hgrid.inj 1 0 0 1 he).1
  -- the corner and the inner corner are both common neighbours of `x` and `y`
  have hu_x : G.Adj (pt 0 0) (pt 1 0) := hgrid.col 0 1 0 d01
  have hu_y : G.Adj (pt 0 0) (pt 0 1) := hgrid.row 0 0 1 d01
  have hi_x : G.Adj (pt 1 1) (pt 1 0) := hgrid.row 1 1 0 d10
  have hi_y : G.Adj (pt 1 1) (pt 0 1) := hgrid.col 1 0 1 d10
  -- STEP 1: μ = 2 forces `w` to BE the inner corner
  have hw11 : w = pt 1 1 := by
    rcases two_common h hxy_ne hxy_nadj hu_x.symm hu_y.symm hi_x.symm hi_y.symm
      hwx hwy with hc | hc | hc
    · exact absurd (hgrid.inj 0 0 1 1 hc).1 d01
    · exact absurd hc.symm hwu
    · exact hc.symm
  subst hw11
  -- STEP 2: the far corner at the corner `pt 0 0`
  obtain ⟨p, q, hp, hq, hpF, hqF, hFne⟩ := hFu
  have hp_eq : p = pt 2 0 :=
    apex_unique h hp ⟨hu_x, hgrid.col 0 2 0 d02, hgrid.col 1 2 0 d12⟩
  have hq_eq : q = pt 0 2 :=
    apex_unique h hq ⟨hu_y, hgrid.row 0 0 2 d02, hgrid.row 0 1 2 d12⟩
  subst hp_eq; subst hq_eq
  have hnadj1 : ¬ G.Adj (pt 2 0) (pt 0 2) := hgrid.off 2 0 0 2 d20 d02
  have hne1 : pt 2 0 ≠ pt 0 2 := fun he => d20 (hgrid.inj 2 0 0 2 he).1
  have hFu_eq : Fu = pt 2 2 := by
    rcases two_common h hne1 hnadj1
      (hgrid.col 2 0 0 d20) (hgrid.row 0 2 0 d20)
      (hgrid.row 2 0 2 d02) (hgrid.col 0 2 2 d02) hpF hqF with hc | hc | hc
    · exact absurd (hgrid.inj 0 0 2 2 hc).1 d02
    · exact absurd hc.symm hFne
    · exact hc.symm
  -- STEP 3: the far corner at the inner corner `pt 1 1` — the SAME point
  obtain ⟨p', q', hp', hq', hpF', hqF', hFne'⟩ := hFw
  have hp'_eq : p' = pt 1 2 :=
    apex_unique h hp' ⟨hi_x, hgrid.row 1 1 2 d12, hgrid.row 1 0 2 d02⟩
  have hq'_eq : q' = pt 2 1 :=
    apex_unique h hq' ⟨hi_y, hgrid.col 1 2 1 d12, hgrid.col 0 2 1 d02⟩
  subst hp'_eq; subst hq'_eq
  have hnadj2 : ¬ G.Adj (pt 1 2) (pt 2 1) := hgrid.off 1 2 2 1 d12 d21
  have hne2 : pt 1 2 ≠ pt 2 1 := fun he => d12 (hgrid.inj 1 2 2 1 he).1
  have hFw_eq : Fw = pt 2 2 := by
    rcases two_common h hne2 hnadj2
      (hgrid.row 1 2 1 d21) (hgrid.col 2 1 1 d21)
      (hgrid.col 1 2 2 d12) (hgrid.row 2 1 2 d12) hpF' hqF' with hc | hc | hc
    · exact absurd (hgrid.inj 1 1 2 2 hc).1 d12
    · exact absurd hc.symm hFne'
    · exact hc.symm
  exact ⟨rfl, hFu_eq, hFw_eq⟩

/-- **THE CAPSTONE** — `far_corner_well_defined` with the grid hypothesis
DISCHARGED by `grid_of_canonical`.

Let `G` be canonical at `u`, and let `x ≁ y` be two neighbours of `u` (so `u`
is one of their exactly two common neighbours).  Then for the OTHER common
neighbour `w`, the far corner computed at `u` and the far corner computed at
`w` coincide.

This is log 035's NEW RESULT 1 in the form it is quoted: *canonical + μ = 2 ⇒
the Steiner block `{x, y, x∘y}` through a non-adjacent pair is
well-defined*. -/
theorem far_corner_well_defined_of_canonical (h : G.IsSRGWith n k 1 2)
    {u x y w Fu Fw : V} (hcan : CanonicalAt G u)
    (hux : G.Adj u x) (huy : G.Adj u y) (hxy : ¬ G.Adj x y) (hxyne : x ≠ y)
    (hwu : w ≠ u) (hwx : G.Adj x w) (hwy : G.Adj y w)
    (hFu : IsFarCorner G u x y Fu) (hFw : IsFarCorner G w x y Fw) : Fu = Fw := by
  -- the two lines through `u`
  obtain ⟨x', hpx, -⟩ := exists_unique_partner h hux
  obtain ⟨y', hpy, -⟩ := exists_unique_partner h huy
  have hxy' : x ≠ y' := by
    rintro rfl; exact hxy hpy.2.2.symm
  have hx'y : x' ≠ y := by
    rintro rfl; exact hxy hpx.2.2
  have hx'y' : x' ≠ y' := by
    rintro rfl; exact hxyne (partner_injective h hpx hpy)
  -- the four label vertices of the plane spanned by those lines
  obtain ⟨hnxy, hnxy'⟩ := not_adj_of_ne_class h hpy hux hxyne hxy'
  obtain ⟨hnx'y, hnx'y'⟩ := not_adj_of_ne_class h hpy hpx.2.1 hx'y hx'y'
  obtain ⟨z₁, hz₁⟩ := exists_label h hux huy hnxy hxyne
  obtain ⟨z₂, hz₂⟩ := exists_label h hux hpy.2.1 hnxy' hxy'
  obtain ⟨z₃, hz₃⟩ := exists_label h hpx.2.1 huy hnx'y hx'y
  obtain ⟨z₄, hz₄⟩ := exists_label h hpx.2.1 hpy.2.1 hnx'y' hx'y'
  have hgrid : IsGrid G (gridPt u y y' x z₁ z₂ x' z₃ z₄) :=
    grid_of_canonical h hcan hpx hpy hxyne hxy' hx'y hx'y' hz₁ hz₂ hz₃ hz₄
  obtain ⟨-, h1, h2⟩ :=
    far_corner_well_defined h hgrid (w := w) hwu hwx hwy hFu hFw
  rw [h1, h2]

/-! ### C4a — THE STEINER COMPLETION: the block set, and the EXACT COVER

`notes/math/hall-analogue.md` Theorem 2 completes the graph's partial "third
point" operation to a Steiner triple system whose blocks are the lines of `Γ`
together with the six diagonals of each plane.  This section CONSTRUCTS that
block set and proves its defining property — **every pair of distinct points
lies in EXACTLY ONE block** (`sts_exact_cover`) — decomposed exactly as the
note decomposes it:

  * an ADJACENT pair lies in its unique line (λ = 1: `exists_apex`,
    `apex_unique`) and in NO diagonal block, because all three pairs of a
    diagonal block are non-adjacent (`IsDiagonal.pairwise`,
    `not_adj_of_mem_diagonal`);
  * a NON-ADJACENT pair lies in exactly one diagonal block — existence from
    `exists_unique_far_corner` (μ = 2), uniqueness from `diagonal_unique`,
    which IS far-corner well-definedness — and in NO line, because the three
    points of a line are pairwise adjacent (`adj_of_mem_line`).

The block set is well defined AS A SET: not only is the third point symmetric
in the two points that define it (`IsDiagonal.symm`, from `IsFarCorner.symm`),
the whole 3-set is — ANY two of its three points define it
(`IsDiagonal.rotate`), which is the total symmetry of the Steiner operation.

WHERE THE HYPOTHESES ARE USED.  `sts_exact_cover` assumes λ = 1, μ = 2 and
`Canonical G` (canonical at EVERY vertex — `hall-analogue.md`'s unqualified
"canonical").  Canonicality enters in exactly two places, both through the
grid of `grid_of_canonical`: `IsDiagonal.rotate` and `diagonal_unique`.
Everything else — the entire adjacent case, and the non-adjacency of all
three pairs of a diagonal block — uses λ = 1 and μ = 2 alone.
-/

/-- **CANONICAL**, unqualified, as in `notes/math/hall-analogue.md`: canonical
at EVERY vertex.  (Log 031 certifies the failure of `CanonicalAt` at a SINGLE
vertex for v = 99, which is strictly stronger than the failure of this.) -/
def Canonical (G : SimpleGraph V) : Prop := ∀ x, CanonicalAt G x

/-- **THE DIAGONAL BLOCK** through a non-adjacent pair: `F` is a far corner of
`{x,y}` at SOME common neighbour of `x` and `y`.  By `diagonal_unique` — which
is far-corner well-definedness — the common neighbour used does not matter, so
`{x, y, F}` is a function of the pair `{x,y}` alone. -/
def IsDiagonal (G : SimpleGraph V) (x y F : V) : Prop :=
  x ≠ y ∧ ¬ G.Adj x y ∧ ∃ u, IsFarCorner G u x y F

/-- **THE BLOCK SET** `B := {graph lines} ∪ {{x, y, x∘y} : x ≁ y}`, as a
predicate on 3-element subsets of `V`. -/
def IsBlock (G : SimpleGraph V) (B : Finset V) : Prop :=
  (∃ p q r, IsLine G p q r ∧ B = {p, q, r}) ∨
    (∃ x y F, IsDiagonal G x y F ∧ B = {x, y, F})

/-- The far corner's anchor is adjacent to the first defining point. -/
theorem IsFarCorner.adj_left {u x y F : V} (hF : IsFarCorner G u x y F) :
    G.Adj u x := by obtain ⟨p, q, hp, -⟩ := hF; exact hp.1

/-- The far corner's anchor is adjacent to the second defining point. -/
theorem IsFarCorner.adj_right {u x y F : V} (hF : IsFarCorner G u x y F) :
    G.Adj u y := by obtain ⟨p, q, -, hq, -⟩ := hF; exact hq.1

/-- The diagonal block is symmetric in its two defining points. -/
theorem IsDiagonal.symm {x y F : V} (hd : IsDiagonal G x y F) :
    IsDiagonal G y x F := by
  obtain ⟨hne, hnadj, u, hF⟩ := hd
  exact ⟨hne.symm, fun ha => hnadj ha.symm, u, hF.symm⟩

/-- **THE THIRD POINT OF A DIAGONAL BLOCK IS A NEW POINT, NON-ADJACENT TO THE
FIRST** (λ = 1 only).  `x ≠ F`: otherwise `x` and `y` would be two common
neighbours of the adjacent pair `{u,q}`.  `x ≁ F`: otherwise `u` and `F`
would be two apexes of the edge `{x,p}`. -/
theorem IsDiagonal.third (h : G.IsSRGWith n k 1 μ) {x y F : V}
    (hd : IsDiagonal G x y F) : x ≠ F ∧ ¬ G.Adj x F := by
  obtain ⟨hne, hnadj, u, p, q, hp, hq, hpF, hqF, hFu⟩ := hd
  constructor
  · intro he
    exact hne (unique_common_of_adj h hq.2.1
      ((mem_commonNeighbors G).mpr ⟨hp.1, by rw [he]; exact hqF⟩)
      ((mem_commonNeighbors G).mpr ⟨hq.1, hq.2.2.symm⟩))
  · intro hadj
    exact hFu (unique_common_of_adj h hp.2.2
      ((mem_commonNeighbors G).mpr ⟨hp.1.symm, hp.2.1.symm⟩)
      ((mem_commonNeighbors G).mpr ⟨hadj, hpF⟩)).symm

/-- **A DIAGONAL BLOCK IS A CO-TRIANGLE** (λ = 1 only): its three points are
distinct and PAIRWISE NON-ADJACENT.  This is what keeps the diagonals disjoint
from the lines: an adjacent pair can never lie in one. -/
theorem IsDiagonal.pairwise (h : G.IsSRGWith n k 1 μ) {x y F : V}
    (hd : IsDiagonal G x y F) :
    (x ≠ y ∧ x ≠ F ∧ y ≠ F) ∧ ¬ G.Adj x y ∧ ¬ G.Adj x F ∧ ¬ G.Adj y F :=
  ⟨⟨hd.1, (hd.third h).1, (hd.symm.third h).1⟩,
   hd.2.1, (hd.third h).2, (hd.symm.third h).2⟩

/-! #### The grid, revisited: the far corner is the opposite corner -/

/-- **THE GRID EXISTS AT A CANONICAL ROOT**, in the form the block calculus
needs: for `x ≁ y` two neighbours of a canonical `u`, there is a grid whose
corner is `u` and whose two neighbouring points are `x` and `y`.  (This is the
first half of `far_corner_well_defined_of_canonical`'s proof, extracted.) -/
theorem exists_grid_of_canonical (h : G.IsSRGWith n k 1 2) {u x y : V}
    (hcan : CanonicalAt G u) (hux : G.Adj u x) (huy : G.Adj u y)
    (hxy : ¬ G.Adj x y) (hxyne : x ≠ y) :
    ∃ pt : Fin 3 → Fin 3 → V, IsGrid G pt ∧ pt 0 0 = u ∧ pt 1 0 = x ∧ pt 0 1 = y := by
  obtain ⟨x', hpx, -⟩ := exists_unique_partner h hux
  obtain ⟨y', hpy, -⟩ := exists_unique_partner h huy
  have hxy' : x ≠ y' := by rintro rfl; exact hxy hpy.2.2.symm
  have hx'y : x' ≠ y := by rintro rfl; exact hxy hpx.2.2
  have hx'y' : x' ≠ y' := by rintro rfl; exact hxyne (partner_injective h hpx hpy)
  obtain ⟨hnxy, hnxy'⟩ := not_adj_of_ne_class h hpy hux hxyne hxy'
  obtain ⟨hnx'y, hnx'y'⟩ := not_adj_of_ne_class h hpy hpx.2.1 hx'y hx'y'
  obtain ⟨z₁, hz₁⟩ := exists_label h hux huy hnxy hxyne
  obtain ⟨z₂, hz₂⟩ := exists_label h hux hpy.2.1 hnxy' hxy'
  obtain ⟨z₃, hz₃⟩ := exists_label h hpx.2.1 huy hnx'y hx'y
  obtain ⟨z₄, hz₄⟩ := exists_label h hpx.2.1 hpy.2.1 hnx'y' hx'y'
  refine ⟨gridPt u y y' x z₁ z₂ x' z₃ z₄,
    grid_of_canonical h hcan hpx hpy hxyne hxy' hx'y hx'y' hz₁ hz₂ hz₃ hz₄, ?_, ?_, ?_⟩ <;>
    simp [gridPt]

/-- **THE FAR CORNER OF A GRID'S CORNER PAIR IS THE OPPOSITE CORNER.**  In a
grid, the far corner of `{pt 1 0, pt 0 1}` computed at the corner `pt 0 0` is
`pt 2 2` — the two apexes are pinned by λ = 1 and the corner by μ = 2.  (This
is STEP 2 of `far_corner_well_defined`, extracted so the block calculus can
reuse it.) -/
theorem grid_far_corner_eq (h : G.IsSRGWith n k 1 2) {pt : Fin 3 → Fin 3 → V}
    (hgrid : IsGrid G pt) {F : V}
    (hF : IsFarCorner G (pt 0 0) (pt 1 0) (pt 0 1) F) : F = pt 2 2 := by
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  have d20 : (2 : Fin 3) ≠ 0 := by decide
  have hu_x : G.Adj (pt 0 0) (pt 1 0) := hgrid.col 0 1 0 d01
  have hu_y : G.Adj (pt 0 0) (pt 0 1) := hgrid.row 0 0 1 d01
  obtain ⟨p, q, hp, hq, hpF, hqF, hFne⟩ := hF
  have hp_eq : p = pt 2 0 :=
    apex_unique h hp ⟨hu_x, hgrid.col 0 2 0 d02, hgrid.col 1 2 0 d12⟩
  have hq_eq : q = pt 0 2 :=
    apex_unique h hq ⟨hu_y, hgrid.row 0 0 2 d02, hgrid.row 0 1 2 d12⟩
  subst hp_eq; subst hq_eq
  have hnadj1 : ¬ G.Adj (pt 2 0) (pt 0 2) := hgrid.off 2 0 0 2 d20 d02
  have hne1 : pt 2 0 ≠ pt 0 2 := fun he => d20 (hgrid.inj 2 0 0 2 he).1
  rcases two_common h hne1 hnadj1
      (hgrid.col 2 0 0 d20) (hgrid.row 0 2 0 d20)
      (hgrid.row 2 0 2 d02) (hgrid.col 0 2 2 d02) hpF hqF with hc | hc | hc
  · exact absurd (hgrid.inj 0 0 2 2 hc).1 d02
  · exact absurd hc.symm hFne
  · exact hc.symm

/-- **EVERY "BROKEN DIAGONAL" OF A GRID IS A DIAGONAL BLOCK.**  Pick one point
from each row, in three distinct columns; the three points are pairwise
non-adjacent and the third is the far corner of the first two, computed at
`pt 0 c₁`.  (With `(c₀,c₁,c₂) = (0,1,2)` this is the main diagonal; the six
column patterns give the six diagonals of the plane.)  Needs NO SRG axioms —
it is a fact about the grid. -/
theorem grid_isDiagonal {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) {c₀ c₁ c₂ : Fin 3}
    (h₀₁ : c₀ ≠ c₁) (h₀₂ : c₀ ≠ c₂) (h₁₂ : c₁ ≠ c₂) :
    IsDiagonal G (pt 0 c₀) (pt 1 c₁) (pt 2 c₂) := by
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  have d20 : (2 : Fin 3) ≠ 0 := by decide
  refine ⟨fun he => d01 (hgrid.inj 0 c₀ 1 c₁ he).1,
    hgrid.off 0 c₀ 1 c₁ d01 h₀₁, pt 0 c₁, pt 0 c₂, pt 2 c₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hgrid.row 0 c₁ c₀ h₀₁.symm, hgrid.row 0 c₁ c₂ h₁₂, hgrid.row 0 c₀ c₂ h₀₂⟩
  · exact ⟨hgrid.col 0 1 c₁ d01, hgrid.col 0 2 c₁ d02, hgrid.col 1 2 c₁ d12⟩
  · exact hgrid.col 0 2 c₂ d02
  · exact hgrid.row 2 c₁ c₂ h₁₂
  · exact fun he => d20 (hgrid.inj 2 c₂ 0 c₁ he).1

/-- **TOTAL SYMMETRY OF THE STEINER OPERATION** — `x ∘ (x ∘ y) = y`, in
relational form: if `F` is the third point of the block through `{x,y}`, then
`y` is the third point of the block through `{x,F}`.  Hence any two of a
block's three points determine it, and the block is a well-defined 3-SET.

Proof: place the configuration in the grid at the anchor `u`
(`exists_grid_of_canonical`); then `F = pt 2 2` (`grid_far_corner_eq`), and
`y = pt 0 1` is visibly the far corner of `{pt 1 0, pt 2 2}` computed at
`pt 2 0`, with apexes `pt 0 0` and `pt 2 1`. -/
theorem IsDiagonal.rotate (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {x y F : V} (hd : IsDiagonal G x y F) : IsDiagonal G x F y := by
  obtain ⟨hne, hnadj, u, hFar⟩ := hd
  obtain ⟨p, q, hp, hq, hpF, hqF, hFu⟩ := hFar
  obtain ⟨pt, hgrid, e00, e10, e01⟩ :=
    exists_grid_of_canonical h (hcan u) hp.1 hq.1 hnadj hne
  subst e00; subst e10; subst e01
  have hFeq : F = pt 2 2 := grid_far_corner_eq h hgrid ⟨p, q, hp, hq, hpF, hqF, hFu⟩
  subst hFeq
  have E : ∀ i j i' j' : Fin 3, i ≠ i' → pt i j ≠ pt i' j' :=
    fun i j i' j' hii he => hii (hgrid.inj i j i' j' he).1
  exact ⟨E 1 0 2 2 (by decide), hgrid.off 1 0 2 2 (by decide) (by decide),
    pt 2 0, pt 0 0, pt 2 1,
    ⟨hgrid.col 2 1 0 (by decide), hgrid.col 2 0 0 (by decide),
      hgrid.col 1 0 0 (by decide)⟩,
    ⟨hgrid.row 2 0 2 (by decide), hgrid.row 2 0 1 (by decide),
      hgrid.row 2 2 1 (by decide)⟩,
    hgrid.row 0 0 1 (by decide), hgrid.col 2 0 1 (by decide),
    E 0 1 2 0 (by decide)⟩

/-- **THE DIAGONAL BLOCK THROUGH A NON-ADJACENT PAIR IS UNIQUE** — this IS
far-corner well-definedness, in block form.  If the two far corners are
computed at the same common neighbour, `far_corner_unique` (μ = 2) settles it;
if at the two different ones, `far_corner_well_defined_of_canonical` does. -/
theorem diagonal_unique (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {x y F F' : V} (hd : IsDiagonal G x y F) (hd' : IsDiagonal G x y F') :
    F = F' := by
  obtain ⟨hne, hnadj, u, hF⟩ := hd
  obtain ⟨-, -, u', hF'⟩ := hd'
  by_cases hu : u' = u
  · subst hu; exact far_corner_unique h hnadj hne hF hF'
  · exact far_corner_well_defined_of_canonical h (hcan u) hF.adj_left hF.adj_right
      hnadj hne hu hF'.adj_left.symm hF'.adj_right.symm hF hF'

/-! #### Which pair of a block is which: the six forms of a block -/

/-- Two distinct points of a LINE are adjacent. -/
theorem adj_of_mem_line {a b c : V} (hL : IsLine G a b c) {p q : V}
    (hp : p ∈ ({a, b, c} : Finset V)) (hq : q ∈ ({a, b, c} : Finset V))
    (hpq : p ≠ q) : G.Adj p q := by
  obtain ⟨hab, hac, hbc⟩ := hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact hab
  · exact hac
  · exact hab.symm
  · exact absurd rfl hpq
  · exact hbc
  · exact hac.symm
  · exact hbc.symm
  · exact absurd rfl hpq

/-- **AN ADJACENT PAIR LIES IN NO DIAGONAL BLOCK** (λ = 1 only): two distinct
points of a diagonal block are non-adjacent. -/
theorem not_adj_of_mem_diagonal (h : G.IsSRGWith n k 1 μ) {x y F : V}
    (hd : IsDiagonal G x y F) {p q : V}
    (hp : p ∈ ({x, y, F} : Finset V)) (hq : q ∈ ({x, y, F} : Finset V))
    (hpq : p ≠ q) : ¬ G.Adj p q := by
  obtain ⟨-, hxy, hxF, hyF⟩ := hd.pairwise h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact hxy
  · exact hxF
  · exact fun ha => hxy ha.symm
  · exact absurd rfl hpq
  · exact hyF
  · exact fun ha => hxF ha.symm
  · exact fun ha => hyF ha.symm
  · exact absurd rfl hpq

/-- A line is determined by ANY two of its points: the remaining point is the
third point of the line through them. -/
theorem line_pair_form {a b c : V} (hL : IsLine G a b c) {p q : V}
    (hp : p ∈ ({a, b, c} : Finset V)) (hq : q ∈ ({a, b, c} : Finset V))
    (hpq : p ≠ q) : ∃ r, IsLine G p q r ∧ ({a, b, c} : Finset V) = {p, q, r} := by
  obtain ⟨hab, hac, hbc⟩ := hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact ⟨c, ⟨hab, hac, hbc⟩, rfl⟩
  · exact ⟨b, ⟨hac, hab, hbc.symm⟩, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨c, ⟨hab.symm, hbc, hac⟩, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd rfl hpq
  · exact ⟨a, ⟨hbc, hab.symm, hac.symm⟩, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨b, ⟨hac.symm, hbc.symm, hab⟩, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨a, ⟨hbc.symm, hac.symm, hab.symm⟩, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd rfl hpq

/-- A diagonal block is determined by ANY two of its points — the six forms of
`IsDiagonal.symm` and `IsDiagonal.rotate`.  This is the statement that makes
the block set a set of unordered TRIPLES. -/
theorem diagonal_pair_form (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {x y F : V} (hd : IsDiagonal G x y F) {p q : V}
    (hp : p ∈ ({x, y, F} : Finset V)) (hq : q ∈ ({x, y, F} : Finset V))
    (hpq : p ≠ q) :
    ∃ r, IsDiagonal G p q r ∧ ({x, y, F} : Finset V) = {p, q, r} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact ⟨F, hd, rfl⟩
  · exact ⟨y, hd.rotate h hcan, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨F, hd.symm, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd rfl hpq
  · exact ⟨x, (hd.symm).rotate h hcan, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨y, (hd.rotate h hcan).symm, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨x, ((hd.symm).rotate h hcan).symm, by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact absurd rfl hpq

/-- **EVERY BLOCK HAS EXACTLY THREE POINTS** (λ = 1 only) — the design is
3-uniform, which is the other half of "Steiner TRIPLE system".  A line's three
points are pairwise adjacent hence distinct; a diagonal's are pairwise
non-adjacent and distinct by `IsDiagonal.pairwise`. -/
theorem block_card (h : G.IsSRGWith n k 1 μ) {B : Finset V} (hB : IsBlock G B) :
    B.card = 3 := by
  rcases hB with ⟨p, q, r, hL, rfl⟩ | ⟨x, y, F, hd, rfl⟩
  · have h1 : p ≠ q := hL.1.ne
    have h2 : p ≠ r := hL.2.1.ne
    have h3 : q ≠ r := hL.2.2.ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]
  · obtain ⟨⟨e1, e2, e3⟩, -⟩ := hd.pairwise h
    rw [Finset.card_insert_of_notMem (by simp [e1, e2]),
      Finset.card_insert_of_notMem (by simp [e3]), Finset.card_singleton]

/-- **EVERY DIAGONAL BLOCK IS A DIAGONAL OF A PLANE** — the other half of the
note's description of the block set ("the lines of `Γ` together with the six
diagonals of each plane"): a diagonal block through `x ≁ y` sits in the grid
built at either of their common neighbours, as the pair of points adjacent to
the corner together with the opposite corner. -/
theorem IsDiagonal.in_plane (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {x y F : V} (hd : IsDiagonal G x y F) :
    ∃ pt : Fin 3 → Fin 3 → V, IsGrid G pt ∧ pt 1 0 = x ∧ pt 0 1 = y ∧ pt 2 2 = F := by
  obtain ⟨hne, hnadj, u, hFar⟩ := hd
  obtain ⟨pt, hgrid, e00, e10, e01⟩ :=
    exists_grid_of_canonical h (hcan u) hFar.adj_left hFar.adj_right hnadj hne
  exact ⟨pt, hgrid, e10, e01,
    (grid_far_corner_eq h hgrid (by rw [e00, e10, e01]; exact hFar)).symm⟩

/-- **THE SHAPE OF A BLOCK THROUGH A GIVEN PAIR.**  Any block containing two
distinct points `p ≠ q` is `{p, q, r}`, and its type is forced by the
adjacency of the pair: a LINE if `p ~ q`, a DIAGONAL if `p ≁ q`.  The two
kinds of block therefore never compete for the same pair. -/
theorem block_pair_form (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {B : Finset V} (hB : IsBlock G B) {p q : V} (hp : p ∈ B) (hq : q ∈ B)
    (hpq : p ≠ q) :
    ∃ r, ((G.Adj p q ∧ IsLine G p q r) ∨ (¬ G.Adj p q ∧ IsDiagonal G p q r)) ∧
      B = {p, q, r} := by
  rcases hB with ⟨a, b, c, hL, rfl⟩ | ⟨x, y, F, hd, rfl⟩
  · obtain ⟨r, hLr, he⟩ := line_pair_form hL hp hq hpq
    exact ⟨r, Or.inl ⟨hLr.1, hLr⟩, he⟩
  · obtain ⟨r, hdr, he⟩ := diagonal_pair_form h hcan hd hp hq hpq
    exact ⟨r, Or.inr ⟨hdr.2.1, hdr⟩, he⟩

/-- **THE STS EXACT-COVER PROPERTY — `hall-analogue.md` Theorem 2's defining
property, machine-checked.**

Let `Γ` be an srg(v,k,1,2) that is canonical at every vertex.  Then every pair
of distinct points lies in **exactly one** block of
`B = {lines} ∪ {{x,y,x∘y} : x ≁ y}`.

Existence: `exists_apex` (λ = 1) for an adjacent pair, `exists_unique_far_corner`
(μ = 2) for a non-adjacent one.  Uniqueness: `block_pair_form` reduces any
block through the pair to `{p,q,r}` of the type forced by the adjacency, and
then `apex_unique` (λ = 1) resp. `diagonal_unique` (far-corner
well-definedness) identifies the third point.

Together with `sts_blocks_per_point` — `r` lines plus `2·C(r,2)` diagonals
`= r²` blocks per point, the count an STS(v) demands — this is the Steiner
completion of the note, no longer a markdown claim. -/
theorem sts_exact_cover (h : G.IsSRGWith n k 1 2) (hcan : Canonical G) {p q : V}
    (hpq : p ≠ q) : ∃! B : Finset V, IsBlock G B ∧ p ∈ B ∧ q ∈ B := by
  obtain ⟨B, hB, hpB, hqB⟩ : ∃ B : Finset V, IsBlock G B ∧ p ∈ B ∧ q ∈ B := by
    by_cases hadj : G.Adj p q
    · obtain ⟨t, ht, -⟩ := exists_apex h hadj
      exact ⟨{p, q, t}, Or.inl ⟨p, q, t, ht, rfl⟩, by simp, by simp⟩
    · have hpos : 0 < Fintype.card (G.commonNeighbors p q) := by
        rw [h.of_not_adj hpq hadj]; norm_num
      obtain ⟨⟨u, hu⟩⟩ := Fintype.card_pos_iff.mp hpos
      rw [mem_commonNeighbors] at hu
      obtain ⟨F, hF, -⟩ := exists_unique_far_corner h hu.1.symm hu.2.symm hadj hpq
      exact ⟨{p, q, F}, Or.inr ⟨p, q, F, ⟨hpq, hadj, u, hF⟩, rfl⟩, by simp, by simp⟩
  refine ⟨B, ⟨hB, hpB, hqB⟩, ?_⟩
  rintro C ⟨hC, hpC, hqC⟩
  obtain ⟨r, hr, rfl⟩ := block_pair_form h hcan hC hpC hqC hpq
  obtain ⟨r', hr', rfl⟩ := block_pair_form h hcan hB hpB hqB hpq
  rcases hr with ⟨hadj, hL⟩ | ⟨hnadj, hD⟩ <;> rcases hr' with ⟨hadj', hL'⟩ | ⟨hnadj', hD'⟩
  · rw [apex_unique h (⟨hL.1, hL.2.1, hL.2.2⟩ : IsApex G p q r)
      (⟨hL'.1, hL'.2.1, hL'.2.2⟩ : IsApex G p q r')]
  · exact absurd hadj hnadj'
  · exact absurd hadj' hnadj
  · rw [diagonal_unique h hcan hD hD']

/-! ### C4b — each plane carries 12 blocks: the AG(2,3) subsystem

`hall-analogue.md` Theorem 2's last clause: each plane is an AG(2,3)
subsystem of the completion.  What is proved here:

  * a plane's twelve blocks are its **6 graph lines** (3 rows + 3 columns of
    the grid) and its **6 diagonals** (one point per row, in three distinct
    columns) — `plane_blocks_are`, `plane_blocks_isBlock`;
  * there are exactly **12** of them, i.e. those twelve subsets are distinct
    — `plane_blocks_card`;
  * the twelve are an EXACT COVER of the plane's `C(9,2) = 36` point pairs —
    `ag23_exact_cover` at the index level, by `decide`;
  * the plane is CLOSED: the block of the whole design through any two of its
    points is one of those twelve — `plane_blocks_closed`.  This is the
    subsystem statement, and it is what makes the AG(2,3) identification more
    than a coincidence of counts.

WHAT IS *NOT* PROVED: that this subsystem is isomorphic, as a design, to
`AG(2,3)` over `GF(3)` — there is no Lean model of `AG(2,3)` here, only the
concrete 12-block index design `ag23` on `Fin 3 × Fin 3` (which IS the affine
plane's block set, written out).  Read the identification as "carries the
12-block design `ag23`", which is what the four theorems say.
-/

/-- The twelve blocks of the affine plane of order 3 on the index set
`Fin 3 × Fin 3`: three rows, three columns, and the six broken diagonals (one
point per row, in three distinct columns).  Kept at the index level so that
the design facts are `decide`-able once and for all. -/
def ag23 : Finset (Finset (Fin 3 × Fin 3)) :=
  {{(0,0),(0,1),(0,2)}, {(1,0),(1,1),(1,2)}, {(2,0),(2,1),(2,2)},
   {(0,0),(1,0),(2,0)}, {(0,1),(1,1),(2,1)}, {(0,2),(1,2),(2,2)},
   {(0,0),(1,1),(2,2)}, {(0,1),(1,2),(2,0)}, {(0,2),(1,0),(2,1)},
   {(0,0),(1,2),(2,1)}, {(0,1),(1,0),(2,2)}, {(0,2),(1,1),(2,0)}}

set_option maxRecDepth 100000 in
/-- Twelve blocks — in particular the twelve listed sets are distinct. -/
theorem ag23_card : ag23.card = 12 := by decide

set_option maxRecDepth 100000 in
/-- Each is a 3-set. -/
theorem ag23_block_card : ∀ B ∈ ag23, B.card = 3 := by decide

set_option maxRecDepth 400000 in
/-- **THE 12 BLOCKS COVER EACH OF THE 36 POINT PAIRS EXACTLY ONCE** — the
AG(2,3) exact-cover property, by `decide` over the 81 ordered pairs. -/
theorem ag23_exact_cover : ∀ P Q : Fin 3 × Fin 3, P ≠ Q →
    (ag23.filter (fun B => P ∈ B ∧ Q ∈ B)).card = 1 := by decide

/-- The existence half of `ag23_exact_cover`, in usable form. -/
theorem ag23_mem_of_ne {P Q : Fin 3 × Fin 3} (hPQ : P ≠ Q) :
    ∃ C ∈ ag23, P ∈ C ∧ Q ∈ C := by
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp (ag23_exact_cover P Q hPQ)
  have hmem : C ∈ ag23.filter (fun B => P ∈ B ∧ Q ∈ B) := by
    rw [hC]; exact Finset.mem_singleton_self C
  rw [Finset.mem_filter] at hmem
  exact ⟨C, hmem.1, hmem.2⟩

/-- The twelve blocks of the plane spanned by a grid, as subsets of `V`. -/
def planeBlocks (pt : Fin 3 → Fin 3 → V) : Finset (Finset V) :=
  ag23.image (fun C => C.image (fun P => pt P.1 P.2))

/-- **6 LINES AND 6 DIAGONALS.**  The three rows and three columns of a grid
are graph LINES; each of the six ways of choosing one point per row in three
distinct columns is a DIAGONAL block.  (No SRG axioms: this is grid geometry
plus `grid_isDiagonal`.) -/
theorem plane_blocks_are {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) :
    (∀ i : Fin 3, IsLine G (pt i 0) (pt i 1) (pt i 2)) ∧
      (∀ j : Fin 3, IsLine G (pt 0 j) (pt 1 j) (pt 2 j)) ∧
      (∀ c₀ c₁ c₂ : Fin 3, c₀ ≠ c₁ → c₀ ≠ c₂ → c₁ ≠ c₂ →
        IsDiagonal G (pt 0 c₀) (pt 1 c₁) (pt 2 c₂)) :=
  ⟨fun i => ⟨hgrid.row i 0 1 (by decide), hgrid.row i 0 2 (by decide),
      hgrid.row i 1 2 (by decide)⟩,
   fun j => ⟨hgrid.col 0 1 j (by decide), hgrid.col 0 2 j (by decide),
      hgrid.col 1 2 j (by decide)⟩,
   fun _ _ _ h₀₁ h₀₂ h₁₂ => grid_isDiagonal hgrid h₀₁ h₀₂ h₁₂⟩

/-- **EVERY ONE OF THE TWELVE IS A BLOCK OF THE DESIGN** — six by the line
clause, six by the diagonal clause. -/
theorem plane_blocks_isBlock {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) :
    ∀ B ∈ planeBlocks pt, IsBlock G B := by
  intro B hB
  simp only [planeBlocks, Finset.mem_image] at hB
  obtain ⟨C, hC, rfl⟩ := hB
  simp only [ag23, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl ⟨pt 0 0, pt 0 1, pt 0 2, ⟨hgrid.row 0 0 1 (by decide),
      hgrid.row 0 0 2 (by decide), hgrid.row 0 1 2 (by decide)⟩, by simp⟩
  · exact Or.inl ⟨pt 1 0, pt 1 1, pt 1 2, ⟨hgrid.row 1 0 1 (by decide),
      hgrid.row 1 0 2 (by decide), hgrid.row 1 1 2 (by decide)⟩, by simp⟩
  · exact Or.inl ⟨pt 2 0, pt 2 1, pt 2 2, ⟨hgrid.row 2 0 1 (by decide),
      hgrid.row 2 0 2 (by decide), hgrid.row 2 1 2 (by decide)⟩, by simp⟩
  · exact Or.inl ⟨pt 0 0, pt 1 0, pt 2 0, ⟨hgrid.col 0 1 0 (by decide),
      hgrid.col 0 2 0 (by decide), hgrid.col 1 2 0 (by decide)⟩, by simp⟩
  · exact Or.inl ⟨pt 0 1, pt 1 1, pt 2 1, ⟨hgrid.col 0 1 1 (by decide),
      hgrid.col 0 2 1 (by decide), hgrid.col 1 2 1 (by decide)⟩, by simp⟩
  · exact Or.inl ⟨pt 0 2, pt 1 2, pt 2 2, ⟨hgrid.col 0 1 2 (by decide),
      hgrid.col 0 2 2 (by decide), hgrid.col 1 2 2 (by decide)⟩, by simp⟩
  · exact Or.inr ⟨pt 0 0, pt 1 1, pt 2 2,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩
  · exact Or.inr ⟨pt 0 1, pt 1 2, pt 2 0,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩
  · exact Or.inr ⟨pt 0 2, pt 1 0, pt 2 1,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩
  · exact Or.inr ⟨pt 0 0, pt 1 2, pt 2 1,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩
  · exact Or.inr ⟨pt 0 1, pt 1 0, pt 2 2,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩
  · exact Or.inr ⟨pt 0 2, pt 1 1, pt 2 0,
      grid_isDiagonal hgrid (by decide) (by decide) (by decide), by simp⟩

set_option maxRecDepth 100000 in
/-- **TWELVE DISTINCT BLOCKS** — the grid's nine points are distinct, so the
twelve index blocks have twelve distinct images. -/
theorem plane_blocks_card {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) :
    (planeBlocks pt).card = 12 := by
  have hf : Function.Injective (fun P : Fin 3 × Fin 3 => pt P.1 P.2) := by
    intro P Q he
    obtain ⟨h1, h2⟩ := hgrid.inj P.1 P.2 Q.1 Q.2 he
    exact Prod.ext h1 h2
  rw [planeBlocks, Finset.card_image_of_injective _ (Finset.image_injective hf)]
  decide

/-- **THE PLANE IS A SUBSYSTEM.**  The block of the WHOLE design through any
two distinct points of a plane is one of that plane's twelve blocks — so the
plane is closed under the Steiner operation, and its induced design is
exactly `ag23`.  (This is where `sts_exact_cover`'s uniqueness does the
work.) -/
theorem plane_blocks_closed (h : G.IsSRGWith n k 1 2) (hcan : Canonical G)
    {pt : Fin 3 → Fin 3 → V} (hgrid : IsGrid G pt) {P Q : Fin 3 × Fin 3}
    (hPQ : P ≠ Q) {B : Finset V} (hB : IsBlock G B) (hPB : pt P.1 P.2 ∈ B)
    (hQB : pt Q.1 Q.2 ∈ B) : B ∈ planeBlocks pt := by
  obtain ⟨C, hC, hPC, hQC⟩ := ag23_mem_of_ne hPQ
  have hne : pt P.1 P.2 ≠ pt Q.1 Q.2 := by
    intro he
    obtain ⟨h1, h2⟩ := hgrid.inj P.1 P.2 Q.1 Q.2 he
    exact hPQ (Prod.ext h1 h2)
  have hIm : C.image (fun R : Fin 3 × Fin 3 => pt R.1 R.2) ∈ planeBlocks pt :=
    Finset.mem_image_of_mem _ hC
  obtain ⟨B', -, huniq⟩ := sts_exact_cover h hcan hne
  have e1 : B = B' := huniq B ⟨hB, hPB, hQB⟩
  have e2 : C.image (fun R : Fin 3 × Fin 3 => pt R.1 R.2) = B' :=
    huniq _ ⟨plane_blocks_isBlock hgrid _ hIm,
      Finset.mem_image_of_mem _ hPC, Finset.mem_image_of_mem _ hQC⟩
  rw [e1, ← e2]; exact hIm

/-! ### C4c — the counting identity of the Steiner completion

`hall-analogue.md` Theorem 2 completes the graph's partial "third point"
operation to a Steiner triple system whose blocks are the graph lines
together with the six diagonals of each plane.  The reason the completion
works with **no slack and no overlap** is the identity below: at each point
the graph supplies `r` lines and the planes supply exactly the missing
`2·C(r,2) = r(r−1)` diagonals, totalling `r² = (v−1)/2` blocks — precisely
the number of blocks through a point of an STS(v).
-/

/-- `2·C(n,2) = n(n−1)` in ℕ (no division). -/
theorem two_choose_two (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => decide
  | succ p ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel, Nat.mul_add,
      ih]
    cases p with
    | zero => decide
    | succ s =>
      simp only [Nat.add_sub_cancel]
      ring

/-- **C4, the per-point count**: `r` graph lines `+` `2·C(r,2)` plane
diagonals `=` `r²` blocks.  (v = 99: 7 + 42 = 49; v = 243: 11 + 110 = 121.) -/
theorem sts_blocks_per_point (r : ℕ) : r + 2 * Nat.choose r 2 = r * r := by
  rw [two_choose_two]
  cases r with
  | zero => decide
  | succ s => simp only [Nat.add_sub_cancel]; ring

/-- **C4, the global count**, stated multiplicatively to stay in ℕ.  With
`v = 1 + 2r²`: the `v·r/3` lines plus the `6·v·C(r,2)/9` diagonals give
`v·r²/3 = v(v−1)/6` blocks.  Multiplying through by 3 and by 6
respectively, this is the pair of identities below.  Note `v − 1 = 2r²` is
what makes the two agree — the parameter relation of the λ=1, μ=2 family. -/
theorem sts_block_count (r : ℕ) :
    (1 + 2 * r ^ 2) * r + (1 + 2 * r ^ 2) * (2 * Nat.choose r 2)
        = (1 + 2 * r ^ 2) * (r * r) ∧
      (1 + 2 * r ^ 2) * (1 + 2 * r ^ 2 - 1) = 2 * ((1 + 2 * r ^ 2) * (r * r)) := by
  constructor
  · rw [← Nat.mul_add, sts_blocks_per_point]
  · have h1 : 1 + 2 * r ^ 2 - 1 = 2 * (r * r) := by
      have : r ^ 2 = r * r := by ring
      omega
    rw [h1]; ring

/-- The v = 99 and v = 243 instances of the per-point count. -/
theorem sts_blocks_99_243 :
    7 + 2 * Nat.choose 7 2 = 49 ∧ 11 + 2 * Nat.choose 11 2 = 121 := by
  refine ⟨by decide, by decide⟩

/-! ### C5 — the exact size of the Hall gap -/

/-- **THE 6/(r(r+1)) COUNT** — log 035's NEW RESULT 2, exactly.

Through a point of the completed STS there are `r²` blocks, hence
`C(r²,2)` pairs of blocks, each of which Hall's condition requires to
generate an AG(2,3) subsystem.  Canonicality supplies the `C(r,2)` GRID
planes through the point, and each grid plane, having `4` blocks through the
point, certifies `C(4,2) = 6` of those pairs.  The certified fraction is
therefore

  `6·C(r,2) / C(r²,2) = 6 / (r(r+1))`,

which the statement below records as the cross-multiplied ℕ identity.  Since
the right-hand side tends to 0, **the gap is structural, not
effort-limited**. -/
theorem hall_fraction (r : ℕ) :
    6 * Nat.choose r 2 * (r * (r + 1)) = 6 * Nat.choose (r ^ 2) 2 := by
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  have h1 : 2 * (6 * Nat.choose r 2 * (r * (r + 1)))
      = 6 * (r * (r - 1)) * (r * (r + 1)) := by
    rw [← two_choose_two r]; ring
  have h2 : 2 * (6 * Nat.choose (r ^ 2) 2) = 6 * (r ^ 2 * (r ^ 2 - 1)) := by
    rw [← two_choose_two (r ^ 2)]; ring
  rw [h1, h2]
  cases r with
  | zero => decide
  | succ s =>
    have e1 : s + 1 - 1 = s := by omega
    have e2 : (s + 1) ^ 2 - 1 = s * s + 2 * s := by
      have : (s + 1) ^ 2 = s * s + 2 * s + 1 := by ring
      omega
    rw [e1, e2]
    ring

/-- The certified fraction at the three orders that matter: `6/(r(r+1))` is
`126/1176` at v = 99 (`r = 7`) and `330/7260` at v = 243 (`r = 11`) — the
figures the note and log 035 quote. -/
theorem hall_fraction_99_243 :
    6 * Nat.choose 7 2 = 126 ∧ Nat.choose (7 ^ 2) 2 = 1176 ∧
      6 * Nat.choose 11 2 = 330 ∧ Nat.choose (11 ^ 2) 2 = 7260 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### C6 — the Diophantine side

TWO STATEMENTS AT DIFFERENT STRENGTHS, and it matters which one is quoted.

**(i) WHAT THE APPLICATION NEEDS — proved here FOR ALL `n`, no bound.**  The
Hall route's conclusion is `v = 3ⁿ`; to kill the three open orders of the
parameter family one only needs that `99`, `6273` and `494019` are *not*
powers of 3.  That is elementary and unbounded, and it is proved here TWICE
by independent routes:

  * `not_pow_three_of_between` — a number strictly between two consecutive
    powers of 3 is not a power of 3 (monotonicity of `3ⁿ`);
  * `not_pow_three_of_not_dvd` — `3ᵃ·b` with `b > 1` and `3 ∤ b` is not a
    power of 3 (induction on `a`, cancelling one factor 3 at a time).

`family_not_power_of_three` is the headline: `∀ n`, none of the three is
`3ⁿ`.  `family_not_power_of_three_dvd` re-derives it from the factorisations
`99 = 3²·11`, `6273 = 3²·17·41`, `494019 = 3⁵·19·107`, which
`family_factorisations` *verifies* rather than asserts.

**(ii) THE GENERAL DIOPHANTINE IS NOT PROVED HERE.**
`diophantine_finite_check` / `diophantine_of_exp_le` are a FINITE
VERIFICATION by `decide` over `n ≤ 12`, `r ≤ 520` — a computation, not a
proof of `1 + 2r² = 3ⁿ ⇒ r ∈ {0,1,2,11}`.  The general statement is
Ramanujan–Nagell-type (the classical route factors
`3ⁿ = (1 + r√−2)(1 − r√−2)` in `ℤ[√−2]` and needs a primitive-divisor
argument); it is CITED in lean/README.md, not ours.  **Nothing in this
project depends on it**: every use goes through (i), which is unbounded.
-/

/-- **UNBOUNDED, ROUTE 1 — bracketing.**  If `m` is strictly between two
consecutive powers of 3 then `m` is not a power of 3, for EVERY exponent. -/
theorem not_pow_three_of_between {m a : ℕ} (h1 : 3 ^ a < m) (h2 : m < 3 ^ (a + 1))
    (n : ℕ) : m ≠ 3 ^ n := by
  intro he
  subst he
  by_cases hn : n ≤ a
  · exact absurd h1 (Nat.not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hn))
  · have hn' : a + 1 ≤ n := by omega
    exact absurd h2 (Nat.not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hn'))

/-- **UNBOUNDED, ROUTE 2 — divisibility.**  `3ᵃ·b` with `b > 1` prime to 3 is
never a power of 3.  Induction on `a`, cancelling one factor 3 per step; the
base case is "`b` is a power of 3 and `3 ∤ b`, so `b = 1`". -/
theorem not_pow_three_of_not_dvd {b : ℕ} (hb : 1 < b) (hnd : ¬ (3 ∣ b)) :
    ∀ a n : ℕ, 3 ^ a * b ≠ 3 ^ n := by
  intro a
  induction a with
  | zero =>
    intro n he
    rw [pow_zero, one_mul] at he
    cases n with
    | zero => rw [pow_zero] at he; omega
    | succ m => exact hnd ⟨3 ^ m, by rw [he, pow_succ]; ring⟩
  | succ p ih =>
    intro n he
    cases n with
    | zero =>
      rw [pow_zero] at he
      have hdvd : b ∣ 1 := ⟨3 ^ (p + 1), by rw [mul_comm]; exact he.symm⟩
      have := Nat.dvd_one.mp hdvd
      omega
    | succ m =>
      refine ih m (Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num) ?_)
      have hs : (3 : ℕ) ^ p * 3 * b = 3 ^ m * 3 := by
        rw [← pow_succ, ← pow_succ]; exact he
      calc (3 : ℕ) * (3 ^ p * b) = 3 ^ p * 3 * b := by ring
        _ = 3 ^ m * 3 := hs
        _ = 3 * 3 ^ m := by ring

/-- The factorisations the divisibility route uses, **verified, not trusted**:
`99 = 3²·11`, `6273 = 3²·17·41`, `494019 = 3⁵·19·107`, and in each case the
cofactor is prime to 3. -/
theorem family_factorisations :
    (99 : ℕ) = 3 ^ 2 * 11 ∧ (6273 : ℕ) = 3 ^ 2 * (17 * 41) ∧
      (494019 : ℕ) = 3 ^ 5 * (19 * 107) ∧
      ¬ ((3 : ℕ) ∣ 11) ∧ ¬ ((3 : ℕ) ∣ 17 * 41) ∧ ¬ ((3 : ℕ) ∣ 19 * 107) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **THE STATEMENT THE APPLICATION USES — TRUE FOR ALL `n`.**  None of `99`,
`6273`, `494019` is a power of 3.  So a proof that a λ=1, μ=2 graph must have
3-power order would eliminate all three open orders of the family at once —
the reason the Hall route was worth chasing.  No bound on `n`: proved by
bracketing, `3⁴ < 99 < 3⁵`, `3⁷ < 6273 < 3⁸`, `3¹¹ < 494019 < 3¹²`. -/
theorem family_not_power_of_three :
    (∀ n, (99 : ℕ) ≠ 3 ^ n) ∧ (∀ n, (6273 : ℕ) ≠ 3 ^ n) ∧
      (∀ n, (494019 : ℕ) ≠ 3 ^ n) :=
  ⟨not_pow_three_of_between (a := 4) (by norm_num) (by norm_num),
   not_pow_three_of_between (a := 7) (by norm_num) (by norm_num),
   not_pow_three_of_between (a := 11) (by norm_num) (by norm_num)⟩

/-- The same three facts by the INDEPENDENT divisibility route, from the
verified factorisations.  (Two proofs of the load-bearing statement, since
this is the one the Hall route would consume.) -/
theorem family_not_power_of_three_dvd :
    (∀ n, (99 : ℕ) ≠ 3 ^ n) ∧ (∀ n, (6273 : ℕ) ≠ 3 ^ n) ∧
      (∀ n, (494019 : ℕ) ≠ 3 ^ n) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · simpa using not_pow_three_of_not_dvd (b := 11) (by norm_num) (by norm_num) 2 n
  · simpa using not_pow_three_of_not_dvd (b := 697) (by norm_num) (by norm_num) 2 n
  · simpa using not_pow_three_of_not_dvd (b := 2033) (by norm_num) (by norm_num) 5 n

/-- Non-vacuity of the previous theorem: the OTHER two members of the family
ARE powers of 3, so `family_not_power_of_three` is a real separation and not
a fact about every integer. -/
theorem family_powers_of_three : (9 : ℕ) = 3 ^ 2 ∧ (243 : ℕ) = 3 ^ 5 := by
  refine ⟨by norm_num, by norm_num⟩

set_option maxRecDepth 100000 in
/-- **A FINITE VERIFICATION, NOT A THEOREM ABOUT ALL `n`.**  Checked by
`decide`: no `r ≤ 520` with `n ≤ 12` other than `r ∈ {0,1,2,11}` satisfies
`1 + 2r² = 3ⁿ`.  Quote it as a computation over an explicit finite range —
the same discipline as `C3.lean`'s `c3_trace_core`.  The general Diophantine
statement is CITED, not proved (see the section header and lean/README.md). -/
theorem diophantine_finite_check :
    ∀ r ≤ 520, ∀ n ≤ 12, 1 + 2 * r ^ 2 = 3 ^ n →
      r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 11 := by decide

/-- **THE DIOPHANTINE CONDITION for n ≤ 12** — the `r`-bound of
`diophantine_finite_check` is not a restriction, because `n ≤ 12` already
forces `r ≤ 520`.  So: if a λ=1, μ=2 parameter set `v = 1 + 2r²` is a power
of 3 at most `3¹² = 531,441`, then `v ∈ {1, 3, 9, 243}`.  **Still bounded** —
for the application use `family_not_power_of_three`, which is not. -/
theorem diophantine_of_exp_le {r n : ℕ} (hn : n ≤ 12) (heq : 1 + 2 * r ^ 2 = 3 ^ n) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 11 := by
  have h3 : (3 : ℕ) ^ n ≤ 3 ^ 12 := Nat.pow_le_pow_right (by norm_num) hn
  have hle : 1 + 2 * r ^ 2 ≤ 531441 := by
    rw [heq]; simpa using h3
  have hr : r ≤ 520 := by nlinarith [sq_nonneg r]
  exact diophantine_finite_check r hr n hn heq

/-! ### NON-VACUITY — Paley(9)

Everything above is stated with `IsSRGWith`, `CanonicalAt`, `IsGrid` and
`IsFarCorner` as hypotheses.  This section shows they are simultaneously
satisfiable, so none of the theorems is vacuous: Paley(9) = the 3×3 rook's
graph is an srg(9,4,1,2), it carries a grid, and it is canonical at a root.
(Log 034 records that canonicality at v = 9 is automatic — `B_a` is a
2-set — which is exactly why this witness is cheap.  It is a witness for the
HYPOTHESES, not evidence for anything at v = 99.)
-/

/-- Paley(9) = srg(9,4,1,2) = the 3×3 rook's graph. -/
def paley9 : SimpleGraph (Fin 3 × Fin 3) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)
  symm := ⟨by rintro p q ⟨h1, h2⟩; exact ⟨h1.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel paley9.Adj := fun p q =>
  inferInstanceAs (Decidable (p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)))

set_option maxRecDepth 100000 in
/-- Paley(9) really is an srg(9,4,1,2) — checked by `decide`. -/
theorem paley9_srg : paley9.IsSRGWith 9 4 1 2 where
  card := by decide
  regular := by
    unfold SimpleGraph.IsRegularOfDegree
    decide
  of_adj := by decide
  of_not_adj := by
    have hall : ∀ v w : Fin 3 × Fin 3, v ≠ w → ¬ paley9.Adj v w →
        Fintype.card (paley9.commonNeighbors v w) = 2 := by decide
    exact fun v w => hall v w

/-- Paley(9) carries a grid — the coordinate one.  Hence `IsGrid` is
satisfiable, and `far_corner_well_defined` is not vacuous. -/
theorem paley9_isGrid : IsGrid paley9 (fun i j => (i, j)) where
  inj := by decide
  row := by decide
  col := by decide
  off := by decide

set_option maxRecDepth 100000 in
/-- Paley(9) is canonical at the origin — hence `CanonicalAt` is satisfiable.
-/
theorem paley9_canonicalAt : CanonicalAt paley9 (0, 0) := by
  unfold CanonicalAt IsPartner IsLabel
  decide

/-- **THE PREMISES FIRE.**  `CanonicalAt` is a ∀-implication, so
`paley9_canonicalAt` on its own would also hold if `IsPartner`/`IsLabel` were
never satisfiable.  They are: here is a concrete matched pair `{(0,1),(0,2)}`
of `N((0,0))`, a concrete `a = (1,0)` outside it, the two label vertices
`z_ab = (1,1)` and `z_ab′ = (1,2)`, and the adjacency the definition demands.
So `CanonicalAt paley9 (0,0)` is a non-vacuous statement, and `IsPartner`,
`IsLabel` are inhabited. -/
theorem paley9_canonical_premises_fire :
    paley9.Adj ((0 : Fin 3), (0 : Fin 3)) (1, 0) ∧
      IsPartner paley9 (0, 0) (0, 1) (0, 2) ∧
      IsLabel paley9 (0, 0) (1, 0) (0, 1) (1, 1) ∧
      IsLabel paley9 (0, 0) (1, 0) (0, 2) (1, 2) ∧
      paley9.Adj ((1 : Fin 3), (1 : Fin 3)) (1, 2) :=
  ⟨by decide,
   ⟨by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   by decide⟩

/-- **`grid_of_canonical` IS APPLICABLE** — the strongest non-vacuity check
available here: every one of its ten hypotheses holds simultaneously in
Paley(9), and the grid it then produces is the coordinate grid.  (A theorem
whose hypotheses were jointly unsatisfiable could not be applied at all.) -/
theorem paley9_grid_of_canonical :
    IsGrid paley9 (gridPt ((0 : Fin 3), (0 : Fin 3)) (0, 1) (0, 2)
      (1, 0) (1, 1) (1, 2) (2, 0) (2, 1) (2, 2)) :=
  grid_of_canonical paley9_srg paley9_canonicalAt
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩

/-- `IsFarCorner` is inhabited: in Paley(9) the far corner of the non-adjacent
pair `{(1,0), (0,1)}` computed at their common neighbour `(0,0)` is `(2,2)` —
the apexes being `(2,0)` and `(0,2)`.  So `far_corner_unique`,
`far_corner_well_defined` and `exists_unique_far_corner` are not vacuous. -/
theorem paley9_farCorner :
    IsFarCorner paley9 ((0 : Fin 3), (0 : Fin 3)) (1, 0) (0, 1) (2, 2) :=
  ⟨(2, 0), (0, 2), ⟨by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- Translation by any vector is an automorphism of Paley(9) — by `decide`
over the 729 triples `(v,p,q)`.  (Cheap; the point of doing it this way is
that lifting `paley9_canonicalAt` through `CanonicalAt.transfer` costs
seconds, whereas deciding `Canonical paley9` directly ranges over `9⁶`
tuples and costs minutes.) -/
theorem paley9_translate_adj : ∀ v p q : Fin 3 × Fin 3,
    paley9.Adj (p + v) (q + v) ↔ paley9.Adj p q := by decide

/-- **`Canonical` IS SATISFIABLE**: Paley(9) is canonical at EVERY vertex, by
translating `paley9_canonicalAt` with `CanonicalAt.transfer`.  This is the
hypothesis of `sts_exact_cover`, so the exact-cover theorem is not vacuous. -/
theorem paley9_canonical : Canonical paley9 := by
  intro v
  have e : (Equiv.addRight v) ((0 : Fin 3), (0 : Fin 3)) = v := by
    simp [Prod.ext_iff]
  have h := paley9_canonicalAt.transfer (Equiv.addRight v)
    (fun p q => paley9_translate_adj v p q)
  rwa [e] at h

/-- `IsDiagonal` is inhabited: the main diagonal of Paley(9)'s coordinate
grid is a diagonal block. -/
theorem paley9_isDiagonal :
    IsDiagonal paley9 ((0 : Fin 3), (0 : Fin 3)) (1, 1) (2, 2) :=
  grid_isDiagonal paley9_isGrid (by decide) (by decide) (by decide)

/-- **BOTH KINDS OF BLOCK OCCUR** — so `IsBlock` is not secretly one-sided:
a row of the rook's graph is a line block, the main diagonal is a diagonal
block. -/
theorem paley9_blocks_both_kinds :
    IsBlock paley9 {((0 : Fin 3), (0 : Fin 3)), (0, 1), (0, 2)} ∧
      IsBlock paley9 {((0 : Fin 3), (0 : Fin 3)), (1, 1), (2, 2)} :=
  ⟨Or.inl ⟨(0, 0), (0, 1), (0, 2), ⟨by decide, by decide, by decide⟩, rfl⟩,
   Or.inr ⟨(0, 0), (1, 1), (2, 2), paley9_isDiagonal, rfl⟩⟩

/-- **`sts_exact_cover` APPLIED** — the strongest non-vacuity check available:
all of its hypotheses hold simultaneously in Paley(9), so every pair of its
distinct points lies in exactly one block.  (At v = 9 the whole graph is a
single plane, so this instance is also `plane_blocks_closed`'s extreme
case.) -/
theorem paley9_sts_exact_cover {p q : Fin 3 × Fin 3} (hpq : p ≠ q) :
    ∃! B : Finset (Fin 3 × Fin 3), IsBlock paley9 B ∧ p ∈ B ∧ q ∈ B :=
  sts_exact_cover paley9_srg paley9_canonical hpq

/-- Paley(9)'s coordinate grid carries twelve blocks — the whole STS(9). -/
theorem paley9_planeBlocks_card :
    (planeBlocks (fun i j => ((i, j) : Fin 3 × Fin 3))).card = 12 :=
  plane_blocks_card paley9_isGrid

end Conway99
