/-
Conway99.C3Wlog — the two relabeling WLOGs of the C3 D-cycle cube campaign
(WLOG-C, WLOG-D of notes/c3-dcycle-design.md sections 3-4), machine-checked
in the `relabel_to_canonicalC3` mold, plus the centralizer machinery they
ride on.  Design inputs: src/c3_instance.py (--canon-d), src/c3_cubes.py
(the 50 (t, L) cubes), notes/c3-dcycle-design.md.

WHAT IS PROVED HERE, sorry-free (no literature input anywhere in this file):

  A. CENTRALIZER ACTION.  `orbitPermLift π` is the lift of an orbit
     permutation `π : Perm (Fin 33)` to `Fin 99` — `3i+a ↦ 3π(i)+a` in the
     `orbitEquiv` coordinates (`orbitPermLift_apply` / `orbitPermLift_val`).
     It CENTRALIZES the canonical order-3 element g = `canonicalC3`
     (`orbitPermLift_comm_canonicalC3`, `orbitPermLift_mul_canonicalC3`),
     its action on orbit indices is exactly π (`orbitPermLift_orbit`), and
     lifting is multiplicative (`orbitPermLift_mul`).  Consequence: the
     relabeled graph `G.map (orbitPermLift π)` of a g-invariant G is again
     g-invariant (`map_invariant_of_conj`), isomorphic to G (`mapPermIso`),
     and its orbit-blocks are the π-permuted orbit-blocks of G
     (`orbitPermLift_map_adj` — the bridge along which EVERY orbit-level
     derived structure, d-pattern and D-graph included, transports by π).

  B. WLOG-C (d-canonicalization; soundness of --canon-d):
     `exists_perm_image_eq_topBlock` — any T ⊆ Fin 33 with |T| = t ≤ 33 is
     carried onto the top block {33−t, …, 32} (`topBlock t`,
     `card_topBlock`) by some π ∈ S₃₃; campaign corollary
     `relabel_to_canonical_d` — any g-invariant graph on Fin 99 with
     triangle-orbit set T is isomorphic, via the centralizing relabeling
     `orbitPermLift π`, to a g-invariant graph whose triangle-orbit set is
     EXACTLY `topBlock t` (the 33 canon-d units of c3_instance.py).

  C. WLOG-D (cycle canonicalization; soundness of the (t, L) cube form):
     `exists_perm_canonical_cycle` — given any graph D on Fin 33 and an
     injective enumeration c : Fin L → Fin 33 of a closed walk avoiding the
     top block (consecutive vertices D-adjacent, Fin-L addition supplying
     the wrap — exactly what D8's cycle-through-orbit-0 provides), some
     π ∈ S₃₃ fixes `topBlock t` POINTWISE (stronger than the design's
     setwise requirement) and relabels the cycle to (0, 1, …, L−1): the
     relabeled D has all L canonical edges {s, s+1} and the wrap {0, L−1}
     — the w2 cube units of c3_cubes.py.  Campaign corollary
     `relabel_to_canonical_cycle` — the lift of that π to Fin 99 preserves
     g-invariance AND the canonical d-pattern while putting the D-cycle in
     canonical position.  The workhorse `exists_perm_comp_eq_of_notMem`
     (any two injective enumerations avoiding a frozen block are related
     by a permutation fixing the block pointwise) is deliberately general:
     level-2 sub-splits (freeze `topBlock t ∪ {0..L−1}`, canonicalize the
     next cycle to {L..L+L₂−1}) instantiate the SAME lemma.

  D. Bonus closure of lean/README.md informal item 4(b):
     `relabel_graph_to_canonicalC3` — the graph-level C3 conjugacy WLOG:
     a graph with a fixed-point-free order-3 automorphism σ is isomorphic
     to a `canonicalC3`-invariant graph, srg parameters transported
     (composes `relabel_to_canonicalC3`, `mapPermIso`,
     `map_invariant_of_conj` and WLOG.lean's `isSRGWith_of_iso`; the
     formerly-informal one-liner is now a theorem).

WHAT IS **NOT** IN THIS FILE (stays on the disclosed semantic links of the
c3_cubes.py soundness chain): the spectral trace input (t-slices, C3.lean
hypothesis form), E1–E4 enrichment equisatisfiability (dossier arithmetic
D5–D6), and D8 (a 2-regular graph decomposes into cycles of length ≥ 3
with well-defined cycle-through-orbit-0 — the supplier of `c` above).
-/
import Mathlib
import Conway99.C3
import Conway99.WLOG

namespace Conway99

/-! ### A. The centralizer action: lifting orbit permutations to `Fin 99` -/

/-- The lift of an orbit permutation `π : Perm (Fin 33)` to `Fin 99`:
in `orbitEquiv` coordinates, `(i, a) ↦ (π i, a)`, i.e. vertex
`3i+a ↦ 3π(i)+a` — whole g-orbits move by π, offsets stay put.  This is
the centralizer element used by WLOG-C and WLOG-D of
notes/c3-dcycle-design.md §4. -/
def orbitPermLift (π : Equiv.Perm (Fin 33)) : Equiv.Perm (Fin 99) :=
  orbitEquiv.permCongr (π.prodCongr (Equiv.refl (Fin 3)))

/-- `orbitPermLift` in orbit coordinates: `(i, a) ↦ (π i, a)`. -/
theorem orbitPermLift_apply (π : Equiv.Perm (Fin 33)) (i : Fin 33) (a : Fin 3) :
    orbitPermLift π (orbitEquiv (i, a)) = orbitEquiv (π i, a) := by
  simp [orbitPermLift]

/-- `orbitPermLift` numerically: vertex `3i+a` goes to `3π(i)+a`. -/
theorem orbitPermLift_val (π : Equiv.Perm (Fin 33)) (i : Fin 33) (a : Fin 3) :
    (orbitPermLift π (orbitEquiv (i, a)) : ℕ) = 3 * (π i : ℕ) + (a : ℕ) := by
  rw [orbitPermLift_apply, orbitEquiv_val]

/-- Lifting is multiplicative: the map `π ↦ orbitPermLift π` is a group
homomorphism S₃₃ → S₉₉ (so composed WLOG relabelings are again lifts). -/
theorem orbitPermLift_mul (π π' : Equiv.Perm (Fin 33)) :
    orbitPermLift (π * π') = orbitPermLift π * orbitPermLift π' := by
  ext v
  obtain ⟨⟨i, a⟩, rfl⟩ := orbitEquiv.surjective v
  simp only [Equiv.Perm.mul_apply, orbitPermLift_apply]

/-- CENTRALIZER, pointwise form: `orbitPermLift π` commutes with the
canonical order-3 element g — g shifts offsets inside orbits, the lift
permutes whole orbits. -/
theorem orbitPermLift_comm_canonicalC3 (π : Equiv.Perm (Fin 33)) (v : Fin 99) :
    orbitPermLift π (canonicalC3 v) = canonicalC3 (orbitPermLift π v) := by
  obtain ⟨⟨i, a⟩, rfl⟩ := orbitEquiv.surjective v
  rw [canonicalC3_orbit_apply, orbitPermLift_apply, orbitPermLift_apply,
    canonicalC3_orbit_apply]

/-- CENTRALIZER, group form: `orbitPermLift π * canonicalC3 =
canonicalC3 * orbitPermLift π`. -/
theorem orbitPermLift_mul_canonicalC3 (π : Equiv.Perm (Fin 33)) :
    orbitPermLift π * canonicalC3 = canonicalC3 * orbitPermLift π := by
  ext v
  simp only [Equiv.Perm.mul_apply, orbitPermLift_comm_canonicalC3]

/-- The induced action of `orbitPermLift π` on orbit indices is exactly π:
the lift permutes orbit-level structure precisely as π permutes `Fin 33`. -/
theorem orbitPermLift_orbit (π : Equiv.Perm (Fin 33)) (v : Fin 99) :
    (orbitEquiv.symm (orbitPermLift π v)).1 = π (orbitEquiv.symm v).1 := by
  obtain ⟨⟨i, a⟩, rfl⟩ := orbitEquiv.surjective v
  rw [orbitPermLift_apply]
  simp

/-! ### Graph relabeling transport (generic, any vertex type) -/

/-- Adjacency of a permutation-relabeled graph on relabeled vertices,
coercion-friendly form of `SimpleGraph.map_adj_apply`. -/
theorem map_perm_adj {V : Type*} (G : SimpleGraph V) (p : Equiv.Perm V) (a b : V) :
    (G.map p.toEmbedding).Adj (p a) (p b) ↔ G.Adj a b := by
  simpa using SimpleGraph.map_adj_apply (G := G) (f := p.toEmbedding) (a := a) (b := b)

/-- Relabeling a graph along a permutation of its vertices yields an
isomorphic graph (conjugation IS relabeling). -/
def mapPermIso {V : Type*} (p : Equiv.Perm V) (G : SimpleGraph V) :
    G ≃g G.map p.toEmbedding where
  toEquiv := p
  map_rel_iff' := by
    intro a b
    exact map_perm_adj G p a b

/-- Invariance transport: if `G` is σ-invariant and the relabeling `p`
conjugates σ to `g` (`p ∘ σ = g ∘ p`), then the relabeled graph
`G.map p` is g-invariant.  This is the graph-level glue of every
conjugacy/centralizer WLOG in this development. -/
theorem map_invariant_of_conj {V : Type*} {G : SimpleGraph V} {p σ g : Equiv.Perm V}
    (hσ : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v))
    (hpg : ∀ v, p (σ v) = g (p v)) (u v : V) :
    (G.map p.toEmbedding).Adj u v ↔ (G.map p.toEmbedding).Adj (g u) (g v) := by
  obtain ⟨u', rfl⟩ := p.surjective u
  obtain ⟨v', rfl⟩ := p.surjective v
  rw [map_perm_adj, ← hpg u', ← hpg v', map_perm_adj]
  exact hσ u' v'

/-- Adjacency in a graph mapped along an embedding is decidable when the
domain is a finite decidable type (search the finitely many preimages). -/
instance mapAdjDecidable {V W : Type*} [Fintype V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V ↪ W) :
    DecidableRel (G.map f).Adj := fun u v =>
  decidable_of_iff' _ (SimpleGraph.map_adj f G u v)

/-- Graph-level C3 conjugacy WLOG (closes lean/README.md informal item
4(b)): every srg(99,14,1,2) on `Fin 99` admitting a fixed-point-free
order-3 automorphism σ is isomorphic — by the relabeling `p` of
`relabel_to_canonicalC3` — to a `canonicalC3`-invariant srg(99,14,1,2).
Prescribing the canonical g, as `src/c3_instance.py` does, loses no
models.  (That an order-3 automorphism of a Conway graph IS
fixed-point-free is Behbahani–Lam 2011; as everywhere in C3.lean it
enters only as the hypothesis `hfpf`.) -/
theorem relabel_graph_to_canonicalC3 (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin 99)) (h3 : orderOf σ = 3) (hfpf : ∀ v, σ v ≠ v)
    (hσ : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) (hsrg : G.IsSRGWith 99 14 1 2) :
    ∃ p : Equiv.Perm (Fin 99),
      (G.map p.toEmbedding).IsSRGWith 99 14 1 2 ∧
      ∀ u v, (G.map p.toEmbedding).Adj u v ↔
        (G.map p.toEmbedding).Adj (canonicalC3 u) (canonicalC3 v) := by
  obtain ⟨p, hp⟩ := relabel_to_canonicalC3 σ h3 hfpf
  exact ⟨p, isSRGWith_of_iso (mapPermIso p G) hsrg,
    fun u v => map_invariant_of_conj hσ hp u v⟩

/-! ### Orbit-block transport and the triangle-orbit indicator -/

/-- BLOCK TRANSPORT: relabeling by `orbitPermLift π` carries the
orbit-block `(i, j)` of `G` to the orbit-block `(π i, π j)` of the
relabeled graph, offsets untouched.  Every orbit-level derived structure
— the d-pattern, the block cardinalities |S_ij|, hence the D-graph of
notes/c3-dcycle-design.md — therefore transports along π. -/
theorem orbitPermLift_map_adj (π : Equiv.Perm (Fin 33)) (G : SimpleGraph (Fin 99))
    (i j : Fin 33) (a b : Fin 3) :
    (G.map (orbitPermLift π).toEmbedding).Adj (orbitEquiv (π i, a)) (orbitEquiv (π j, b)) ↔
      G.Adj (orbitEquiv (i, a)) (orbitEquiv (j, b)) := by
  rw [← orbitPermLift_apply, ← orbitPermLift_apply, map_perm_adj]

/-- Orbit `i` carries a triangle: its first two vertices `3i` and `3i+1`
are adjacent.  For a g-invariant graph this single adjacency makes the
whole orbit a K₃, matching the encoder's diagonal bit `d_i`
(`src/c3_instance.py` `adj_lit`). -/
def orbitIsTriangle (G : SimpleGraph (Fin 99)) (i : Fin 33) : Prop :=
  G.Adj (orbitEquiv (i, 0)) (orbitEquiv (i, 1))

/-- The triangle-orbit indicator transports along `orbitPermLift π` by π. -/
theorem orbitIsTriangle_map (π : Equiv.Perm (Fin 33)) (G : SimpleGraph (Fin 99))
    (i : Fin 33) :
    orbitIsTriangle (G.map (orbitPermLift π).toEmbedding) (π i) ↔ orbitIsTriangle G i :=
  orbitPermLift_map_adj π G i i 0 1

/-! ### The finite-combinatorics workhorse -/

/-- WORKHORSE (absolute form): any two injective enumerations `f, g` of a
type β inside a finite type α are related by a permutation of α with
`π ∘ f = g` — the symmetric group acts transitively on injections. -/
theorem exists_perm_comp_eq {α β : Type*} [Finite α] [Finite β]
    {f g : β → α} (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ π : Equiv.Perm α, ∀ b, π (f b) = g b := by
  classical
  cases nonempty_fintype α
  cases nonempty_fintype β
  have hcompl :
      Fintype.card {x // ¬x ∈ Set.range f} = Fintype.card {x // ¬x ∈ Set.range g} := by
    have h1 : Fintype.card {x // x ∈ Set.range f} = Fintype.card β :=
      Fintype.card_congr (Equiv.ofInjective f hf).symm
    have h2 : Fintype.card {x // x ∈ Set.range g} = Fintype.card β :=
      Fintype.card_congr (Equiv.ofInjective g hg).symm
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1, h2]
  refine ⟨((Equiv.sumCompl (· ∈ Set.range f)).symm.trans
    (((((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).sumCongr
      (Fintype.equivOfCardEq hcompl)).trans
      (Equiv.sumCompl (· ∈ Set.range g))))), fun b => ?_⟩
  have hmem : f b ∈ Set.range f := Set.mem_range_self b
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hmem,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  have hb : (Equiv.ofInjective f hf).symm ⟨f b, hmem⟩ = b :=
    hf (Equiv.apply_ofInjective_symm hf ⟨f b, hmem⟩)
  rw [hb]
  rfl

/-- WORKHORSE (relative form): if both enumerations avoid a frozen block
`F`, the permutation can be chosen to fix `F` POINTWISE.  This is the
reusable core of WLOG-D at every cube level: level 1 freezes the triangle
block, level 2 freezes triangle block + first canonical cycle, etc. -/
theorem exists_perm_comp_eq_of_notMem {α β : Type*} [Finite α] [Finite β]
    (F : Finset α) {f g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfF : ∀ b, f b ∉ F) (hgF : ∀ b, g b ∉ F) :
    ∃ π : Equiv.Perm α, (∀ a ∈ F, π a = a) ∧ ∀ b, π (f b) = g b := by
  classical
  have hf' : Function.Injective fun b => (⟨f b, hfF b⟩ : {a : α // a ∉ F}) :=
    fun b₁ b₂ h => hf (congrArg Subtype.val h)
  have hg' : Function.Injective fun b => (⟨g b, hgF b⟩ : {a : α // a ∉ F}) :=
    fun b₁ b₂ h => hg (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq hf' hg'
  refine ⟨σ.extendDomain (Equiv.refl {a : α // a ∉ F}), fun a ha => ?_, fun b => ?_⟩
  · exact Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl _) (not_not_intro ha)
  · rw [Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl _) (hfF b)]
    simpa using congrArg Subtype.val (hσ b)

/-- A permutation fixing a finite set pointwise preserves membership in it
both ways. -/
theorem perm_fixed_mem_iff {α : Type*} {π : Equiv.Perm α} {F : Finset α}
    (hfix : ∀ a ∈ F, π a = a) (i : α) : π i ∈ F ↔ i ∈ F := by
  constructor
  · intro h
    have h2 : π i = i := π.injective (hfix (π i) h)
    rwa [← h2]
  · intro h
    rwa [hfix i h]

/-! ### B. WLOG-C: d-canonicalization -/

/-- The top-`t` block `{33−t, …, 32}` of `Fin 33` — the canonical position
of the `t` triangle orbits (`c3_instance.py --canon-d`: `+d_i` exactly on
this block). -/
def topBlock (t : ℕ) : Finset (Fin 33) :=
  Finset.univ.filter fun i : Fin 33 => 33 - t ≤ (i : ℕ)

/-- Membership in the top block. -/
theorem mem_topBlock {t : ℕ} {i : Fin 33} : i ∈ topBlock t ↔ 33 - t ≤ (i : ℕ) := by
  simp [topBlock]

/-- The top-`t` block has exactly `t` elements (for `t ≤ 33`). -/
theorem card_topBlock {t : ℕ} (ht : t ≤ 33) : (topBlock t).card = t := by
  refine Finset.card_eq_of_bijective
    (fun i hi => (⟨33 - t + i, by omega⟩ : Fin 33)) ?_ ?_ ?_
  · intro a ha
    rw [mem_topBlock] at ha
    have hlt := a.isLt
    refine ⟨(a : ℕ) - (33 - t), by omega, ?_⟩
    apply Fin.ext
    change 33 - t + ((a : ℕ) - (33 - t)) = (a : ℕ)
    omega
  · intro i hi
    rw [mem_topBlock]
    change 33 - t ≤ 33 - t + i
    omega
  · intro i j hi hj h
    have h' : 33 - t + i = 33 - t + j := congrArg Fin.val h
    omega

/-- WLOG-C, permutation level: any `T ⊆ Fin 33` with `|T| = t ≤ 33` is
carried onto the top-`t` block by some permutation — `π(T) = topBlock t`,
with the two-way membership correspondence. -/
theorem exists_perm_image_eq_topBlock {t : ℕ} (ht : t ≤ 33) (T : Finset (Fin 33))
    (hT : T.card = t) :
    ∃ π : Equiv.Perm (Fin 33),
      T.image π = topBlock t ∧ ∀ i, π i ∈ topBlock t ↔ i ∈ T := by
  classical
  have hcard : Fintype.card {i // i ∈ T} = Fintype.card {i // i ∈ topBlock t} := by
    rw [Fintype.card_coe, Fintype.card_coe, hT, card_topBlock ht]
  let e : {i // i ∈ T} ≃ {i // i ∈ topBlock t} := Fintype.equivOfCardEq hcard
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq
    (f := fun x : {i // i ∈ T} => (x : Fin 33))
    (g := fun x : {i // i ∈ T} => (e x : Fin 33))
    Subtype.coe_injective (Subtype.coe_injective.comp e.injective)
  have hmapsto : ∀ i, i ∈ T → π i ∈ topBlock t := fun i hi => by
    have h : π i = ↑(e ⟨i, hi⟩) := hπ ⟨i, hi⟩
    rw [h]
    exact (e ⟨i, hi⟩).2
  have himg : T.image π = topBlock t := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hmapsto i hi
    · exact le_of_eq
        (by rw [Finset.card_image_of_injective _ π.injective, hT, card_topBlock ht])
  refine ⟨π, himg, fun i => ⟨fun h => ?_, hmapsto i⟩⟩
  rw [← himg] at h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
  rwa [← π.injective hji]

/-- WLOG-C, campaign form (soundness of `c3_instance.py --canon-d`): any
`canonicalC3`-invariant graph on `Fin 99` whose triangle-orbit set is `T`
with `|T| = t ≤ 33` relabels — by the centralizing lift `orbitPermLift π`
— to an ISOMORPHIC, still-g-invariant graph whose triangle-orbit set is
exactly the top-`t` block.  The 33 canon-d unit clauses therefore lose no
g-invariant models. -/
theorem relabel_to_canonical_d {t : ℕ} (ht : t ≤ 33) (G : SimpleGraph (Fin 99))
    (hinv : ∀ u v, G.Adj u v ↔ G.Adj (canonicalC3 u) (canonicalC3 v))
    (T : Finset (Fin 33)) (hTcard : T.card = t)
    (hT : ∀ i, orbitIsTriangle G i ↔ i ∈ T) :
    ∃ π : Equiv.Perm (Fin 33),
      (∀ v, orbitPermLift π (canonicalC3 v) = canonicalC3 (orbitPermLift π v)) ∧
      Nonempty (G ≃g G.map (orbitPermLift π).toEmbedding) ∧
      (∀ u v, (G.map (orbitPermLift π).toEmbedding).Adj u v ↔
        (G.map (orbitPermLift π).toEmbedding).Adj (canonicalC3 u) (canonicalC3 v)) ∧
      (∀ i, orbitIsTriangle (G.map (orbitPermLift π).toEmbedding) i ↔
        i ∈ topBlock t) := by
  obtain ⟨π, _, hπ⟩ := exists_perm_image_eq_topBlock ht T hTcard
  refine ⟨π, orbitPermLift_comm_canonicalC3 π, ⟨mapPermIso _ G⟩,
    map_invariant_of_conj hinv (orbitPermLift_comm_canonicalC3 π), fun i => ?_⟩
  obtain ⟨i', rfl⟩ := π.surjective i
  rw [orbitIsTriangle_map, hT i']
  exact (hπ i').symm

/-! ### C. WLOG-D: canonicalizing the D-cycle through the low block -/

/-- WLOG-D, core form (soundness of the `(t, L)` cube units of
`src/c3_cubes.py`): let `D` be any graph on `Fin 33` (in the campaign: the
2-regular `|S_ij| = 2` relation on nontriangle orbits) and
`c : Fin L → Fin 33` an injective enumeration avoiding the top-`t` block
whose consecutive vertices are D-adjacent — `Fin L` addition makes
`c (L−1) — c 0` the wrap edge, so `c` enumerates a closed cycle, exactly
what D8 supplies for the cycle through orbit 0.  Then some `π ∈ S₃₃`

  * fixes the top-`t` block POINTWISE (design §4 asks only setwise),
  * relabels the cycle to canonical position: `π (c s) = s`, and
  * gives the relabeled D-graph all `L` canonical cycle edges
    `{s, s+1}` for `s < L−1` plus the wrap `{0, L−1}` — the positive
    w2 unit clauses of cube `(t, L)`.

The remainder of D is confined to `{L, …, 32−t}` by the E3 exactly-2 rows
at the CNF level (unit propagation), not here. -/
theorem exists_perm_canonical_cycle {t L : ℕ} [NeZero L]
    (hLn : L ≤ 33 - t) (h33 : L ≤ 33)
    (D : SimpleGraph (Fin 33)) (c : Fin L → Fin 33)
    (hcinj : Function.Injective c)
    (hlow : ∀ s, c s ∉ topBlock t)
    (hadj : ∀ s : Fin L, D.Adj (c s) (c (s + 1))) :
    ∃ π : Equiv.Perm (Fin 33),
      (∀ i ∈ topBlock t, π i = i) ∧
      (∀ s : Fin L, π (c s) = Fin.castLE h33 s) ∧
      (∀ s : Fin L, (D.map π.toEmbedding).Adj (Fin.castLE h33 s)
        (Fin.castLE h33 (s + 1))) := by
  classical
  have heF : ∀ s : Fin L, Fin.castLE h33 s ∉ topBlock t := by
    intro s
    rw [mem_topBlock]
    simp only [Fin.val_castLE]
    have hs := s.isLt
    omega
  obtain ⟨π, hfix, hπ⟩ := exists_perm_comp_eq_of_notMem (topBlock t)
    hcinj (Fin.castLE_injective h33) hlow heF
  refine ⟨π, hfix, hπ, fun s => ?_⟩
  rw [← hπ s, ← hπ (s + 1), map_perm_adj]
  exact hadj s

/-- A relabeling that fixes the top block pointwise preserves the
canonical d-pattern: if `G`'s triangle orbits are exactly `topBlock t`,
so are those of `G.map (orbitPermLift π)`. -/
theorem orbitIsTriangle_map_of_fixed {t : ℕ} {π : Equiv.Perm (Fin 33)}
    (G : SimpleGraph (Fin 99)) (hfix : ∀ i ∈ topBlock t, π i = i)
    (hG : ∀ i, orbitIsTriangle G i ↔ i ∈ topBlock t) (i : Fin 33) :
    orbitIsTriangle (G.map (orbitPermLift π).toEmbedding) i ↔ i ∈ topBlock t := by
  obtain ⟨i', rfl⟩ := π.surjective i
  rw [orbitIsTriangle_map, hG i']
  exact (perm_fixed_mem_iff hfix i').symm

/-- WLOG-D, campaign form: a `canonicalC3`-invariant graph on `Fin 99`
with canonical d-pattern, whose (abstract) D-graph has a cycle enumerated
by `c` on the nontriangle block, relabels — by the centralizing lift
`orbitPermLift π` of the cycle-canonicalizing π — to an ISOMORPHIC,
still-g-invariant graph with the SAME canonical d-pattern whose D-graph
carries the canonical cycle `(0, 1, …, L−1)` with wrap edge `{0, L−1}`.
The final clause is the block-transport bridge: the relabeled graph's
orbit-blocks are the π-moved orbit-blocks of `G`, so its counting-derived
D-graph is exactly `D.map π` (the identification of D with the
`|S_ij| = 2` relation is the E3 clause layer, outside this file). -/
theorem relabel_to_canonical_cycle {t L : ℕ} [NeZero L]
    (hLn : L ≤ 33 - t) (h33 : L ≤ 33)
    (G : SimpleGraph (Fin 99))
    (hinv : ∀ u v, G.Adj u v ↔ G.Adj (canonicalC3 u) (canonicalC3 v))
    (hd : ∀ i, orbitIsTriangle G i ↔ i ∈ topBlock t)
    (D : SimpleGraph (Fin 33)) (c : Fin L → Fin 33)
    (hcinj : Function.Injective c) (hlow : ∀ s, c s ∉ topBlock t)
    (hadj : ∀ s : Fin L, D.Adj (c s) (c (s + 1))) :
    ∃ π : Equiv.Perm (Fin 33),
      (∀ v, orbitPermLift π (canonicalC3 v) = canonicalC3 (orbitPermLift π v)) ∧
      Nonempty (G ≃g G.map (orbitPermLift π).toEmbedding) ∧
      (∀ u v, (G.map (orbitPermLift π).toEmbedding).Adj u v ↔
        (G.map (orbitPermLift π).toEmbedding).Adj (canonicalC3 u) (canonicalC3 v)) ∧
      (∀ i, orbitIsTriangle (G.map (orbitPermLift π).toEmbedding) i ↔
        i ∈ topBlock t) ∧
      (∀ s : Fin L, (D.map π.toEmbedding).Adj (Fin.castLE h33 s)
        (Fin.castLE h33 (s + 1))) ∧
      (∀ (i j : Fin 33) (a b : Fin 3),
        (G.map (orbitPermLift π).toEmbedding).Adj
          (orbitEquiv (π i, a)) (orbitEquiv (π j, b)) ↔
          G.Adj (orbitEquiv (i, a)) (orbitEquiv (j, b))) := by
  obtain ⟨π, hfix, _, hcyc⟩ := exists_perm_canonical_cycle hLn h33 D c hcinj hlow hadj
  exact ⟨π, orbitPermLift_comm_canonicalC3 π, ⟨mapPermIso _ G⟩,
    map_invariant_of_conj hinv (orbitPermLift_comm_canonicalC3 π),
    orbitIsTriangle_map_of_fixed G hfix hd, hcyc,
    fun i j a b => orbitPermLift_map_adj π G i j a b⟩

end Conway99
