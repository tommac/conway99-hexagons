/-
Conway99.Dirac — the Dirac-type perfect matching lemma, formalized.

CONTEXT.  "A graph on an EVEN number of vertices whose minimum degree is at
least half the vertex count has a perfect matching" is the matching shadow of
Dirac's 1952 Hamiltonicity theorem.  It is a standard textbook fact, but it is
used here as a *tool* rather than quoted, so it is proved outright: nothing in
this file is a literature input, and nothing in it is specific to the Conway
problem.

WHAT IS PROVED, AND IN WHICH ORDER.  The sharp form is
`not_isTutteViolator_of_card_eq_two_mul`: for a graph on `2 * m` vertices with
minimum degree `≥ m`, NO vertex set is a Tutte violator.  Mathlib's
`SimpleGraph.tutte` then converts that into the headline
`exists_perfectMatching_of_card_eq_two_mul` and its stated-with-`Even` form
`exists_perfectMatching_of_card_le_two_mul_degree`.  The generic parameter `m`
is carried throughout; the concrete `14`/`7` instance is a convenience
corollary at the bottom that NOTHING in this project consumes — `Alpha22.lean`,
the one caller, goes through the generic `2 * m` form.

NON-VACUITY.  `C4` (the 4-cycle, realised as "different parity" on `Fin 4`)
satisfies the hypotheses TIGHTLY — four vertices, every degree exactly two —
and `C4_exists_perfectMatching` runs the theorem on it.  `C4_hypotheses` records
the hypotheses as a single `decide`-checked conjunction, so the hypothesis set
is visibly satisfiable and the sharpness of `card ≤ 2 * degree` is visible too
(`C4_degree_eq`).

THE ARGUMENT (Route A: discharge Tutte's condition directly).  Write `n = 2m`
for the vertex count, `δ ≥ m` for the minimum degree, `t = |u|` for the size of
the candidate violator, and let `K` be `G` with `u` deleted.

  1. SIZE LEMMA (`hsize` in the proof).  Every connected component of `K` has
     at least `δ - t + 1 ≥ m - t + 1` vertices: a vertex `v` of the component
     keeps all of its `≥ δ - t` neighbours that avoid `u`, and those all lie in
     `v`'s own component, as does `v` itself.  (Stated subtraction-free as
     `m + 1 ≤ |component| + t`.)
  2. `t = 0`.  Components have `≥ m+1` vertices and `K` has `2m` of them, so
     `K` has at most ONE component and hence at most one odd component.  But
     the number of odd components has the parity of the vertex count
     (`SimpleGraph.odd_ncard_oddComponents`), which is even.  So there are
     none, and `0 < #odd` is contradicted.
  3. `1 ≤ t ≤ m`.  If `t` were a violator there would be `≥ t+1` odd
     components, so `(t+1)(m-t+1) ≤ 2m-t`.  Writing `t = a+1`, `m = a+1+s`
     this reads `(a+2)(s+1) ≤ a+1+2s`, i.e. `a·s + 2 ≤ 1`.  Contradiction.
     (This is the downward-parabola step `t·(m-t+1) ≥ m`, in the shape that
     needs no subtraction and no case split on where the vertex `t` sits.)
  4. `t > m`.  Components are nonempty, so `#odd ≤ #components ≤ 2m - t`, and
     `2m - t < m < t` — no violation is possible for large `u` at all.

Only step 2 uses evenness of the vertex count, and it uses it only through the
parity of the odd-component count.  Steps 3 and 4 are pure counting.
-/
import Mathlib

namespace Conway99

open SimpleGraph

/-! ### Counting lemmas about connected components

Three facts about an arbitrary finite graph `H`, none of them about matchings:
the number of components is at most the number of vertices; if every component
has at least `q` vertices then `#components * q` is at most the vertex count;
and odd components are components. -/

section Counting

variable {W : Type*} [Finite W]

private lemma nat_card_connectedComponent_le (H : SimpleGraph W) :
    Nat.card H.ConnectedComponent ≤ Nat.card W :=
  Nat.card_le_card_of_surjective H.connectedComponentMk fun c => c.exists_rep

private lemma nat_card_connectedComponent_mul_le (H : SimpleGraph W) (q : ℕ)
    (hq : ∀ c : H.ConnectedComponent, q ≤ c.supp.ncard) :
    Nat.card H.ConnectedComponent * q ≤ Nat.card W := by
  classical
  cases nonempty_fintype W
  have hcov : (Finset.univ : Finset H.ConnectedComponent).biUnion
      (fun c => c.supp.toFinset) = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConnectedComponent.mem_supp_iff, iff_true]
    exact ⟨H.connectedComponentMk v, rfl⟩
  have hsum := Finset.card_biUnion
    (s := (Finset.univ : Finset H.ConnectedComponent))
    (t := fun c : H.ConnectedComponent => c.supp.toFinset)
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr
      (pairwise_disjoint_supp_connectedComponent H hxy))
  rw [hcov] at hsum
  calc Nat.card H.ConnectedComponent * q
      = ∑ _c : H.ConnectedComponent, q := by
        simp [Nat.card_eq_fintype_card, mul_comm]
    _ ≤ ∑ c : H.ConnectedComponent, c.supp.toFinset.card :=
        Finset.sum_le_sum fun c _ => by
          rw [← Set.ncard_eq_toFinset_card']; exact hq c
    _ = Nat.card W := by rw [← hsum]; simp [Nat.card_eq_fintype_card]

private lemma ncard_oddComponents_le (H : SimpleGraph W) :
    H.oddComponents.ncard ≤ Nat.card H.ConnectedComponent := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ

end Counting

/-! ### Degrees as `Set.ncard` -/

variable {V : Type*} [Fintype V]

private lemma ncard_neighborSet_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]

/-! ### The sharp form: no Tutte violators -/

/-- **A graph on `2 * m` vertices with minimum degree `≥ m` has no Tutte
violator.**  This is the whole mathematical content; the matching statements
below are `SimpleGraph.tutte` applied to it. -/
theorem not_isTutteViolator_of_card_eq_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (hcard : Fintype.card V = 2 * m) (hdeg : ∀ v, m ≤ G.degree v) (u : Set V) :
    ¬ G.IsTutteViolator u := by
  classical
  intro hviol
  -- `hviol`, unfolded: `u` leaves behind more odd components than it has vertices
  have hviol' : u.ncard <
      ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard := hviol
  -- the surviving vertex set, and its size
  have hW : Nat.card ↥(((⊤ : G.Subgraph).deleteVerts u).verts) + u.ncard = 2 * m := by
    rw [Nat.card_coe_set_eq]
    have hverts : ((⊤ : G.Subgraph).deleteVerts u).verts = uᶜ := by
      rw [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.compl_eq_univ_sdiff]
    rw [hverts, Set.ncard_compl_add_ncard u, Nat.card_eq_fintype_card, hcard]
  -- STEP 1: every surviving component has at least `m - t + 1` vertices
  have hsize : ∀ c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent,
      m + 1 ≤ c.supp.ncard + u.ncard := by
    intro c
    obtain ⟨v, hv⟩ := c.nonempty_supp
    have hsub : insert (v : V) (G.neighborSet (v : V) \ u) ⊆ Subtype.val '' c.supp := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_sdiff, mem_neighborSet] at hw
      rcases hw with rfl | ⟨hwadj, hwu⟩
      · exact ⟨v, hv, rfl⟩
      · refine ⟨⟨w, ⟨Set.mem_univ w, hwu⟩⟩, ?_, rfl⟩
        refine ConnectedComponent.mem_supp_of_adj_mem_supp c hv ?_
        exact Subgraph.Adj.coe
          (Subgraph.deleteVerts_adj.mpr ⟨by trivial, v.2.2, by trivial, hwu, hwadj⟩)
    have h1 : (insert (v : V) (G.neighborSet (v : V) \ u)).ncard ≤ c.supp.ncard := by
      rw [← Set.ncard_image_of_injective c.supp Subtype.val_injective]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp) (Set.toFinite _)] at h1
    have h2 : G.degree (v : V) ≤ (G.neighborSet (v : V) \ u).ncard + u.ncard := by
      rw [← ncard_neighborSet_eq_degree]
      exact Set.ncard_le_ncard_sdiff_add_ncard _ _ (Set.toFinite _)
    have h3 := hdeg (v : V)
    omega
  -- the two generic component counts
  have hO := ncard_oddComponents_le ((⊤ : G.Subgraph).deleteVerts u).coe
  have hN := nat_card_connectedComponent_le ((⊤ : G.Subgraph).deleteVerts u).coe
  rcases Nat.eq_zero_or_pos u.ncard with ht0 | ht1
  · -- STEP 2: `t = 0` — at most one component, and the parity forbids it being odd
    have hq : ∀ c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent,
        m + 1 ≤ c.supp.ncard := fun c => by have := hsize c; omega
    have hmul := nat_card_connectedComponent_mul_le
      ((⊤ : G.Subgraph).deleteVerts u).coe (m + 1) hq
    have hlt2 : Nat.card ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent < 2 := by
      rcases Nat.lt_or_ge
        (Nat.card ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) 2 with hc | hc
      · exact hc
      · exact absurd (le_trans (Nat.mul_le_mul hc (le_refl (m + 1))) hmul) (by omega)
    have hOne : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard = 1 := by omega
    have hodd := (SimpleGraph.odd_ncard_oddComponents
      (G := ((⊤ : G.Subgraph).deleteVerts u).coe)).mp (by rw [hOne]; exact odd_one)
    rw [Nat.odd_iff] at hodd
    omega
  · rcases Nat.lt_or_ge u.ncard (m + 1) with htm | htm
    · -- STEP 3: `1 ≤ t ≤ m` — the downward parabola, subtraction-free
      obtain ⟨a, ha⟩ : ∃ a, u.ncard = a + 1 := ⟨u.ncard - 1, by omega⟩
      obtain ⟨s, hs⟩ : ∃ s, m = a + 1 + s := ⟨m - u.ncard, by omega⟩
      have hq : ∀ c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent,
          s + 1 ≤ c.supp.ncard := fun c => by have := hsize c; omega
      have hmul := nat_card_connectedComponent_mul_le
        ((⊤ : G.Subgraph).deleteVerts u).coe (s + 1) hq
      have hge : a + 2 ≤
          Nat.card ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent := by omega
      have hle : (a + 2) * (s + 1) ≤
          Nat.card ↥(((⊤ : G.Subgraph).deleteVerts u).verts) :=
        le_trans (Nat.mul_le_mul hge (le_refl (s + 1))) hmul
      have hexp : a + 2 * s + 2 ≤ (a + 2) * (s + 1) :=
        calc a + 2 * s + 2 ≤ a * s + (a + 2 * s + 2) := Nat.le_add_left _ _
          _ = (a + 2) * (s + 1) := by ring
      have hfin := le_trans hexp hle
      omega
    · -- STEP 4: `t > m` — too few vertices are left to host `t+1` components
      omega

/-! ### The matching statements -/

/-- **Dirac-type perfect matching lemma, generic form.**  A graph on `2 * m`
vertices all of whose degrees are at least `m` has a perfect matching. -/
theorem exists_perfectMatching_of_card_eq_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (hcard : Fintype.card V = 2 * m) (hdeg : ∀ v, m ≤ G.degree v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  SimpleGraph.tutte.mpr (not_isTutteViolator_of_card_eq_two_mul G hcard hdeg)

/-- **Dirac-type perfect matching lemma**, in the form the hypotheses are
usually met in: an even number of vertices, and every degree at least half of
it.  (`Fintype.card V ≤ 2 * G.degree v` is exactly `G.degree v ≥ |V| / 2` with
no division.) -/
theorem exists_perfectMatching_of_card_le_two_mul_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : Even (Fintype.card V))
    (hdeg : ∀ v, Fintype.card V ≤ 2 * G.degree v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨m, hm⟩ := heven
  refine exists_perfectMatching_of_card_eq_two_mul G (m := m) (by omega) fun v => ?_
  have := hdeg v
  omega

/-- Concrete instance: `Fintype.card V = 14` and minimum degree `≥ 7`, the
shape the lemma is usually quoted in.  NOT USED by anything in this project:
the `14` that actually arises downstream is the REPLICATION NUMBER of a
2-(22,4,2) design (`Alpha22.lean`), not a vertex-neighbourhood size, and
`Alpha22.lean` reaches it through the generic `2 * m` form above.  Kept as a
convenience statement only. -/
theorem exists_perfectMatching_of_card_eq_fourteen
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 14) (hdeg : ∀ v, 7 ≤ G.degree v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  exists_perfectMatching_of_card_eq_two_mul G (m := 7) (by omega) hdeg

/-! ### Non-vacuity: the 4-cycle, where the degree bound is TIGHT -/

/-- The 4-cycle on `Fin 4`, realised as "the two vertices have different
parity" (so `0 ~ 1 ~ 2 ~ 3 ~ 0`).  Four vertices, every degree exactly two:
the hypotheses of the lemma hold with NO slack. -/
def C4 : SimpleGraph (Fin 4) where
  Adj a b := (a : ℕ) % 2 ≠ (b : ℕ) % 2
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance C4DecidableRel : DecidableRel C4.Adj := fun a b =>
  inferInstanceAs (Decidable ((a : ℕ) % 2 ≠ (b : ℕ) % 2))

/-- The degree bound is met exactly, not with room to spare. -/
theorem C4_degree_eq : ∀ v, C4.degree v = 2 := by decide

/-- The hypotheses of `exists_perfectMatching_of_card_le_two_mul_degree` are
jointly satisfiable — checked by `decide`, so the theorem above is not vacuous. -/
theorem C4_hypotheses :
    Even (Fintype.card (Fin 4)) ∧ ∀ v, Fintype.card (Fin 4) ≤ 2 * C4.degree v := by
  refine ⟨⟨2, by decide⟩, by decide⟩

/-- …and the lemma delivers a perfect matching on it. -/
theorem C4_exists_perfectMatching : ∃ M : C4.Subgraph, M.IsPerfectMatching :=
  exists_perfectMatching_of_card_le_two_mul_degree C4 C4_hypotheses.1 C4_hypotheses.2

end Conway99
