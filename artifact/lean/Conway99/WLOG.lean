/-
Conway99.WLOG — the HARD direction of the skeleton WLOG theorem.

`Conway99.skeletonWLOG : skeletonWLOG_statement` (statement in
`Conway99/Skeleton.lean`): every srg(99,14,1,2), on ANY vertex type, is
isomorphic to a completion of the canonical skeleton — so the SAT search
over the 3,486 free outside-outside variables loses no models.

Structure (matching the proof plan in the `skeletonWLOG_statement`
docstring):

  * `isSRGWith_of_iso` — `IsSRGWith` transports along a graph isomorphism
    (`card_commonNeighbors_iso` / `degree_iso` are the counting bridges).
  * `finPairEquiv`, `pairOf_partner` — `Fin 14` as 7 blocks × Bool, the
    bridge to `Conway99.Group`'s fixed matching.
  * `exists_partner_compatible_equiv` — ANY fixed-point-free involution on
    a 14-element type can be enumerated compatibly with the fixed matching
    `partner`: the orbit quotient has 7 classes (each `{u, f u}` splits as
    representative/partner, giving `S ≃ orbits × Bool`), and composing
    orbit-enumeration with `finPairEquiv` aligns the matchings.
  * `exists_skeleton_iso_rooted` — the construction, with the root `v₀`
    taken as a PARAMETER and the isomorphism proved to carry the skeleton's
    root `rootV` to it: the λ=1 matching involution on N(v₀)
    (`neighborhood_matching`), the matching-compatible enumeration
    `nu : Fin 14 → V`, the unique outside common neighbor `wo i` of each
    non-matched pair (`outside_common_neighbor`), injectivity of the
    assembled `E : Fin 99 → V` (μ=2 kills any vertex seeing three of N(v₀)
    — `hthree`), bijectivity by counting, and the region-by-region
    adjacency agreement with `skeletonGraph`.
  * `exists_skeleton_iso`, `skeletonWLOG`, `skeletonWLOG_poly` — the
    original (root-forgetting) statements, now corollaries.
  * `skeletonWLOG_rooted` — the rooted statement with `IsSRGWith` on the
    skeleton side, the form root-indexed facts transport along.
  * `D_iso` (+ `IsFlag.map`, `IsCanonFlag.map`, `classOf_iso`, …) — the
    canonical-transition counter of `FlagCount.lean` is an isomorphism
    invariant, so a bound at the skeleton's root IS a bound at `v₀`.
  * `forall_D_le_of_skeleton_root` / `conway99_n3_ge_of_skeleton_root` —
    the two composed: a skeleton-root bound on `D`, valid for every
    completion that is an srg(99,14,1,2), yields `∀ x, D G x ≤ m` and
    hence `n₃ ≥ 348` at `m = 77`.  **The skeleton-root bound itself is a
    HYPOTHESIS** (it is the SAT/DRAT certificate plus the informal encoder
    correspondence); what is proved here is the root-quantifier step.

WHY THE ROOT PARAMETER (2026-08-11).  `exists_skeleton_iso` obtained `v₀`
INSIDE its proof, so its statement said nothing about which vertex became
the root; a bound proved at the skeleton's root could then be exported only
as `∃ x, …`, never `∀ x, …`.  The construction never used any property of
`v₀`, so taking it as a parameter — and, the load-bearing half, RECORDING
`e rootV = v₀` in the conclusion — closes that gap.

Everything is sorry-free, no `native_decide`; audited in
`Conway99/Audit.lean`.
-/
import Mathlib
import Conway99.Skeleton
import Conway99.FlagCount

/- `show` is used heavily below to pin definitional unfoldings (cond/match
reductions) — deliberate here: the explicit goal states ARE the audit
trail.  Silenced file-locally, matching the lakefile's policy of keeping
audit logs readable. -/
set_option linter.style.show false

namespace Conway99

open SimpleGraph

/-! ### Transport of `IsSRGWith` along a graph isomorphism -/

section Transport

variable {V : Type*} {W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
variable {n k l m : ℕ}

/-- Common-neighbor counts transport along a graph isomorphism. -/
theorem card_commonNeighbors_iso [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (a b : V) :
    Fintype.card (H.commonNeighbors (f a) (f b)) =
      Fintype.card (G.commonNeighbors a b) :=
  Fintype.card_congr
    ((Equiv.subtypeEquiv f.toEquiv fun x => by
      rw [mem_commonNeighbors, mem_commonNeighbors]
      exact and_congr f.map_adj_iff.symm f.map_adj_iff.symm).symm)

/-- Degrees transport along a graph isomorphism. -/
theorem degree_iso [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (v : V) : H.degree (f v) = G.degree v := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr (f.mapNeighborSet v).symm

/-- `IsSRGWith` transports along a graph isomorphism: all four defining
counts are counts of sets the isomorphism puts in bijection. -/
theorem isSRGWith_of_iso [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (h : G.IsSRGWith n k l m) : H.IsSRGWith n k l m := by
  constructor
  · rw [← f.card_eq]
    exact h.card
  · intro w
    have hw : f (f.symm w) = w := f.apply_symm_apply w
    rw [← hw, degree_iso f]
    exact h.regular (f.symm w)
  · intro v w hadj
    have hv : f (f.symm v) = v := f.apply_symm_apply v
    have hw : f (f.symm w) = w := f.apply_symm_apply w
    rw [← hv, ← hw, card_commonNeighbors_iso f]
    apply h.of_adj
    rw [← f.map_adj_iff, hv, hw]
    exact hadj
  · intro v w hne hnadj
    have hv : f (f.symm v) = v := f.apply_symm_apply v
    have hw : f (f.symm w) = w := f.apply_symm_apply w
    rw [← hv, ← hw, card_commonNeighbors_iso f]
    apply h.of_not_adj
    · intro hc
      exact hne (by rw [← hv, ← hw, hc])
    · intro hc
      apply hnadj
      rw [← hv, ← hw]
      exact f.map_adj_iff.mpr hc

end Transport

/-! ### `Fin 14` as 7 matched pairs × position -/

/-- The block of the matched partner is the block of the vertex. -/
theorem pairOf_partner (v : Fin 14) : pairOf (partner v) = pairOf v :=
  pairOf_member _ _

/-- The position of the matched partner is the flipped position bit. -/
theorem posIn_partner (v : Fin 14) : posIn (partner v) = !posIn v :=
  posIn_member _ _

/-- `Fin 14 ≃ Fin 7 × Bool` via (block, position) — `Conway99.Group`'s
`member`/`pairOf`/`posIn` packaged as an equivalence. -/
def finPairEquiv : Fin 14 ≃ Fin 7 × Bool where
  toFun w := (pairOf w, posIn w)
  invFun p := member p.1 p.2
  left_inv w := member_pairOf_posIn w
  right_inv p := by
    cases p with
    | mk a b => simp only [pairOf_member, posIn_member]

@[simp] theorem finPairEquiv_apply (w : Fin 14) :
    finPairEquiv w = (pairOf w, posIn w) := rfl

/-- Under `finPairEquiv`, taking the matched partner is flipping the
position bit. -/
theorem finPairEquiv_partner (w : Fin 14) :
    finPairEquiv (partner w) = (pairOf w, !posIn w) := by
  simp only [finPairEquiv_apply, partner, pairOf_member, posIn_member]

/-! ### Enumerating a fixed-point-free involution compatibly with the
fixed matching -/

/-- Any fixed-point-free involution `f` on a 14-element type can be
enumerated compatibly with the fixed matching of `Conway99.Group`: there
is an equivalence `e : Fin 14 ≃ S` with `e (partner w) = f (e w)` for all
`w`.  (Each orbit `{u, f u}` has exactly two elements, so `S` splits as
orbits × Bool with `f` flipping the Bool; there are 7 orbits by counting;
`finPairEquiv` aligns this with `pairOf`/`partner`.) -/
theorem exists_partner_compatible_equiv {S : Type*} [Fintype S]
    (hcard : Fintype.card S = 14) (f : S → S)
    (hinv : ∀ u, f (f u) = u) (hfix : ∀ u, f u ≠ u) :
    ∃ e : Fin 14 ≃ S, ∀ w : Fin 14, e (partner w) = f (e w) := by
  classical
  -- the orbit setoid of the involution: u ≈ v iff v = u or v = f u
  letI sd : Setoid S :=
    ⟨fun u v => v = u ∨ v = f u, by
      refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
      · rintro x y (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (hinv x).symm
      · rintro x y z (rfl | rfl) hyz
        · exact hyz
        · rcases hyz with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (hinv x)⟩
  haveI : DecidableRel ((· ≈ ·) : S → S → Prop) := fun _ _ => Classical.dec _
  -- each orbit splits as representative / image: S ≃ orbits × Bool,
  -- with the involution acting as the bit flip
  have key : ∃ E : Quotient sd × Bool ≃ S, ∀ (q : Quotient sd) (b : Bool),
      E (q, !b) = f (E (q, b)) := by
    have hrep : ∀ q : Quotient sd, (⟦q.out⟧ : Quotient sd) = q :=
      fun q => Quotient.out_eq q
    refine ⟨⟨fun p => cond p.2 (f p.1.out) p.1.out,
             fun u => (⟦u⟧, decide (u ≠ (⟦u⟧ : Quotient sd).out)), ?_, ?_⟩, ?_⟩
    · -- left inverse
      rintro ⟨q, b⟩
      cases b
      · show ((⟦q.out⟧ : Quotient sd),
          decide (q.out ≠ (⟦q.out⟧ : Quotient sd).out)) = (q, false)
        rw [Prod.mk.injEq]
        refine ⟨hrep q, ?_⟩
        rw [hrep q]
        simp
      · show ((⟦f q.out⟧ : Quotient sd),
          decide (f q.out ≠ (⟦f q.out⟧ : Quotient sd).out)) = (q, true)
        have h1 : (⟦f q.out⟧ : Quotient sd) = q :=
          (Quotient.sound (Or.inr (hinv q.out).symm)).trans (hrep q)
        rw [Prod.mk.injEq]
        refine ⟨h1, ?_⟩
        rw [h1]
        simp [hfix q.out]
    · -- right inverse
      intro u
      by_cases hu : u = (⟦u⟧ : Quotient sd).out
      · have hd : decide (u ≠ (⟦u⟧ : Quotient sd).out) = false :=
          decide_eq_false fun hc => hc hu
        show cond (decide (u ≠ (⟦u⟧ : Quotient sd).out))
          (f (⟦u⟧ : Quotient sd).out) (⟦u⟧ : Quotient sd).out = u
        rw [hd]
        exact hu.symm
      · have hd : decide (u ≠ (⟦u⟧ : Quotient sd).out) = true :=
          decide_eq_true hu
        show cond (decide (u ≠ (⟦u⟧ : Quotient sd).out))
          (f (⟦u⟧ : Quotient sd).out) (⟦u⟧ : Quotient sd).out = u
        rw [hd]
        -- u is in the orbit of its representative but is not it, so it
        -- is the image
        have horb : u = (⟦u⟧ : Quotient sd).out ∨
            u = f ((⟦u⟧ : Quotient sd).out) := Quotient.mk_out (s := sd) u
        rcases horb with hc | hc
        · exact absurd hc hu
        · exact hc.symm
    · -- the involution flips the bit
      intro q b
      cases b
      · show cond (!false) (f q.out) q.out = f (cond false (f q.out) q.out)
        rfl
      · show cond (!true) (f q.out) q.out = f (cond true (f q.out) q.out)
        show q.out = f (f q.out)
        exact (hinv q.out).symm
  obtain ⟨EQ, hEQ⟩ := key
  -- 7 orbits by counting
  have hQcard : Fintype.card (Quotient sd) = 7 := by
    have h1 : Fintype.card (Quotient sd × Bool) = 14 := by
      rw [Fintype.card_congr EQ, hcard]
    rw [Fintype.card_prod, Fintype.card_bool] at h1
    omega
  refine ⟨finPairEquiv.trans
    (((Fintype.equivFinOfCardEq hQcard).symm.prodCongr
      (Equiv.refl Bool)).trans EQ), fun w => ?_⟩
  simp only [Equiv.trans_apply, finPairEquiv_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq]
  rw [pairOf_partner, posIn_partner]
  exact hEQ _ _

/-! ### The construction: from an arbitrary srg(99,14,1,2) to a skeleton
completion -/

/-- **ROOTED** form of the skeleton WLOG: for EVERY prescribed vertex
`v₀ : V`, an srg(99,14,1,2) is isomorphic to a completion of the canonical
skeleton **by an isomorphism that carries the skeleton's root `rootV`
(= vertex `0` of the `1 + 14 + 84` decomposition) to `v₀`**.

The root equation is the load-bearing part and the reason this, not the
unrooted `exists_skeleton_iso` below, is the theorem to cite: a quantity
computed at the skeleton's root — e.g. `FlagCount.D … rootV`, the counter
the SAT campaign bounds — transfers to `v₀` SPECIFICALLY, hence (as `v₀`
ranges over `V`) to every vertex of `G`.  Without it, a bound proved at the
skeleton root yields only `∃ x, …`, not `∀ x, …`.

Nothing in the construction uses any property of `v₀` beyond membership in
`V`, which is exactly why it may be taken as a parameter. -/
theorem exists_skeleton_iso_rooted {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (v0 : V) :
    ∃ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false)
      (e : (skeletonGraph X hsymm hirrefl) ≃g G), e rootV = v0 := by
  classical
  -- 1. the root is GIVEN (`v0`); nothing below uses anything about it
  -- 2. N(v₀) and its λ=1 matching involution
  have hS : Fintype.card (G.neighborFinset v0) = 14 := by
    rw [Fintype.card_coe, card_neighborFinset_eq_degree]
    exact h.regular v0
  have hmatch : ∀ u : G.neighborFinset v0, ∃ w : G.neighborFinset v0,
      G.Adj (u : V) (w : V) ∧
        ∀ y : V, G.Adj v0 y → G.Adj (u : V) y → y = (w : V) := by
    intro u
    have hu : G.Adj v0 (u : V) := by
      have := u.2; rwa [mem_neighborFinset] at this
    obtain ⟨w, ⟨hvw, huw⟩, huniq⟩ := neighborhood_matching h hu
    have hwmem : w ∈ G.neighborFinset v0 := by rwa [mem_neighborFinset]
    exact ⟨⟨w, hwmem⟩, huw, fun y hy1 hy2 => huniq y ⟨hy1, hy2⟩⟩
  choose M hM1 hM2 using hmatch
  have hMadj : ∀ u : G.neighborFinset v0, G.Adj v0 (M u : V) := by
    intro u
    have := (M u).2; rwa [mem_neighborFinset] at this
  have hMinv : ∀ u, M (M u) = u := by
    intro u
    have hu : G.Adj v0 (u : V) := by
      have := u.2; rwa [mem_neighborFinset] at this
    have := hM2 (M u) (u : V) hu (hM1 u).symm
    exact Subtype.ext this.symm
  have hMfix : ∀ u, M u ≠ u := by
    intro u heq
    exact (hM1 u).ne (by rw [heq])
  -- 3. matching-compatible enumeration of N(v₀), packaged opaquely
  have hnu_ex : ∃ nu : Fin 14 → V, (∀ w, G.Adj v0 (nu w)) ∧
      Function.Injective nu ∧
      (∀ w w', G.Adj (nu w) (nu w') ↔ partner w = w') := by
    obtain ⟨eN, heN⟩ := exists_partner_compatible_equiv hS M hMinv hMfix
    have hadj : ∀ w, G.Adj v0 ((eN w : V)) := by
      intro w
      have := (eN w).2; rwa [mem_neighborFinset] at this
    have hpm : ∀ w, ((eN (partner w) : V)) = ((M (eN w) : V)) :=
      fun w => congrArg Subtype.val (heN w)
    refine ⟨fun w => (eN w : V), hadj, ?_, ?_⟩
    · intro w w' hww'
      exact eN.injective (Subtype.ext hww')
    · intro w w'
      constructor
      · intro hadj'
        have h1 := hM2 (eN w) ((eN w' : V)) (hadj w') hadj'
        have h2 : ((eN w' : V)) = ((eN (partner w) : V)) := by
          rw [hpm]; exact h1
        have := eN.injective (Subtype.ext h2)
        exact this.symm
      · rintro rfl
        show G.Adj ((eN w : V)) ((eN (partner w) : V))
        rw [hpm]
        exact hM1 (eN w)
  obtain ⟨nu, hnu_adj, hnu_inj, hnu_adj_iff⟩ := hnu_ex
  -- 4. the unique outside common neighbor of each non-matched pair
  have houtside : ∀ i : Fin 84, ∃ x : V,
      (x ≠ v0 ∧ G.Adj (nu (labelAt i).1) x ∧ G.Adj (nu (labelAt i).2) x ∧
        ¬G.Adj v0 x) ∧
      ∀ y : V, G.Adj (nu (labelAt i).1) y → G.Adj (nu (labelAt i).2) y →
        y = v0 ∨ y = x := by
    intro i
    have hab : ¬G.Adj (nu (labelAt i).1) (nu (labelAt i).2) := by
      rw [hnu_adj_iff]
      intro hpart
      have h1 : pairOf (labelAt i).2 = pairOf (labelAt i).1 := by
        rw [← hpart, pairOf_partner]
      exact labelReps_pairOf_ne _ (labelAt_mem i) h1.symm
    have hne : nu (labelAt i).1 ≠ nu (labelAt i).2 :=
      fun hc => (labelAt_lt i).ne (hnu_inj hc)
    obtain ⟨x, hx1, hx2⟩ :=
      outside_common_neighbor h (hnu_adj (labelAt i).1)
        (hnu_adj (labelAt i).2) hab hne
    exact ⟨x, hx1, hx2⟩
  choose wo hwo hwu using houtside
  have hwo_ne_v0 : ∀ i, wo i ≠ v0 := fun i => (hwo i).1
  have hwo_nadj : ∀ i, ¬G.Adj v0 (wo i) := fun i => (hwo i).2.2.2
  have hwo_ne_nu : ∀ i w, wo i ≠ nu w := by
    intro i w heq
    apply hwo_nadj i
    rw [heq]
    exact hnu_adj w
  -- 5. μ=2: no non-neighbor of v₀ sees three vertices of N(v₀)
  have hthree : ∀ x : V, x ≠ v0 → ¬G.Adj v0 x →
      ∀ w1 w2 w3 : Fin 14, w1 ≠ w2 → w1 ≠ w3 → w2 ≠ w3 →
      G.Adj (nu w1) x → G.Adj (nu w2) x → G.Adj (nu w3) x → False := by
    intro x hxv hvx w1 w2 w3 h12 h13 h23 ha1 ha2 ha3
    have hcard2 : Fintype.card (G.commonNeighbors v0 x) = 2 :=
      h.of_not_adj (Ne.symm hxv) hvx
    have hsub : ({nu w1, nu w2, nu w3} : Finset V) ⊆
        (G.commonNeighbors v0 x).toFinset := by
      intro y hy
      rw [Set.mem_toFinset]
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact (mem_commonNeighbors G).mpr ⟨hnu_adj w1, ha1.symm⟩
      · rcases Finset.mem_insert.mp hy' with rfl | hy''
        · exact (mem_commonNeighbors G).mpr ⟨hnu_adj w2, ha2.symm⟩
        · rw [Finset.mem_singleton] at hy''
          subst hy''
          exact (mem_commonNeighbors G).mpr ⟨hnu_adj w3, ha3.symm⟩
    have hc3 : ({nu w1, nu w2, nu w3} : Finset V).card = 3 := by
      have hn1 : nu w1 ∉ ({nu w2, nu w3} : Finset V) := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with hc | hc
        · exact hnu_inj.ne h12 hc
        · exact hnu_inj.ne h13 (Finset.mem_singleton.mp hc)
      have hn2 : nu w2 ∉ ({nu w3} : Finset V) := fun hmem =>
        hnu_inj.ne h23 (Finset.mem_singleton.mp hmem)
      rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
        Finset.card_singleton]
    have hle := Finset.card_le_card hsub
    rw [hc3, Set.toFinset_card, hcard2] at hle
    omega
  -- 6. the outside witnesses are pairwise distinct
  have hwo_inj : Function.Injective wo := by
    intro i j hij
    by_contra hne
    have hpair : labelAt i ≠ labelAt j := fun hc => hne (labelAt_injective hc)
    have hab := labelAt_lt i
    have hcd := labelAt_lt j
    by_cases hc1 : (labelAt j).1 ≠ (labelAt i).1 ∧ (labelAt j).1 ≠ (labelAt i).2
    · refine hthree (wo i) (hwo_ne_v0 i) (hwo_nadj i)
        (labelAt i).1 (labelAt i).2 (labelAt j).1
        hab.ne hc1.1.symm hc1.2.symm (hwo i).2.1 (hwo i).2.2.1 ?_
      rw [hij]
      exact (hwo j).2.1
    · by_cases hd1 : (labelAt j).2 ≠ (labelAt i).1 ∧ (labelAt j).2 ≠ (labelAt i).2
      · refine hthree (wo i) (hwo_ne_v0 i) (hwo_nadj i)
          (labelAt i).1 (labelAt i).2 (labelAt j).2
          hab.ne hd1.1.symm hd1.2.symm (hwo i).2.1 (hwo i).2.2.1 ?_
        rw [hij]
        exact (hwo j).2.2.1
      · -- both endpoints of label j lie in label i ⇒ the labels coincide
        push Not at hc1 hd1
        by_cases hca : (labelAt j).1 = (labelAt i).1
        · by_cases hda : (labelAt j).2 = (labelAt i).1
          · exact hcd.ne (hca.trans hda.symm)
          · exact hpair (Prod.ext hca (hd1 hda)).symm
        · have hcb : (labelAt j).1 = (labelAt i).2 := hc1 hca
          by_cases hda : (labelAt j).2 = (labelAt i).1
          · rw [hcb, hda] at hcd
            exact absurd (hab.trans hcd) (lt_irrefl _)
          · exact hcd.ne (hcb.trans (hd1 hda).symm)
  -- 7. the assembled vertex identification Fin 99 → V
  have hEex : ∃ E : Fin 99 → V, E rootV = v0 ∧ (∀ w, E (nVert w) = nu w) ∧
      (∀ i, E (outVert i) = wo i) := by
    refine ⟨fun u => match regionOf u with
      | .root => v0
      | .inN w => nu w
      | .outside i => wo i, rfl, fun w => ?_, fun i => ?_⟩
    · show (match regionOf (nVert w) with
        | .root => v0
        | .inN w => nu w
        | .outside i => wo i) = nu w
      rw [regionOf_nVert]
    · show (match regionOf (outVert i) with
        | .root => v0
        | .inN w => nu w
        | .outside i => wo i) = wo i
      rw [regionOf_outVert]
  obtain ⟨E, hEr, hEn, hEo⟩ := hEex
  have hEinj : Function.Injective E := by
    intro u u' heq
    rcases region_cases u with rfl | ⟨w, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases region_cases u' with rfl | ⟨w', rfl⟩ | ⟨i', rfl⟩
    · rfl
    · rw [hEr, hEn] at heq
      exact absurd heq (hnu_adj w').ne
    · rw [hEr, hEo] at heq
      exact absurd heq.symm (hwo_ne_v0 i')
    · rw [hEn, hEr] at heq
      exact absurd heq.symm (hnu_adj w).ne
    · rw [hEn, hEn] at heq
      rw [hnu_inj heq]
    · rw [hEn, hEo] at heq
      exact absurd heq.symm (hwo_ne_nu i' w)
    · rw [hEo, hEr] at heq
      exact absurd heq (hwo_ne_v0 i)
    · rw [hEo, hEn] at heq
      exact absurd heq (hwo_ne_nu i w')
    · rw [hEo, hEo] at heq
      rw [hwo_inj heq]
  have hEbij : Function.Bijective E :=
    (Fintype.bijective_iff_injective_and_card E).mpr
      ⟨hEinj, by rw [Fintype.card_fin, h.card]⟩
  -- 8. the free block, the isomorphism, and the root equation
  refine ⟨fun i j => decide (G.Adj (wo i) (wo j)), fun i j => ?_,
    fun i => ?_, ?_, ?_⟩
  · rw [decide_eq_decide]
    exact G.adj_comm _ _
  · rw [decide_eq_false_iff_not]
    exact G.irrefl
  · refine ⟨Equiv.ofBijective E hEbij, @fun u u' => ?_⟩
    show G.Adj (E u) (E u') ↔ _
    rcases region_cases u with rfl | ⟨w, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases region_cases u' with rfl | ⟨w', rfl⟩ | ⟨i', rfl⟩
    · -- root, root
      rw [hEr]
      exact iff_of_false G.irrefl (skeletonGraph _ _ _).irrefl
    · -- root, N
      rw [hEr, hEn, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_root, regionOf_nVert, regAdjB]
      simpa using hnu_adj w'
    · -- root, outside
      rw [hEr, hEo, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_root, regionOf_outVert, regAdjB]
      simpa using hwo_nadj i'
    · -- N, root
      rw [hEn, hEr, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_root, regionOf_nVert, regAdjB]
      simpa using (hnu_adj w).symm
    · -- N, N
      rw [hEn, hEn, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_nVert, regAdjB, decide_eq_true_eq]
      rw [hnu_adj_iff]
      exact (same_pair_iff_partner w w').symm
    · -- N, outside
      rw [hEn, hEo, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_nVert, regionOf_outVert, regAdjB,
        decide_eq_true_eq]
      constructor
      · intro hadj
        by_contra hcon
        push Not at hcon
        exact hthree (wo i') (hwo_ne_v0 i') (hwo_nadj i')
          (labelAt i').1 (labelAt i').2 w
          (labelAt_lt i').ne (Ne.symm hcon.1) (Ne.symm hcon.2)
          (hwo i').2.1 (hwo i').2.2.1 hadj
      · rintro (rfl | rfl)
        · exact (hwo i').2.1
        · exact (hwo i').2.2.1
    · -- outside, root
      rw [hEo, hEr, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_root, regionOf_outVert, regAdjB]
      simpa using fun hadj => hwo_nadj i hadj.symm
    · -- outside, N
      rw [hEo, hEn, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_nVert, regionOf_outVert, regAdjB,
        decide_eq_true_eq]
      rw [G.adj_comm]
      constructor
      · intro hadj
        by_contra hcon
        push Not at hcon
        exact hthree (wo i) (hwo_ne_v0 i) (hwo_nadj i)
          (labelAt i).1 (labelAt i).2 w'
          (labelAt_lt i).ne (Ne.symm hcon.1) (Ne.symm hcon.2)
          (hwo i).2.1 (hwo i).2.2.1 hadj
      · rintro (rfl | rfl)
        · exact (hwo i).2.1
        · exact (hwo i).2.2.1
    · -- outside, outside
      rw [hEo, hEo, skeletonGraph_adj]
      simp only [skeletonAdjB, regionOf_outVert, regAdjB, decide_eq_true_eq]
  · -- THE ROOT EQUATION: the isomorphism carries `rootV` to the given `v₀`
    show E rootV = v0
    exact hEr

/-- Every srg(99,14,1,2) is isomorphic to a completion of the canonical
skeleton: there is a choice of the free outside-outside block `X` and a
graph isomorphism `skeletonGraph X ≃g G`.

UNROOTED corollary of `exists_skeleton_iso_rooted`, kept under its original
name because the campaign, the README and `Audit.lean` all cite it.  It
FORGETS which vertex the root came from, so it licenses only existential
transfer (`∃ x, P x`) of root-indexed facts; use the rooted form when the
root matters. -/
theorem exists_skeleton_iso {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) :
    ∃ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false),
      Nonempty ((skeletonGraph X hsymm hirrefl) ≃g G) := by
  have hpos : 0 < Fintype.card V := by rw [h.card]; norm_num
  obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨X, hsymm, hirrefl, e, -⟩ := exists_skeleton_iso_rooted h v0
  exact ⟨X, hsymm, hirrefl, ⟨e⟩⟩

/-! ### The WLOG theorem, hard direction -/

/-- HARD direction of the WLOG (the easy direction is
`srg_exists_of_skeleton`): every srg(99,14,1,2), on any vertex type, is
isomorphic to a completion of the canonical skeleton; the SAT search over
the 3,486 free outside-outside variables loses no models. -/
theorem skeletonWLOG : skeletonWLOG_statement := by
  intro V _ _ G _ h
  obtain ⟨X, hsymm, hirrefl, ⟨iso⟩⟩ := exists_skeleton_iso h
  exact ⟨X, hsymm, hirrefl, isSRGWith_of_iso iso.symm h⟩

/-- Universe-polymorphic form of `skeletonWLOG` (verifier addition):
`skeletonWLOG_statement` quantifies over `V : Type` — universe 0, which
covers every concrete finite vertex type — but nothing in the construction
needs that restriction, and `exists_skeleton_iso` is already stated for
`Type*`.  This closes the gap between the docstring's "on ANY vertex type"
and the universe-0 statement.  (No `DecidableEq V` needed either.) -/
theorem skeletonWLOG_poly {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) :
    ∃ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2 := by
  obtain ⟨X, hsymm, hirrefl, ⟨iso⟩⟩ := exists_skeleton_iso h
  exact ⟨X, hsymm, hirrefl, isSRGWith_of_iso iso.symm h⟩

/-- **ROOTED** form of `skeletonWLOG_poly`, and the one a root-indexed
quantity should be transported along: for EVERY prescribed `v₀ : V` there is
a completion `X` of the skeleton which IS an srg(99,14,1,2), together with
an isomorphism onto `G` carrying `rootV` to `v₀`. -/
theorem skeletonWLOG_rooted {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (v0 : V) :
    ∃ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false)
      (e : (skeletonGraph X hsymm hirrefl) ≃g G),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2 ∧ e rootV = v0 := by
  obtain ⟨X, hsymm, hirrefl, e, hroot⟩ := exists_skeleton_iso_rooted h v0
  exact ⟨X, hsymm, hirrefl, e, isSRGWith_of_iso e.symm h, hroot⟩

/-! ### Transport of the canonical-transition counter `D`

The rooted WLOG says an isomorphism carries `rootV` to `v₀`.  To USE that we
also need the quantity being bounded to be an invariant of the abstract
graph — otherwise "the skeleton's root satisfies the bound" says nothing
about `v₀`.  `D_iso` is that missing step for `FlagCount.D`, the counter the
graded campaign bounds.  It needs no srg hypothesis: `D` is built from
adjacency and equality alone. -/

section DTransport

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

theorem IsPartner.map (f : G ≃g G') {x a a' : V} (hp : IsPartner G x a a') :
    IsPartner G' (f x) (f a) (f a') :=
  ⟨f.map_adj_iff.mpr hp.1, f.map_adj_iff.mpr hp.2.1, f.map_adj_iff.mpr hp.2.2⟩

theorem IsLabel.map (f : G ≃g G') {x a b z : V} (hl : IsLabel G x a b z) :
    IsLabel G' (f x) (f a) (f b) (f z) :=
  ⟨f.map_adj_iff.mpr hl.1, f.map_adj_iff.mpr hl.2.1,
    fun he => hl.2.2.1 (f.injective he),
    fun ha => hl.2.2.2 (f.map_adj_iff.mp ha)⟩

theorem IsFlag.map (f : G ≃g G') {x a b : V} (hf : IsFlag G x a b) :
    IsFlag G' (f x) (f a) (f b) :=
  ⟨f.map_adj_iff.mpr hf.1, f.map_adj_iff.mpr hf.2.1,
    fun he => hf.2.2.1 (f.injective he),
    fun ha => hf.2.2.2 (f.map_adj_iff.mp ha)⟩

theorem IsCanonFlag.map (f : G ≃g G') {x a b : V} (hc : IsCanonFlag G x a b) :
    IsCanonFlag G' (f x) (f a) (f b) := by
  obtain ⟨b', z, z', hp, hl, hl', hz⟩ := hc
  exact ⟨f b', f z, f z', hp.map f, hl.map f, hl'.map f, f.map_adj_iff.mpr hz⟩

theorem isFlag_iso (f : G ≃g G') (x a b : V) :
    IsFlag G' (f x) (f a) (f b) ↔ IsFlag G x a b := by
  refine ⟨fun hf => ?_, fun hf => hf.map f⟩
  simpa using hf.map f.symm

theorem isCanonFlag_iso (f : G ≃g G') (x a b : V) :
    IsCanonFlag G' (f x) (f a) (f b) ↔ IsCanonFlag G x a b := by
  refine ⟨fun hc => ?_, fun hc => hc.map f⟩
  simpa using hc.map f.symm

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- The matched class of `b` transports: `classOf` is the class in the
abstract graph, so the isomorphism maps it onto the image class. -/
theorem classOf_iso (f : G ≃g G') (x b : V) :
    classOf G' (f x) (f b) = (classOf G x b).image f := by
  ext w
  simp only [classOf, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨b, Or.inl rfl, rfl⟩
    · refine ⟨f.symm w, Or.inr ⟨?_, ?_⟩, f.apply_symm_apply w⟩
      · exact f.map_adj_iff.mp (by rwa [f.apply_symm_apply])
      · exact f.map_adj_iff.mp (by rwa [f.apply_symm_apply])
  · rintro ⟨v, (rfl | ⟨h1, h2⟩), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨f.map_adj_iff.mpr h1, f.map_adj_iff.mpr h2⟩

theorem canonFlagsAt_iso (f : G ≃g G') (x : V) :
    canonFlagsAt G' (f x) = (canonFlagsAt G x).image (fun p => (f p.1, f p.2)) := by
  ext p
  simp only [canonFlagsAt, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(f.symm p.1, f.symm p.2), ⟨?_, ?_⟩, ?_⟩
    · exact (isFlag_iso f x _ _).mp (by simpa using h1)
    · exact (isCanonFlag_iso f x _ _).mp (by simpa using h2)
    · simp
  · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1.map f, h2.map f⟩

theorem canonTransitionsAt_iso (f : G ≃g G') (x : V) :
    canonTransitionsAt G' (f x) =
      (canonTransitionsAt G x).image (fun t => (f t.1, t.2.image f)) := by
  simp only [canonTransitionsAt, canonFlagsAt_iso f, Finset.image_image]
  refine Finset.image_congr fun p _ => ?_
  simp only [Function.comp_apply, classOf_iso f]

/-- **`D` IS AN ISOMORPHISM INVARIANT**, pointwise: the canonical-transition
count at `x` in `G` equals the count at `f x` in `G'`.  With
`exists_skeleton_iso_rooted` this is what carries a bound proved at the
skeleton's root to a PRESCRIBED vertex of an abstract srg(99,14,1,2). -/
theorem D_iso (f : G ≃g G') (x : V) : D G' (f x) = D G x := by
  have hinj : Function.Injective (fun t : V × Finset V => (f t.1, t.2.image f)) := by
    rintro ⟨a, S⟩ ⟨a', S'⟩ heq
    rw [Prod.mk.injEq] at heq
    refine Prod.ext (f.injective heq.1) ?_
    ext v
    have hv := Finset.ext_iff.mp heq.2 (f v)
    simpa [f.injective.eq_iff] using hv
  simp only [D, canonTransitionsAt_iso f, Finset.card_image_of_injective _ hinj]

end DTransport

/-! ### The root-quantifier bridge: a skeleton-root bound becomes a
universal bound

This is the shape the graded campaign's certificates are consumed in.  The
HYPOTHESIS `hskel` is the SAT/DRAT statement — "on every completion of the
canonical skeleton that is an srg(99,14,1,2), the canonical-transition
counter at the skeleton's root is at most `m`" — and is NOT proved here (the
tie between the CNF the solver refuted and `D … rootV` is the encoder
correspondence, informal item 7(c) of lean/README.md).  What IS proved here
is the inference from it to a bound at EVERY vertex of EVERY abstract
srg(99,14,1,2): that step is the root quantifier, and it needs both the
rooted WLOG and `D_iso`. -/

/-- From a bound on `D` at the skeleton's root, valid for every skeleton
completion that is an srg(99,14,1,2), to `∀ x, D G x ≤ m` on an arbitrary
srg(99,14,1,2).  The unrooted `exists_skeleton_iso` gives only `∃ x`. -/
theorem forall_D_le_of_skeleton_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) {m : ℕ}
    (hskel : ∀ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2 →
        D (skeletonGraph X hsymm hirrefl) rootV ≤ m) :
    ∀ x : V, D G x ≤ m := by
  intro x
  obtain ⟨X, hsymm, hirrefl, e, hsrg, hroot⟩ := skeletonWLOG_rooted G h x
  have hD : D G x = D (skeletonGraph X hsymm hirrefl) rootV := by
    rw [← hroot]; exact D_iso e rootV
  rw [hD]
  exact hskel X hsymm hirrefl hsrg

/-- The headline chain, assembled: the certified rung `D ≤ 77` at the
skeleton's root gives `n₃ ≥ 348` for EVERY srg(99,14,1,2).  `hskel` is the
SAT certificate (not a Lean theorem — see the section docstring); everything
between it and the conclusion is proved. -/
theorem conway99_n3_ge_of_skeleton_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (hskel : ∀ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2 →
        D (skeletonGraph X hsymm hirrefl) rootV ≤ 77) :
    348 ≤ n3 G :=
  conway99_n3_ge h (forall_D_le_of_skeleton_root h hskel)

end Conway99
