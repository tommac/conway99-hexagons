/-
Conway99.Switch2 — the 2-switch theorem of log 034, formalized.

CONTEXT.  The audit of the external srg(243,22,1,2) deliverable (log 034)
found that three of its four "hunts" for a NON-canonical member of the
λ=1, μ=2 family had provably zero power.  One of the three was a
4.03-million-trial random search over degree-preserving 2-switches, and the
reason it could not have succeeded under any seed is this theorem, which fell
out of the audit and had lived only in a markdown note:

> **THEOREM.**  No degree-preserving 2-switch on an srg(v,k,1,2) yields an
> srg(v,k,1,2).

A *degree-preserving 2-switch* on disjoint edges `{a,b}`, `{c,d}` with
`a ≁ c` and `b ≁ d` deletes those two edges and inserts `{a,c}`, `{b,d}`.
Each of the four vertices loses exactly one incidence and gains exactly one,
so every degree is unchanged — that is what "degree-preserving" names; the
theorem below does not need to assume it.

WHAT IS PROVED, AND IT IS STRONGER THAN THE HEADLINE.  `switch_not_lambda_one`
shows the switched graph cannot have λ = 1 AT ALL — no assumption on its
vertex count, degree or μ.  The headline `not_isSRGWith_switch` (and its
spec form `not_isSRGWith_of_switch`) is the immediate corollary.  So the
switch cannot even stay inside the λ=1 world, let alone reach srg(v,k,1,2).
Both are stated for an ARBITRARY graph whose adjacency is the switch of `G`'s
(`hspec`), and `switchGraph` is the concrete witness that such a graph exists
— so the statement is not vacuous.

THE ARGUMENT (log 034, and the Lean proof follows it line for line).  Let `t`
be the unique common neighbour of the adjacent pair `a`, `b` (λ = 1).

  1. `t ∉ {c, d}`: `t = c` would make `a ~ c` and `t = d` would make `b ~ d`.
     So `t` is untouched by the switch and keeps exactly its old neighbours.
  2. The edge `{a, t}` SURVIVES the switch, and in `G` its unique common
     neighbour with `a` is `b` — which the switch removes from `N(a)`.  So
     λ = 1 in the switched graph forces a NEW common neighbour, and the only
     candidate is the newly added `c`: hence `t ~ c`.  Symmetrically, the
     surviving edge `{b, t}` forces `t ~ d`.
  3. Now `a, b, c, d ∈ N(t)` with `a ~ b` and `c ~ d`.  λ = 1 says `N(t)`
     induces a perfect matching (`SRG.neighborhood_matching`), so `{a,b}` and
     `{c,d}` are two of its edges and therefore `a ≁ d` and `b ≁ c`.  (In the
     proof this is the uniqueness statement `unique_common_of_adj` applied to
     the edges `{a,t}` and `{b,t}` — the same fact in the form that is
     cheapest to use.)
  4. `a ≁ c` in `G` and `a ≠ c`, so μ = 2 gives a SECOND common neighbour `s`
     of `a` and `c` besides `t`.  By step 3, `s ≠ b` (else `b ~ c`) and
     `s ≠ d` (else `a ~ d`), so NEITHER of the two edges `{a,s}`, `{c,s}` is
     deleted by the switch: `s` survives as a common neighbour of `a` and
     `c`.  But `t` does too, and `{a,c}` is now an EDGE — two common
     neighbours on an edge contradicts λ = 1. ∎

μ = 2 enters only in step 4, and only through "there is a second common
neighbour"; λ = 1 of the SOURCE graph is used in steps 1–3, λ = 1 of the
TARGET graph in steps 2 and 4.
-/
import Mathlib
import Conway99.SRG

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k : ℕ}

/-! ### The switch, as an operation on adjacency -/

/-- The two pairs a 2-switch DELETES: `{a,b}` and `{c,d}`, in both vertex
orders (so the predicate is symmetric). -/
def SwitchRemoved (a b c d x y : V) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = c)

/-- The two pairs a 2-switch INSERTS: `{a,c}` and `{b,d}`, in both vertex
orders. -/
def SwitchAdded (a b c d x y : V) : Prop :=
  (x = a ∧ y = c) ∨ (x = c ∧ y = a) ∨ (x = b ∧ y = d) ∨ (x = d ∧ y = b)

instance decidableSwitchRemoved (a b c d x y : V) : Decidable (SwitchRemoved a b c d x y) := by
  unfold SwitchRemoved; infer_instance

instance decidableSwitchAdded (a b c d x y : V) : Decidable (SwitchAdded a b c d x y) := by
  unfold SwitchAdded; infer_instance

/-- The graph obtained from `G` by the degree-preserving 2-switch on `{a,b}`,
`{c,d}` → `{a,c}`, `{b,d}`.  The `x ≠ y` conjunct keeps the definition
irreflexive for arbitrary (possibly coinciding) `a, b, c, d`; under the
theorem's distinctness hypotheses it is implied by the rest. -/
def switchGraph (G : SimpleGraph V) (a b c d : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((G.Adj x y ∧ ¬ SwitchRemoved a b c d x y) ∨ SwitchAdded a b c d x y)
  symm := ⟨by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨hadj, hdel⟩ | hnew
    · refine Or.inl ⟨hadj.symm, ?_⟩
      unfold SwitchRemoved at hdel ⊢
      tauto
    · refine Or.inr ?_
      unfold SwitchAdded at hnew ⊢
      tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance switchGraphDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d : V) :
    DecidableRel (switchGraph G a b c d).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧
    ((G.Adj x y ∧ ¬ SwitchRemoved a b c d x y) ∨ SwitchAdded a b c d x y)))

/-- `switchGraph` satisfies the switch specification — the witness that makes
the `hspec`-form theorems below non-vacuous. -/
theorem switchGraph_adj_iff (G : SimpleGraph V) (a b c d x y : V) :
    (switchGraph G a b c d).Adj x y ↔
      x ≠ y ∧ ((G.Adj x y ∧ ¬ SwitchRemoved a b c d x y) ∨ SwitchAdded a b c d x y) :=
  Iff.rfl

/-! ### The theorem -/

/-- **No degree-preserving 2-switch on an srg(v,k,1,2) yields a graph with
λ = 1** — the sharp form of log 034's theorem, stated for ANY graph `G'`
whose adjacency is the switch of `G`'s.  Nothing is assumed about `G'`
beyond that every one of ITS edges has exactly one common neighbour; in
particular no vertex count, degree or μ is prescribed. -/
theorem switch_not_lambda_one
    (hG : G.IsSRGWith n k 1 2) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (hac_ne : a ≠ c) (had_ne : a ≠ d) (hbc_ne : b ≠ c) (hbd_ne : b ≠ d)
    {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (hspec : ∀ x y : V, G'.Adj x y ↔
      x ≠ y ∧ ((G.Adj x y ∧ ¬ SwitchRemoved a b c d x y) ∨ SwitchAdded a b c d x y))
    {n' k' μ' : ℕ} : ¬ G'.IsSRGWith n' k' 1 μ' := by
  intro hG'
  -- all the distinctness facts, in both orders, so `tauto` can discharge the
  -- `SwitchRemoved` / `SwitchAdded` side conditions below
  have hab_ne : a ≠ b := hab.ne
  have hba_ne : b ≠ a := hab.ne'
  have hcd_ne : c ≠ d := hcd.ne
  have hdc_ne : d ≠ c := hcd.ne'
  have hca_ne : c ≠ a := hac_ne.symm
  have hda_ne : d ≠ a := had_ne.symm
  have hcb_ne : c ≠ b := hbc_ne.symm
  have hdb_ne : d ≠ b := hbd_ne.symm
  -- STEP 1: the apex of the deleted edge {a,b}, and it avoids c and d
  obtain ⟨t, ⟨hta, htb⟩, -⟩ := neighborhood_matching hG hab
  have hta_ne : t ≠ a := hta.ne'
  have htb_ne : t ≠ b := htb.ne'
  have htc_ne : t ≠ c := by intro h; subst h; exact hac hta
  have htd_ne : t ≠ d := by intro h; subst h; exact hbd htb
  have hat_ne : a ≠ t := hta.ne
  have hbt_ne : b ≠ t := htb.ne
  -- `t` is touched by neither deletion nor insertion, so it keeps its
  -- neighbours exactly
  have hG'_t : ∀ x : V, G'.Adj t x ↔ G.Adj t x := by
    intro x
    rw [hspec]
    constructor
    · rintro ⟨-, (⟨h, -⟩ | hnew)⟩
      · exact h
      · exact absurd hnew (by unfold SwitchAdded; tauto)
    · intro h
      exact ⟨h.ne, Or.inl ⟨h, by unfold SwitchRemoved; tauto⟩⟩
  -- the two edges at `t` that survive the switch
  have hG'_at : G'.Adj a t := by
    rw [hspec]; exact ⟨hat_ne, Or.inl ⟨hta, by unfold SwitchRemoved; tauto⟩⟩
  have hG'_bt : G'.Adj b t := by
    rw [hspec]; exact ⟨hbt_ne, Or.inl ⟨htb, by unfold SwitchRemoved; tauto⟩⟩
  -- STEP 2: λ = 1 in `G'` on the surviving edges forces `t ~ c` and `t ~ d`
  have htc : G.Adj t c := by
    obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := neighborhood_matching hG' hG'_at
    have hGw : G.Adj t w := (hG'_t w).mp hw2
    rw [hspec] at hw1
    rcases hw1 with ⟨-, (⟨hGaw, hdel⟩ | hnew)⟩
    · have hwb : w ≠ b := by
        intro h; subst h; exact hdel (Or.inl ⟨rfl, rfl⟩)
      exact absurd (unique_common_of_adj hG hta
        ((mem_commonNeighbors G).mpr ⟨hGaw, hGw⟩)
        ((mem_commonNeighbors G).mpr ⟨hab, htb.symm⟩)) hwb
    · have hwc : w = c := by unfold SwitchAdded at hnew; tauto
      subst hwc; exact hGw
  have htd : G.Adj t d := by
    obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := neighborhood_matching hG' hG'_bt
    have hGw : G.Adj t w := (hG'_t w).mp hw2
    rw [hspec] at hw1
    rcases hw1 with ⟨-, (⟨hGbw, hdel⟩ | hnew)⟩
    · have hwa : w ≠ a := by
        intro h; subst h; exact hdel (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact absurd (unique_common_of_adj hG htb
        ((mem_commonNeighbors G).mpr ⟨hGbw, hGw⟩)
        ((mem_commonNeighbors G).mpr ⟨hab.symm, hta.symm⟩)) hwa
    · have hwd : w = d := by unfold SwitchAdded at hnew; tauto
      subst hwd; exact hGw
  -- STEP 3: {a,b} and {c,d} are two edges of the perfect matching on N(t),
  -- so the cross pairs are non-edges
  have had : ¬ G.Adj a d := by
    intro h
    exact hdb_ne (unique_common_of_adj hG hta
      ((mem_commonNeighbors G).mpr ⟨h, htd⟩)
      ((mem_commonNeighbors G).mpr ⟨hab, htb.symm⟩))
  have hbc : ¬ G.Adj b c := by
    intro h
    exact hca_ne (unique_common_of_adj hG htb
      ((mem_commonNeighbors G).mpr ⟨h, htc⟩)
      ((mem_commonNeighbors G).mpr ⟨hab.symm, hta.symm⟩))
  -- STEP 4: μ = 2 supplies a second common neighbour of the non-adjacent
  -- pair {a,c}, and the switch deletes neither of its two edges
  have hcard : Fintype.card (G.commonNeighbors a c) = 2 := hG.of_not_adj hac_ne hac
  have htmem : t ∈ G.commonNeighbors a c := (mem_commonNeighbors G).mpr ⟨hta, htc.symm⟩
  obtain ⟨⟨s, hsmem⟩, hs_ne⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num)
      (⟨t, htmem⟩ : G.commonNeighbors a c)
  have hst : s ≠ t := fun h => hs_ne (Subtype.ext h)
  rw [mem_commonNeighbors] at hsmem
  obtain ⟨hsa, hsc⟩ := hsmem
  have hsb_ne : s ≠ b := by intro h; subst h; exact hbc hsc.symm
  have hsd_ne : s ≠ d := by intro h; subst h; exact had hsa
  have hG'_ac : G'.Adj a c := by
    rw [hspec]; exact ⟨hac_ne, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have hG'_as : G'.Adj a s := by
    rw [hspec]; exact ⟨hsa.ne, Or.inl ⟨hsa, by unfold SwitchRemoved; tauto⟩⟩
  have hG'_cs : G'.Adj c s := by
    rw [hspec]; exact ⟨hsc.ne, Or.inl ⟨hsc, by unfold SwitchRemoved; tauto⟩⟩
  have hG'_ct : G'.Adj c t := ((hG'_t c).mpr htc).symm
  exact hst (unique_common_of_adj hG' hG'_ac
    ((mem_commonNeighbors G').mpr ⟨hG'_as, hG'_cs⟩)
    ((mem_commonNeighbors G').mpr ⟨hG'_at, hG'_ct⟩))

/-- **No degree-preserving 2-switch on an srg(v,k,1,2) yields an
srg(v,k,1,2)** — log 034's theorem, spec form: `G'` is any graph whose
adjacency is the switch of `G`'s.  Immediate from `switch_not_lambda_one`,
which proves more (the switched graph cannot have λ = 1 at all). -/
theorem not_isSRGWith_of_switch
    (hG : G.IsSRGWith n k 1 2) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (hac_ne : a ≠ c) (had_ne : a ≠ d) (hbc_ne : b ≠ c) (hbd_ne : b ≠ d)
    {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (hspec : ∀ x y : V, G'.Adj x y ↔
      x ≠ y ∧ ((G.Adj x y ∧ ¬ SwitchRemoved a b c d x y) ∨ SwitchAdded a b c d x y)) :
    ¬ G'.IsSRGWith n k 1 2 :=
  switch_not_lambda_one hG hab hcd hac hbd hac_ne had_ne hbc_ne hbd_ne hspec

/-- The same, on the concrete switched graph — the form to quote.  Given an
srg(v,k,1,2) `G` and a valid degree-preserving 2-switch (disjoint edges
`{a,b}`, `{c,d}`; the inserted pairs `{a,c}`, `{b,d}` not already edges),
`switchGraph G a b c d` is NOT an srg(v,k,1,2). -/
theorem not_isSRGWith_switch
    (hG : G.IsSRGWith n k 1 2) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (hac_ne : a ≠ c) (had_ne : a ≠ d) (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) :
    ¬ (switchGraph G a b c d).IsSRGWith n k 1 2 :=
  not_isSRGWith_of_switch hG hab hcd hac hbd hac_ne had_ne hbc_ne hbd_ne
    (switchGraph_adj_iff G a b c d)

end Conway99
