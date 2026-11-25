/-
Conway99.T2Lex — the B-orbit / t2 layer of the lex-leader symmetry breaking
(design: notes/t2-lex-design.md, §2 "The group action on t2 positions" and
§3 "THE CRUX: t2 variables are DEFINED, not free").

CONTEXT.  `src/c2_instance.py` prescribes the involution σ = (π = id,
s = 1⁷) — the partner swap — and enriches the C2 instance with 861 = C(42,2)
indicator variables `t2(j,k)`, one per unordered pair of σ-orbits on the 84
outside labels ("B-orbits").  The t2-leading lex order of the design puts
those 861 positions in front of the 3,486 edge slots, so the lex-leader
theorems of `LexLeader.lean` have to be instantiated at n = 4,347 over the
COMBINED position set.  That instantiation is free (`LexLeader.lean` is
abstract in `n`, in the position type, in `S` and in `C`); what is NOT free
is the group action on the new positions and the equivariance of the t2
DEFINITION.  This file supplies both.

  * `sigmaLabel` / `sigmaEdge`   — σ's induced action on labels / edge slots,
    with `labelPerm_comm_sigma` / `edgeSlotPerm_comm_sigma`: σ is CENTRAL in
    the wreath group (design §2.1 — the fact machine-checked there for all
    645,120 elements is proved here structurally, for all of them at once).
  * `BOrbit`, `card_bOrbit = 42`  — the σ-orbits on the 84 labels; σ is
    fixed-point-free (`sigmaLabel_ne`), so there are exactly 84/2 = 42.
  * `bOrbitPerm`, `bOrbitPerm_comp` — every wreath element induces a
    permutation of the 42 B-orbits, and the action respects composition.
  * `T2Pos`, `card_t2Pos = 861`, `t2PosPerm`, `t2PosPerm_comp` — the same
    for the 861 t2 positions (unordered non-diagonal pairs of B-orbits).
    Together with `bOrbitPerm_comp` this is the `hmul` hypothesis of
    `lexLeader_sound` / `lexLeader_mixed_equisat(_order)` on the new
    positions: the image of the wreath group is nonempty and closed under
    composition.
  * `blockFull_equivariant` + `e2_eq_blockFull` — THE NEW CONTENT, see below.

THE NEW LEMMA PAIR (design §3.1).  The rep-anchored E2 definition
`t2(a,b) := X(r_a, r_b) ∧ X(r_a, L r_b)` is *not* equivariant on arbitrary
assignments (design §3: 90 of the 91 structured elements flip at least one
B-orbit anchor, and the E2 CLAUSE SET is provably not invariant — there is a
worked counterexample on an element that fixes the t2 position outright).
The repair is to go through the block form:

  * `blockFull X p` — all four edge slots lying over the B-orbit pair `p`
    are true.  `blockFull_equivariant`: this is equivariant UNCONDITIONALLY,
    for every assignment `X`, every wreath element and every position — no
    σ-hypothesis, no anchor choice (it is stated fibrewise over `t2PosOf`,
    so no representative is ever named).
  * `e2_eq_blockFull` — on σ-INVARIANT assignments (`SigmaInvariant`, which
    is exactly what the CNF's `eq_clauses` enforce, see that definition's
    docstring) E2's two-slot conjunction EQUALS the block form.  Stated for
    an arbitrary anchor `u` of one orbit and `v` of the other; the CNF's
    min-index representatives `r_a`, `r_b` are one instance of that, which
    is precisely why the anchor-flip problem disappears.

Together they give the t2 half of the lex-leader hypothesis `hC` on the
combined 4,347-position set: on the σ-invariant set the t2 block of the
position vector transforms by `permApply (t2PosPerm π s)` exactly as the
edge block transforms by `permApply (edgeSlotPerm π s)`
(`blockFull_permApply` below), and the σ-invariant set is itself mapped to
itself (`SigmaInvariant.comp`, from centrality).

WHAT THIS DOES *NOT* DO — stated exactly.  `hC` itself is NOT proved here and
stays at exactly today's epistemic level: that the edge half of the
constraint set (the skeleton + srg conditions + the C2 enrichment families
E1–E4) is preserved by the wreath action is test-verified on the Python side
(`src/test_symmetry.py`, and the design's §3.1a computations) and listed as
informal in `lean/README.md`.  The lemma pair above removes the NEW risk that
the t2 layer introduces — that a DEFINED variable's definition might fail to
be equivariant, which without σ-invariance it demonstrably does — and nothing
else.  It does not improve, and does not degrade, the pre-existing informal
status of `hC`'s edge half.
-/
import Mathlib
import Conway99.Group

namespace Conway99

/-! ### σ, the prescribed involution, as a wreath element -/

/-- The all-ones sign vector: σ is the wreath element `(π = id, s = 1⁷)` of
`src/c2_instance.py` (`pi = tuple(range(7))`, `s = (1,) * 7`). -/
def sigmaSign : Fin 7 → Bool := fun _ => true

/-- On N(0), σ is the partner swap (`Group.partner`). -/
theorem sigma_one_sigmaSign (v : Fin 14) : sigma 1 sigmaSign v = partner v := by
  simp [sigma, sigmaSign, partner]

theorem coe_sigmaEquiv_one_sigmaSign : ⇑(sigmaEquiv 1 sigmaSign) = partner := by
  funext v
  simpa using sigma_one_sigmaSign v

/-- Composing σ AFTER `(π, s)` gives the wreath element `(π, ¬s)`. -/
theorem sigma_sigmaSign_comp_left (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) :
    sigma π s (sigma 1 sigmaSign v) = sigma π (fun a => !(s a)) v := by
  rw [sigma_comp, mul_one]
  simp [sigma, sigmaSign]

/-- Composing σ BEFORE `(π, s)` gives the SAME wreath element `(π, ¬s)`. -/
theorem sigma_sigmaSign_comp_right (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) :
    sigma 1 sigmaSign (sigma π s v) = sigma π (fun a => !(s a)) v := by
  rw [sigma_comp, one_mul]
  simp [sigma, sigmaSign]

/-- **σ is central in the wreath group** (design §2.1), at the level of N(0):
the two composition orders give the same element `(π, ¬s)`. -/
theorem sigma_comm_sigmaSign (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) :
    sigma π s (sigma 1 sigmaSign v) = sigma 1 sigmaSign (sigma π s v) :=
  (sigma_sigmaSign_comp_left π s v).trans (sigma_sigmaSign_comp_right π s v).symm

@[simp] theorem partner_partner (v : Fin 14) : partner (partner v) = v := by
  simp [partner]

theorem partner_ne (v : Fin 14) : partner v ≠ v := by
  intro h
  have h2 := congrArg posIn h
  simp [partner] at h2

/-! ### The induced action on the 84 labels, and σ's label action `L` -/

/-- The label action respects composition (the `labelPerm` analogue of
`edgeSlotPerm_comp`). -/
theorem labelPerm_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool) (l : Label) :
    labelPerm π₁ s₁ (labelPerm π₂ s₂ l) =
      labelPerm (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) l := by
  apply Subtype.ext
  simp only [labelPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · l.val)
  funext v
  simp only [Function.comp_apply, sigmaEquiv_apply]
  exact sigma_comp π₁ π₂ s₁ s₂ v

/-- σ's action on the 84 outside labels: `L` of `src/c2_instance.py`
(`symmetry.outside_perm(symmetry.sigma_on_N(id, 1⁷))`), i.e. the partner swap
applied to both members of a label. -/
def sigmaLabel (l : Label) : Label :=
  ⟨l.val.map partner, by
    have h := mem_labelFinset_map 1 sigmaSign l.property
    rwa [coe_sigmaEquiv_one_sigmaSign] at h⟩

@[simp] theorem sigmaLabel_val (l : Label) : (sigmaLabel l).val = l.val.map partner := rfl

/-- `sigmaLabel` IS the group element σ's induced label action. -/
theorem sigmaLabel_eq_labelPerm (l : Label) : sigmaLabel l = labelPerm 1 sigmaSign l := by
  apply Subtype.ext
  rw [labelPerm_apply_val, coe_sigmaEquiv_one_sigmaSign, sigmaLabel_val]

@[simp] theorem sigmaLabel_sigmaLabel (l : Label) : sigmaLabel (sigmaLabel l) = l := by
  apply Subtype.ext
  simp only [sigmaLabel_val, Sym2.map_map]
  rw [show (partner ∘ partner) = id by funext v; simp]
  simp

/-- σ is FIXED-POINT-FREE on the 84 labels: a label joins two DISTINCT
matched pairs, so it cannot be its own partner-swap. -/
theorem map_partner_ne (e : Sym2 (Fin 14)) (he : sameBlock e = false) : e.map partner ≠ e := by
  induction e with
  | _ a b =>
    simp only [sameBlock_mk, decide_eq_false_iff_not] at he
    simp only [Sym2.map_mk, ne_eq, Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact partner_ne a h1
    · exact he (by rw [← h1]; simp [partner])

theorem sigmaLabel_ne (l : Label) : sigmaLabel l ≠ l := by
  intro h
  have hval : l.val.map partner = l.val := congrArg Subtype.val h
  have he : sameBlock l.val = false := by
    have hp : l.val ∈ labelFinset := l.property
    unfold labelFinset at hp
    exact (Finset.mem_filter.mp hp).2
  exact map_partner_ne l.val he hval

/-- The vertex-level commutation, transported through
`sigma_one_sigmaSign`.  (It is of course also `Group.sigma_partner` — the two
derivations agree, and this one is the design's: it goes through
`sigma_comp`.) -/
theorem partner_comm_sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) :
    sigma π s (partner v) = partner (sigma π s v) := by
  rw [← sigma_one_sigmaSign v, ← sigma_one_sigmaSign (sigma π s v)]
  exact sigma_comm_sigmaSign π s v

/-- **σ commutes with every wreath element** on labels — the design's
`labelPerm_comm_sigma`, a two-line corollary of `sigma_comp`: both
composition orders give `(π, ¬s)`. -/
theorem labelPerm_comm_sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (l : Label) :
    labelPerm π s (sigmaLabel l) = sigmaLabel (labelPerm π s l) := by
  apply Subtype.ext
  simp only [sigmaLabel_val, labelPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · l.val)
  funext v
  simp only [Function.comp_apply, sigmaEquiv_apply]
  exact partner_comm_sigma π s v

/-! ### The 42 B-orbits -/

/-- The σ-orbit relation on labels: `l ≈ l'` iff `l' ∈ {l, σ l}`. -/
instance bOrbitSetoid : Setoid Label where
  r l l' := l' = l ∨ l' = sigmaLabel l
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by rintro l l' (rfl | rfl) <;> simp
      trans := by rintro l l' l'' (rfl | rfl) (rfl | rfl) <;> simp }

theorem bRel_iff {l l' : Label} : l ≈ l' ↔ (l' = l ∨ l' = sigmaLabel l) := Iff.rfl

instance bOrbitDecidableRel : DecidableRel ((· ≈ ·) : Label → Label → Prop) := fun l l' =>
  inferInstanceAs (Decidable (l' = l ∨ l' = sigmaLabel l))

/-- A B-orbit: one of the 42 σ-orbits `{u, L u}` on the 84 outside labels.
`c2_instance.enrich_clauses` indexes them by their min-index representative
`reps[j]`; nothing here ever names a representative. -/
abbrev BOrbit : Type := Quotient bOrbitSetoid

theorem bMk_eq_iff {l l' : Label} :
    (⟦l'⟧ : BOrbit) = ⟦l⟧ ↔ (l' = l ∨ l' = sigmaLabel l) := by
  rw [Quotient.eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by simp)

@[simp] theorem bMk_sigmaLabel (l : Label) : (⟦sigmaLabel l⟧ : BOrbit) = ⟦l⟧ :=
  bMk_eq_iff.mpr (Or.inr rfl)

/-- **42 B-orbits**: 84 labels, and every σ-orbit has exactly two elements
because σ is an involution without fixed points. -/
theorem card_bOrbit : Fintype.card BOrbit = 42 := by
  have hfiber : ∀ b : BOrbit,
      (Finset.univ.filter (fun l : Label => (⟦l⟧ : BOrbit) = b)).card = 2 := by
    intro b
    obtain ⟨l, rfl⟩ := Quotient.exists_rep b
    have hset : (Finset.univ.filter (fun l' : Label => (⟦l'⟧ : BOrbit) = ⟦l⟧))
        = ({l, sigmaLabel l} : Finset Label) := by
      ext l'
      simp [bMk_eq_iff]
    rw [hset, Finset.card_insert_of_notMem (by simp [Ne.symm (sigmaLabel_ne l)]),
      Finset.card_singleton]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun l : Label => (⟦l⟧ : BOrbit)) (s := (Finset.univ : Finset Label))
    (t := (Finset.univ : Finset BOrbit)) (by intro x _; simp)
  simp only [hfiber, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hsum
  rw [card_label] at hsum
  change Fintype.card (Quotient bOrbitSetoid) = 42
  omega

/-- The induced permutation of the 42 B-orbits — for EVERY wreath element.
Well defined precisely because σ is central (`labelPerm_comm_sigma`). -/
noncomputable def bOrbitPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    Equiv.Perm BOrbit :=
  Equiv.ofBijective
    (Quotient.map (labelPerm π s) (by
      rintro l l' (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (labelPerm_comm_sigma π s l)))
    (Finite.injective_iff_bijective.mp (by
      intro b b'
      refine Quotient.inductionOn₂ b b' (fun l l' h => ?_)
      simp only [Quotient.map_mk] at h
      rw [bMk_eq_iff] at h ⊢
      rcases h with h | h
      · exact Or.inl ((labelPerm π s).injective h)
      · exact Or.inr ((labelPerm π s).injective (by rw [h, labelPerm_comm_sigma]))))

@[simp] theorem bOrbitPerm_mk (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (l : Label) :
    bOrbitPerm π s ⟦l⟧ = ⟦labelPerm π s l⟧ := rfl

/-- The B-orbit action respects composition (wreath multiplication law). -/
theorem bOrbitPerm_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool)
    (b : BOrbit) :
    bOrbitPerm π₁ s₁ (bOrbitPerm π₂ s₂ b) =
      bOrbitPerm (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) b := by
  refine Quotient.inductionOn b (fun l => ?_)
  simp [labelPerm_comp]

/-! ### The 861 t2 positions -/

/-- A t2 position: an unordered pair of DISTINCT B-orbits — one of the 861
indicator variables `t2(j,k)` of `c2_instance.enrich_clauses`. -/
abbrev T2Pos : Type := {p : Sym2 BOrbit // ¬p.IsDiag}

theorem card_t2Pos : Fintype.card T2Pos = 861 := by
  have h : Fintype.card T2Pos = (Fintype.card BOrbit).choose 2 :=
    Sym2.card_subtype_not_diag
  rw [h, card_bOrbit]
  decide

/-- The induced permutation of the 861 t2 positions — for EVERY wreath
element.  With `t2PosPerm_comp` this is exactly the `hne`/`hmul` package
`lexLeader_sound` consumes, now on the t2 half of the position set. -/
noncomputable def t2PosPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    Equiv.Perm T2Pos :=
  Equiv.ofBijective
    (fun p => ⟨p.val.map (bOrbitPerm π s),
      fun hd => p.property ((sym2_map_isDiag_iff (bOrbitPerm π s).injective p.val).mp hd)⟩)
    (Finite.injective_iff_bijective.mp fun _ _ h =>
      Subtype.ext (Sym2.map.injective (bOrbitPerm π s).injective
        (congrArg Subtype.val h)))

@[simp] theorem t2PosPerm_apply_val (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (p : T2Pos) :
    (t2PosPerm π s p).val = p.val.map (bOrbitPerm π s) := rfl

/-- The t2-position action respects composition. -/
theorem t2PosPerm_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool) (p : T2Pos) :
    t2PosPerm π₁ s₁ (t2PosPerm π₂ s₂ p) =
      t2PosPerm (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) p := by
  apply Subtype.ext
  simp only [t2PosPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · p.val)
  funext b
  simp only [Function.comp_apply]
  exact bOrbitPerm_comp π₁ π₂ s₁ s₂ b

/-! ### σ on edge slots, and σ-invariant assignments -/

/-- σ's action on the 3,486 edge slots. -/
noncomputable def sigmaEdge : Equiv.Perm EdgeSlot := edgeSlotPerm 1 sigmaSign

@[simp] theorem sigmaEdge_val (q : EdgeSlot) : (sigmaEdge q).val = q.val.map sigmaLabel := by
  simp only [sigmaEdge, edgeSlotPerm_apply_val]
  exact congrArg (Sym2.map · q.val) (funext fun l => (sigmaLabel_eq_labelPerm l).symm)

/-- σ commutes with every wreath element on edge slots (centrality again). -/
theorem edgeSlotPerm_comm_sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (q : EdgeSlot) :
    edgeSlotPerm π s (sigmaEdge q) = sigmaEdge (edgeSlotPerm π s q) := by
  apply Subtype.ext
  simp only [sigmaEdge_val, edgeSlotPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · q.val)
  funext l
  simp only [Function.comp_apply]
  exact labelPerm_comm_sigma π s l

/-- σ-invariance of an edge assignment.

This is EXACTLY what the CNF's equality clauses enforce: `c2_instance.py`
computes the induced edge permutation `P = symmetry.element_edge_perm(id, 1⁷)`,
takes its 1,722 two-element orbits `{t, P t}` and emits, for each, the pair
`[-x_t, x_{P t}], [x_t, -x_{P t}]` — i.e. `X (P t) = X t` on every moved slot.
On the 42 P-FIXED slots (the E1 slots `{u, L u}`) the same equation holds
trivially, so this ∀-form is equivalent to that clause set, not stronger. -/
def SigmaInvariant (X : EdgeSlot → Bool) : Prop := ∀ q : EdgeSlot, X (sigmaEdge q) = X q

/-- The σ-invariant set is mapped to itself by the wreath action — the first
bullet of design §3.1a, and what makes the equivariance argument close. -/
theorem SigmaInvariant.comp {X : EdgeSlot → Bool} (hX : SigmaInvariant X)
    (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    SigmaInvariant (fun q => X (edgeSlotPerm π s q)) := by
  intro q
  simp only [edgeSlotPerm_comm_sigma]
  exact hX (edgeSlotPerm π s q)

/-! ### The projection edge slot ↦ t2 position, and the block form -/

/-- The B-orbit pair an edge slot lies over.  (It is DIAGONAL exactly on the
42 σ-fixed slots `{u, L u}` — E1's cocliques — and non-diagonal on the other
3,444, which fall into 861 fibres of four.) -/
def t2PosOf (q : EdgeSlot) : Sym2 BOrbit := q.val.map (fun l => ⟦l⟧)

/-- The fibre of `t2PosOf` over the position of `{⟦u⟧, ⟦v⟧}` is exactly the
FOUR slots `{u,v}, {u,σv}, {σu,v}, {σu,σv}` — the block of design §3.1
(`A`, `B`, `C`, `D`). -/
theorem map_bMk_eq_iff (e : Sym2 Label) (u v : Label) :
    e.map (fun l => (⟦l⟧ : BOrbit)) = s(⟦u⟧, ⟦v⟧) ↔
      e = s(u, v) ∨ e = s(u, sigmaLabel v) ∨
      e = s(sigmaLabel u, v) ∨ e = s(sigmaLabel u, sigmaLabel v) := by
  induction e with
  | _ w z =>
    simp only [Sym2.map_mk, Sym2.eq_iff, bMk_eq_iff]
    tauto

/-- Non-vacuity guard: every t2 position really is a pair of DISTINCT
B-orbits with genuine label anchors, so `e2_eq_blockFull` below applies to
all 861 of them (and its `hid`/`hsw`/`hp` hypotheses are satisfiable). -/
theorem exists_anchors (e : Sym2 BOrbit) (he : ¬e.IsDiag) :
    ∃ u v : Label, e = s(⟦u⟧, ⟦v⟧) ∧ (⟦u⟧ : BOrbit) ≠ ⟦v⟧ := by
  revert he
  induction e with
  | _ a b =>
    intro he
    obtain ⟨u, rfl⟩ := Quotient.exists_rep a
    obtain ⟨v, rfl⟩ := Quotient.exists_rep b
    exact ⟨u, v, rfl, by simpa using he⟩

theorem t2PosOf_eq_iff (q : EdgeSlot) (u v : Label) :
    t2PosOf q = s(⟦u⟧, ⟦v⟧) ↔
      q.val = s(u, v) ∨ q.val = s(u, sigmaLabel v) ∨
      q.val = s(sigmaLabel u, v) ∨ q.val = s(sigmaLabel u, sigmaLabel v) :=
  map_bMk_eq_iff q.val u v

/-- The projection is equivariant: it intertwines the edge-slot action with
the B-orbit action.  (Functoriality of `Sym2.map`; no hypotheses.) -/
theorem t2PosOf_edgeSlotPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (q : EdgeSlot) :
    t2PosOf (edgeSlotPerm π s q) = (t2PosOf q).map (bOrbitPerm π s) := by
  simp only [t2PosOf, edgeSlotPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · q.val)
  funext l
  simp

/-- **The block form** of design §3.1: all four edge slots between the two
B-orbits of `p` are true.  Stated fibrewise, so it is manifestly symmetric in
the two orbits and independent of any anchor/representative choice. -/
def blockFull (X : EdgeSlot → Bool) (p : T2Pos) : Prop :=
  ∀ q : EdgeSlot, t2PosOf q = p.val → X q = true

/-- **LEMMA 1 (design §3.1) — the block form is UNCONDITIONALLY equivariant.**
For ANY assignment `X`, ANY wreath element `(π, s)` and ANY t2 position `p`:
pulling `X` back along the edge-slot action and evaluating the block form at
`p` is the same as evaluating the block form of `X` at the moved position.
No σ-invariance is needed, and no representative is chosen. -/
theorem blockFull_equivariant (X : EdgeSlot → Bool) (π : Equiv.Perm (Fin 7))
    (s : Fin 7 → Bool) (p : T2Pos) :
    blockFull (fun q => X (edgeSlotPerm π s q)) p ↔ blockFull X (t2PosPerm π s p) := by
  constructor
  · intro h q hq
    have hpre : t2PosOf ((edgeSlotPerm π s).symm q) = p.val := by
      apply Sym2.map.injective (bOrbitPerm π s).injective
      rw [← t2PosOf_edgeSlotPerm, Equiv.apply_symm_apply, hq, t2PosPerm_apply_val]
    have := h ((edgeSlotPerm π s).symm q) hpre
    simpa using this
  · intro h q hq
    refine h (edgeSlotPerm π s q) ?_
    rw [t2PosOf_edgeSlotPerm, hq, t2PosPerm_apply_val]

/-- **LEMMA 2 (design §3.1) — the E2 bridge, and it NEEDS σ-invariance.**
`xid` is the slot `{u, v}` and `xsw` the slot `{u, σ v}`: exactly the two
slots `c2_instance.enrich_clauses` uses to define `t2(j,k)`, with `u` the
anchor in one orbit and `v` the anchor in the other (the CNF takes the
min-index representatives `r_a`, `r_b`; ANY anchors work here, which is what
kills the anchor-flip problem of design §3).  On a σ-invariant assignment
E2's conjunction equals the block form.

`p` is a t2 POSITION, i.e. non-diagonal, so `hp` already carries
`⟦u⟧ ≠ ⟦v⟧`: `u` and `v` lie in different B-orbits, and no separate
hypothesis to that effect is needed.

Without `hX` the statement is FALSE — the design's §3 counterexample is an
element that fixes the t2 position and still moves `{u,v}` off E2's two
anchor slots — so the σ-equality clauses are load-bearing for the soundness
of the whole t2 lex layer. -/
theorem e2_eq_blockFull (X : EdgeSlot → Bool) (hX : SigmaInvariant X) {u v : Label}
    (xid xsw : EdgeSlot) (hid : xid.val = s(u, v)) (hsw : xsw.val = s(u, sigmaLabel v))
    (p : T2Pos) (hp : p.val = s(⟦u⟧, ⟦v⟧)) :
    (X xid = true ∧ X xsw = true) ↔ blockFull X p := by
  constructor
  · rintro ⟨h1, h2⟩ q hq
    rw [hp, t2PosOf_eq_iff] at hq
    have hxid : q.val = s(u, v) → X q = true := by
      intro h; rw [show q = xid from Subtype.ext (h.trans hid.symm)]; exact h1
    have hxsw : q.val = s(u, sigmaLabel v) → X q = true := by
      intro h; rw [show q = xsw from Subtype.ext (h.trans hsw.symm)]; exact h2
    rcases hq with h | h | h | h
    · exact hxid h
    · exact hxsw h
    · -- {σu, v} = σ · {u, σv}: use σ-invariance to fall back on xsw
      have : q = sigmaEdge xsw := by
        apply Subtype.ext
        rw [h, sigmaEdge_val, hsw]
        simp [Sym2.eq_iff]
      rw [this, hX xsw]
      exact h2
    · -- {σu, σv} = σ · {u, v}
      have : q = sigmaEdge xid := by
        apply Subtype.ext
        rw [h, sigmaEdge_val, hid]
        simp [Sym2.eq_iff]
      rw [this, hX xid]
      exact h1
  · intro h
    refine ⟨h xid ?_, h xsw ?_⟩
    · rw [hp, t2PosOf_eq_iff]; exact Or.inl hid
    · rw [hp, t2PosOf_eq_iff]; exact Or.inr (Or.inl hsw)

/-! ### Non-vacuity, and that `hX` cannot be dropped

`blockFull` is a bounded ∀.  If some fibre of `t2PosOf` were EMPTY, then
`blockFull X p` would hold vacuously for that `p` and every `X`, and
`blockFull_equivariant` would be a tautology about nothing.  It is not:
every fibre is inhabited, and `blockFull` is falsifiable.  Then
`e2_needs_sigmaInvariant` shows the σ-hypothesis of `e2_eq_blockFull` is
load-bearing IN LEAN, not merely in the Python negative control — the
design's §3 counterexample, proved for EVERY t2 position at once. -/

/-- Every t2 position has an edge slot lying over it. -/
theorem exists_slot_over (p : T2Pos) : ∃ q : EdgeSlot, t2PosOf q = p.val := by
  obtain ⟨u, v, hp, hne⟩ := exists_anchors p.val p.property
  have huv : u ≠ v := fun h => hne (by rw [h])
  refine ⟨⟨s(u, v), by simpa using huv⟩, ?_⟩
  rw [hp]
  rfl

/-- `blockFull` is a falsifiable predicate: the all-false assignment fails it
at every position.  (With `exists_slot_over`, this rules out the degenerate
reading of `blockFull_equivariant`.) -/
theorem blockFull_falsifiable (p : T2Pos) : ¬ blockFull (fun _ => false) p := by
  intro h
  obtain ⟨q, hq⟩ := exists_slot_over p
  simpa using h q hq

/-- **`hX` CANNOT BE DROPPED from `e2_eq_blockFull`** (design §3, §3.2).  For
EVERY t2 position there are anchors `u`, `v`, an `xid`/`xsw` pair satisfying
that lemma's `hid`/`hsw`/`hp` hypotheses exactly, and an assignment on which
E2's conjunction is TRUE while the block form is FALSE — the witness fails
`SigmaInvariant`, as it must.  Hence the σ-equality clauses of
`c2_instance.py` are load-bearing for the soundness of the t2 lex layer. -/
theorem e2_needs_sigmaInvariant (p : T2Pos) :
    ∃ (X : EdgeSlot → Bool) (u v : Label) (xid xsw : EdgeSlot),
      xid.val = s(u, v) ∧ xsw.val = s(u, sigmaLabel v) ∧ p.val = s(⟦u⟧, ⟦v⟧) ∧
      X xid = true ∧ X xsw = true ∧ ¬ blockFull X p := by
  obtain ⟨u, v, hp, hne⟩ := exists_anchors p.val p.property
  have huv : u ≠ v := fun h => hne (by rw [h])
  have husv : u ≠ sigmaLabel v := fun h => hne (by rw [h]; simp)
  have hsuv : sigmaLabel u ≠ v := fun h => hne (by rw [← h]; simp)
  refine ⟨fun q => decide (q.val = s(u, v) ∨ q.val = s(u, sigmaLabel v)),
    u, v, ⟨s(u, v), by simpa using huv⟩, ⟨s(u, sigmaLabel v), by simpa using husv⟩,
    rfl, rfl, hp, by simp, by simp, ?_⟩
  intro h
  -- the slot {σu, v} lies in the fibre but is neither of E2's two anchor slots
  have hq : t2PosOf (⟨s(sigmaLabel u, v), by simpa using hsuv⟩ : EdgeSlot) = p.val := by
    rw [hp]
    simp [t2PosOf]
  have := h _ hq
  simp only [decide_eq_true_eq, Sym2.eq_iff] at this
  rcases this with (⟨h1, -⟩ | ⟨-, h2⟩) | (⟨h1, -⟩ | ⟨-, h2⟩)
  · exact sigmaLabel_ne u h1
  · exact huv h2.symm
  · exact sigmaLabel_ne u h1
  · exact huv h2.symm

/-! ### The corollary the lex layer consumes -/

instance blockFullDecidable (X : EdgeSlot → Bool) (p : T2Pos) : Decidable (blockFull X p) :=
  inferInstanceAs (Decidable (∀ q : EdgeSlot, t2PosOf q = p.val → X q = true))

/-- The t2 half of the position vector: the block-form indicator, which on
σ-invariant assignments is E2's `t2` (`e2_eq_blockFull`). -/
def t2Vec (X : EdgeSlot → Bool) (p : T2Pos) : Bool := decide (blockFull X p)

/-- **The `hC` shape** on the t2 half: reading the t2 vector of the pulled-back
assignment at `p` is reading the t2 vector of `X` at the moved position —
i.e. `t2Vec (permApply P_g X) = permApply Q_g (t2Vec X)` in the notation of
`LexLeader.permApply`.  Immediate from Lemma 1, hence also unconditional;
`e2_eq_blockFull` is what identifies `t2Vec` with the CNF's `t2` variables on
the σ-invariant set, and `SigmaInvariant.comp` is what keeps the image inside
that set. -/
theorem t2Vec_equivariant (X : EdgeSlot → Bool) (π : Equiv.Perm (Fin 7))
    (s : Fin 7 → Bool) (p : T2Pos) :
    t2Vec (fun q => X (edgeSlotPerm π s q)) p = t2Vec X (t2PosPerm π s p) := by
  simp only [t2Vec, decide_eq_decide]
  exact blockFull_equivariant X π s p

/-- `e2_eq_blockFull` in the design's Boolean shape: on a σ-invariant
assignment the CNF's E2 conjunction IS the t2 vector entry. -/
theorem e2_and_eq_t2Vec (X : EdgeSlot → Bool) (hX : SigmaInvariant X) {u v : Label}
    (xid xsw : EdgeSlot) (hid : xid.val = s(u, v)) (hsw : xsw.val = s(u, sigmaLabel v))
    (p : T2Pos) (hp : p.val = s(⟦u⟧, ⟦v⟧)) :
    (X xid && X xsw) = t2Vec X p := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, t2Vec, decide_eq_true_iff]
  exact e2_eq_blockFull X hX xid xsw hid hsw p hp

/-! ### The COMBINED 4,347-position frame

`lexLeader_mixed_equisat(_order)` consumes a group of permutations of the
WHOLE position set and a `C` on the whole position vector.  The design's
position set is the 861 t2 positions followed by the 3,486 edge slots
(`c2_instance.t2_combined_order`), i.e. `T2Pos ⊕ EdgeSlot`.  The two halves
above are assembled here, so the `hne`/`hmul` package and the `hC` shape are
available on the combined type rather than one half at a time.  What is still
NOT in Lean is the numbering: the bijection `T2Pos ⊕ EdgeSlot ≃ Fin 4347`
realised by `c2_instance.t2_pairs()` ++ `symmetry.edge_positions()` and the
CNF variable ids it indexes — informal item 6b of `lean/README.md`. -/

theorem card_combined : Fintype.card (T2Pos ⊕ EdgeSlot) = 4347 := by
  rw [Fintype.card_sum, card_t2Pos, card_edgeSlot]

/-- The combined position permutation of a wreath element: `Q_g` on the t2
half, `P_g` on the edge half — the SAME element on both, which is exactly
`c2_instance.combined_perm`. -/
noncomputable def combPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    Equiv.Perm (T2Pos ⊕ EdgeSlot) :=
  (t2PosPerm π s).sumCongr (edgeSlotPerm π s)

@[simp] theorem combPerm_inl (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (p : T2Pos) :
    combPerm π s (Sum.inl p) = Sum.inl (t2PosPerm π s p) := rfl

@[simp] theorem combPerm_inr (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (q : EdgeSlot) :
    combPerm π s (Sum.inr q) = Sum.inr (edgeSlotPerm π s q) := rfl

/-- **`hmul` on the combined positions.**  The image of the wreath group in
`Equiv.Perm (T2Pos ⊕ EdgeSlot)` is closed under composition — both halves
transform under the same wreath multiplication law, so the combined map is a
homomorphism, not just two unrelated actions. -/
theorem combPerm_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool)
    (z : T2Pos ⊕ EdgeSlot) :
    combPerm π₁ s₁ (combPerm π₂ s₂ z) =
      combPerm (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) z := by
  cases z with
  | inl p => simpa using t2PosPerm_comp π₁ π₂ s₁ s₂ p
  | inr q => simpa using edgeSlotPerm_comp π₁ π₂ s₁ s₂ q

/-- The combined position vector of an edge assignment: the block-form t2
indicators on the first half, `X` itself on the second. -/
def combVec (X : EdgeSlot → Bool) : T2Pos ⊕ EdgeSlot → Bool := Sum.elim (t2Vec X) X

/-- **The `hC` shape on the FULL 4,347-position vector**: pulling the edge
assignment back along `P_g` and reading the combined vector is reading the
combined vector of `X` at the `combPerm`-moved position, i.e.
`combVec (permApply P_g X) = permApply (combPerm g) (combVec X)` in
`LexLeader.permApply` notation.  Unconditional (it inherits Lemma 1);
`e2_and_eq_t2Vec` is what identifies the first half with the CNF's `t2`
variables, and needs σ-invariance. -/
theorem combVec_equivariant (X : EdgeSlot → Bool) (π : Equiv.Perm (Fin 7))
    (s : Fin 7 → Bool) (z : T2Pos ⊕ EdgeSlot) :
    combVec (fun q => X (edgeSlotPerm π s q)) z = combVec X (combPerm π s z) := by
  cases z with
  | inl p => exact t2Vec_equivariant X π s p
  | inr q => rfl

end Conway99
