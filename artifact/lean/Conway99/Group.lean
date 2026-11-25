/-
Conway99.Group — the residual symmetry group of the canonical skeleton,
formalized generically: every theorem below is quantified over ALL wreath
elements (π, s) ∈ S₇ × 2⁷ — all 645,120 of them — with structural proofs,
no per-element enumeration.

Conventions (0-indexed here; the Python side is 1-indexed, the export layer
shifts):  N(0) is `Fin 14`; matched pair `a : Fin 7` is `{2a, 2a+1}`;
`pairOf v = v / 2` is the pair (block) of a vertex and `partner v` its
matched partner.  A wreath element is `π : Equiv.Perm (Fin 7)`, permuting
the pairs, together with `s : Fin 7 → Bool`, saying which SOURCE pairs land
with their two members swapped — exactly `symmetry.sigma_on_N` in Python.

Main results:
  * `sigmaEquiv π s : Equiv.Perm (Fin 14)` — every wreath element is a
    genuine permutation of N(0), with explicit computable inverse;
  * `pairOf_sigma` / `sigma_partner` — blocks move by π and partners stay
    partners: the matching is preserved, so these ARE skeleton symmetries;
  * `sigmaEquiv_injective2` — distinct (π, s) give distinct permutations:
    the residual group has (at least) 7!·2⁷ = 645,120 elements;
  * `labelFinset`, `card_labelFinset` — the 84 outside labels;
  * `mem_labelFinset_map`, `labelPerm` — the induced action permutes them;
  * `EdgeSlot`, `card_edgeSlot` — the 3,486 free edge variables;
  * `edgeSlotPerm π s : Equiv.Perm EdgeSlot` — the induced action on edge
    slots is a permutation, for every group element;
  * `sigmaEquiv_mul` / `edgeSlotPerm_comp` — the action respects
    composition (wreath multiplication law), which is exactly the
    mul-closure hypothesis `lexLeader_sound` consumes.
-/
import Mathlib
import Conway99.LexLeader

namespace Conway99

/-! ### Vertices, pairs, partners -/

/-- The matched pair (block) of a vertex of N(0). -/
def pairOf (v : Fin 14) : Fin 7 :=
  ⟨v.val / 2, by have := v.isLt; omega⟩

/-- Second member of its pair? -/
def posIn (v : Fin 14) : Bool := decide (v.val % 2 = 1)

/-- The vertex in pair `a` at position `b`. -/
def member (a : Fin 7) (b : Bool) : Fin 14 :=
  ⟨2 * a.val + (if b then 1 else 0), by have := a.isLt; split <;> omega⟩

/-- The matched partner. -/
def partner (v : Fin 14) : Fin 14 := member (pairOf v) (!posIn v)

@[simp] theorem pairOf_member (a : Fin 7) (b : Bool) : pairOf (member a b) = a := by
  apply Fin.ext
  simp only [pairOf, member]
  cases b <;> simp <;> omega

@[simp] theorem posIn_member (a : Fin 7) (b : Bool) : posIn (member a b) = b := by
  cases b <;> simp [posIn, member] <;> omega

@[simp] theorem member_pairOf_posIn (v : Fin 14) : member (pairOf v) (posIn v) = v := by
  apply Fin.ext
  have := v.isLt
  simp only [member, pairOf, posIn]
  by_cases h : v.val % 2 = 1 <;> simp [h] <;> omega

/-! ### The wreath element as a permutation of N(0) -/

@[simp] theorem perm_inv_apply_self (π : Equiv.Perm (Fin 7)) (a : Fin 7) :
    π⁻¹ (π a) = a := by
  rw [show π⁻¹ = π.symm from rfl]
  exact Equiv.symm_apply_apply π a

@[simp] theorem perm_apply_inv_self (π : Equiv.Perm (Fin 7)) (a : Fin 7) :
    π (π⁻¹ a) = a := by
  rw [show π⁻¹ = π.symm from rfl]
  exact Equiv.apply_symm_apply π a

/-- `symmetry.sigma_on_N`: pair `pairOf v` moves to pair `π (pairOf v)`;
if `s (pairOf v)` the two members land swapped. -/
def sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) : Fin 14 :=
  member (π (pairOf v)) (xor (posIn v) (s (pairOf v)))

/-- Every wreath element is a permutation of N(0), with computable inverse. -/
def sigmaEquiv (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) : Equiv.Perm (Fin 14) where
  toFun := sigma π s
  invFun := sigma π⁻¹ fun a => s (π⁻¹ a)
  left_inv := by
    intro v
    simp only [sigma, pairOf_member, posIn_member, perm_inv_apply_self]
    cases hv : posIn v <;> cases hs : s (pairOf v) <;>
      simp [hv, hs] <;> rw [← hv, member_pairOf_posIn]
  right_inv := by
    intro v
    simp only [sigma, pairOf_member, posIn_member, perm_apply_inv_self]
    cases hv : posIn v <;> cases hs : s (π⁻¹ (pairOf v)) <;>
      simp [hv, hs] <;> rw [← hv, member_pairOf_posIn]

@[simp] theorem sigmaEquiv_apply (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    (v : Fin 14) : sigmaEquiv π s v = sigma π s v := rfl

/-- Blocks move by π. -/
@[simp] theorem pairOf_sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    (v : Fin 14) : pairOf (sigma π s v) = π (pairOf v) := by
  simp [sigma]

@[simp] theorem posIn_sigma (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    (v : Fin 14) : posIn (sigma π s v) = xor (posIn v) (s (pairOf v)) := by
  simp [sigma]

/-- Partners stay partners: the matching is preserved, so `sigmaEquiv π s`
is a symmetry of the skeleton. -/
theorem sigma_partner (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) (v : Fin 14) :
    sigma π s (partner v) = partner (sigma π s v) := by
  simp only [sigma, partner, pairOf_member, posIn_member]
  cases posIn v <;> cases s (pairOf v) <;> rfl

/-- Distinct wreath data give distinct permutations: |residual group| ≥
7!·2⁷ = 645,120. -/
theorem sigmaEquiv_injective2 {π π' : Equiv.Perm (Fin 7)} {s s' : Fin 7 → Bool}
    (h : sigmaEquiv π s = sigmaEquiv π' s') : π = π' ∧ s = s' := by
  have happ : ∀ v, sigma π s v = sigma π' s' v := fun v =>
    congrFun (congrArg (fun (e : Equiv.Perm (Fin 14)) => (e : Fin 14 → Fin 14)) h) v
  constructor
  · apply Equiv.ext
    intro a
    have h1 := congrArg pairOf (happ (member a false))
    simpa using h1
  · funext a
    have h2 := congrArg posIn (happ (member a false))
    simpa using h2

/-- Wreath multiplication law: composition of two elements is the element
with pair-permutations composed and sign vectors xor-twisted. -/
theorem sigma_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool) (v : Fin 14) :
    sigma π₁ s₁ (sigma π₂ s₂ v) =
      sigma (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) v := by
  simp only [sigma, pairOf_member, posIn_member, Equiv.Perm.mul_apply]
  cases posIn v <;> cases s₂ (pairOf v) <;> cases s₁ (π₂ (pairOf v)) <;> rfl

theorem sigmaEquiv_mul (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool) :
    sigmaEquiv π₁ s₁ * sigmaEquiv π₂ s₂ =
      sigmaEquiv (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) := by
  apply Equiv.ext
  intro v
  exact sigma_comp π₁ π₂ s₁ s₂ v

/-! ### The 84 labels and the induced action -/

/-- Two vertices in the same matched pair (equal blocks)? -/
def sameBlock (e : Sym2 (Fin 14)) : Bool :=
  Sym2.lift ⟨fun a b => decide (pairOf a = pairOf b), by
    intro a b
    simp [eq_comm]⟩ e

@[simp] theorem sameBlock_mk (a b : Fin 14) :
    sameBlock s(a, b) = decide (pairOf a = pairOf b) := rfl

/-- The 84 outside labels: unordered pairs of vertices from DISTINCT
matched pairs.  (Distinct blocks forces distinct vertices, so no separate
off-diagonal condition is needed.) -/
def labelFinset : Finset (Sym2 (Fin 14)) :=
  Finset.univ.filter fun e => sameBlock e = false

theorem card_labelFinset : labelFinset.card = 84 := by decide

/-- Injective maps of vertices give injective maps of unordered pairs. -/
theorem sym2_map_isDiag_iff {α β : Type*} {f : α → β} (hf : Function.Injective f)
    (z : Sym2 α) : (z.map f).IsDiag ↔ z.IsDiag := by
  induction z with
  | _ a b =>
    simp only [Sym2.map_pair_eq, Sym2.mk_isDiag_iff]
    exact ⟨fun h => hf h, fun h => congrArg f h⟩

/-- The induced map preserves the label set: blocks move by the injective
π, so distinct blocks stay distinct. -/
theorem mem_labelFinset_map (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    {e : Sym2 (Fin 14)} (he : e ∈ labelFinset) :
    e.map (sigmaEquiv π s) ∈ labelFinset := by
  induction e with
  | _ a b =>
    simp only [labelFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Sym2.map_pair_eq, sameBlock_mk, decide_eq_false_iff_not] at he ⊢
    simp only [sigmaEquiv_apply, pairOf_sigma]
    exact fun hc => he (π.injective hc)

/-- A label, as a type. -/
abbrev Label : Type := {e : Sym2 (Fin 14) // e ∈ labelFinset}

theorem card_label : Fintype.card Label = 84 := by
  rw [Fintype.card_coe]
  exact card_labelFinset

/-- The induced permutation of the 84 labels — for every group element. -/
noncomputable def labelPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    Equiv.Perm Label :=
  Equiv.ofBijective
    (fun l => ⟨l.val.map (sigmaEquiv π s), mem_labelFinset_map π s l.property⟩)
    (Finite.injective_iff_bijective.mp fun l l' h =>
      Subtype.ext (Sym2.map.injective (sigmaEquiv π s).injective
        (congrArg Subtype.val h)))

@[simp] theorem labelPerm_apply_val (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    (l : Label) : (labelPerm π s l).val = l.val.map (sigmaEquiv π s) := rfl

/-! ### The 3,486 edge slots and the induced action -/

/-- An edge slot: an unordered pair of DISTINCT labels — one of the 3,486
free variables of the skeleton instance. -/
abbrev EdgeSlot : Type := {q : Sym2 Label // ¬q.IsDiag}

theorem card_edgeSlot : Fintype.card EdgeSlot = 3486 := by
  have h : Fintype.card EdgeSlot = (Fintype.card Label).choose 2 :=
    Sym2.card_subtype_not_diag
  rw [h, card_label]
  decide

/-- The induced permutation of the 3,486 edge slots — for EVERY element of
the wreath group.  Together with `sigmaEquiv_mul`/`edgeSlotPerm_comp`, the
image of the wreath group in `Equiv.Perm EdgeSlot` is nonempty and closed
under composition: exactly the hypotheses of `lexLeader_sound`. -/
noncomputable def edgeSlotPerm (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool) :
    Equiv.Perm EdgeSlot :=
  Equiv.ofBijective
    (fun q => ⟨q.val.map (labelPerm π s),
      fun hd => q.property ((sym2_map_isDiag_iff (labelPerm π s).injective q.val).mp hd)⟩)
    (Finite.injective_iff_bijective.mp fun q q' h =>
      Subtype.ext (Sym2.map.injective (labelPerm π s).injective
        (congrArg Subtype.val h)))

@[simp] theorem edgeSlotPerm_apply_val (π : Equiv.Perm (Fin 7)) (s : Fin 7 → Bool)
    (q : EdgeSlot) : (edgeSlotPerm π s q).val = q.val.map (labelPerm π s) := rfl

/-- The edge-slot action respects composition. -/
theorem edgeSlotPerm_comp (π₁ π₂ : Equiv.Perm (Fin 7)) (s₁ s₂ : Fin 7 → Bool)
    (q : EdgeSlot) :
    edgeSlotPerm π₁ s₁ (edgeSlotPerm π₂ s₂ q) =
      edgeSlotPerm (π₁ * π₂) (fun a => xor (s₂ a) (s₁ (π₂ a))) q := by
  apply Subtype.ext
  simp only [edgeSlotPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · q.val)
  funext l
  apply Subtype.ext
  simp only [Function.comp_apply, labelPerm_apply_val, Sym2.map_map]
  apply congrArg (Sym2.map · l.val)
  funext v
  simp only [Function.comp_apply, sigmaEquiv_apply]
  exact sigma_comp π₁ π₂ s₁ s₂ v

end Conway99
