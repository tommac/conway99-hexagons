/-
Conway99.LexLeader — machine-checked soundness of lex-leader symmetry
breaking, the argument stated informally in `src/symmetry.py`'s docstring.

Everything here is about boolean position-vectors `Fin n → Bool` (for the
Conway-99 instance, n = 3486 outside-edge slots in the canonical order) and
finite sets of position permutations.

  * `LexLe`        — the exact first-difference order the CNF clauses encode
                     (`false < true`, position 0 most significant).
  * `permApply`    — reading positions through a permutation: Python's X∘P.
  * `lexLeader_sound` — for any nonempty composition-closed finite set S of
                     permutations and any S-invariant constraint C, every
                     satisfying assignment yields one that additionally
                     satisfies ALL lex-leader constraints for S.
  * `lexLeader_equisat` / `lexLeader_mixed_equisat` — satisfiability is
                     therefore EXACTLY preserved when adding lex-leader
                     constraints for any subset of S, including
                     prefix-truncated ones (`PrefixLexLe`), which is what
                     `symbreak.py --prefix-*` emits.

Note the hypotheses: S only needs to be finite, nonempty and closed under
composition (inverses are not needed for soundness), and C only needs to be
preserved in the forward direction by each element of S.  The Conway-99
residual group S₂≀S₇ satisfies far more than this.
-/
import Mathlib

namespace Conway99

variable {n : ℕ}

/-! ### The order -/

/-- `LexLe x y`: `x` is lexicographically ≤ `y`, first-difference form,
`false < true`, position `0` most significant.  This is precisely the
projection semantics of the CNF clauses built by
`symmetry.lex_le_clauses` (verified exhaustively on the Python side by
`test_symmetry.py` T3). -/
def LexLe (x y : Fin n → Bool) : Prop :=
  x = y ∨ ∃ i, x i = false ∧ y i = true ∧ ∀ j, j < i → x j = y j

theorem LexLe.refl (x : Fin n → Bool) : LexLe x x := Or.inl rfl

theorem lexLe_total (x y : Fin n → Bool) : LexLe x y ∨ LexLe y x := by
  by_cases h : x = y
  · exact Or.inl (Or.inl h)
  · have hne : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      exact h (funext fun i => not_not.mp (hemp (Finset.mem_univ i)))
    set D := Finset.univ.filter fun i => x i ≠ y i with hD
    have himem := D.min'_mem hne
    set i := D.min' hne with hi_def
    have hi : x i ≠ y i := by
      have := Finset.mem_filter.mp himem
      exact this.2
    have hpre : ∀ j, j < i → x j = y j := by
      intro j hj
      by_contra hne'
      have hmem : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩
      exact absurd hj (not_lt.mpr (Finset.min'_le D j hmem))
    cases hx : x i <;> cases hy : y i
    · exact absurd (hx.trans hy.symm) hi
    · exact Or.inl (Or.inr ⟨i, hx, hy, hpre⟩)
    · exact Or.inr (Or.inr ⟨i, hy, hx, fun j hj => (hpre j hj).symm⟩)
    · exact absurd (hx.trans hy.symm) hi

theorem lexLe_trans {x y z : Fin n → Bool} (h₁ : LexLe x y) (h₂ : LexLe y z) :
    LexLe x z := by
  rcases h₁ with rfl | ⟨i₁, hx₁, hy₁, hp₁⟩
  · exact h₂
  rcases h₂ with rfl | ⟨i₂, hy₂, hz₂, hp₂⟩
  · exact Or.inr ⟨i₁, hx₁, hy₁, hp₁⟩
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · refine Or.inr ⟨i₁, hx₁, ?_, fun j hj => (hp₁ j hj).trans (hp₂ j (hj.trans hlt))⟩
    rw [← hp₂ i₁ hlt]; exact hy₁
  · subst heq
    rw [hy₁] at hy₂
    simp at hy₂
  · refine Or.inr ⟨i₂, (hp₁ i₂ hgt).trans hy₂, hz₂,
      fun j hj => (hp₁ j (hj.trans hgt)).trans (hp₂ j hj)⟩

/-- Every nonempty finite set of assignments has a lex-minimum. -/
theorem exists_lexLe_min (s : Finset (Fin n → Bool)) :
    s.Nonempty → ∃ y ∈ s, ∀ z ∈ s, LexLe y z := by
  classical
  induction s using Finset.induction_on with
  | empty => rintro ⟨x, hx⟩; simp at hx
  | @insert a t ha ih =>
    intro _
    rcases t.eq_empty_or_nonempty with rfl | ht
    · refine ⟨a, Finset.mem_insert_self a ∅, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact LexLe.refl z
      · simp at hz
    · obtain ⟨y, hy, hmin⟩ := ih ht
      rcases lexLe_total a y with h | h
      · refine ⟨a, Finset.mem_insert_self a t, fun z hz => ?_⟩
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact LexLe.refl z
        · exact lexLe_trans h (hmin z hz)
      · refine ⟨y, Finset.mem_insert_of_mem hy, fun z hz => ?_⟩
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact h
        · exact hmin z hz

/-! ### The action -/

/-- Read positions through a permutation: `permApply p x = x ∘ p`, i.e.
Python's `(X ∘ P)[t] = X[P[t]]` from `symmetry.edge_perm`. -/
def permApply (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => x (p i)

@[simp] theorem permApply_one (x : Fin n → Bool) : permApply 1 x = x := rfl

theorem permApply_permApply (p q : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    permApply q (permApply p x) = permApply (p * q) x := by
  funext i
  simp [permApply, Equiv.Perm.mul_apply]

/-! ### The soundness theorem -/

/-- **Lex-leader soundness.**  Let `S` be a finite, nonempty set of position
permutations closed under composition, and let the constraint predicate `C`
be preserved by every element of `S` (for Conway-99: `C` = "the outside
assignment completes the skeleton to an srg(99,14,1,2)", `S` = the induced
edge-slot action of any subset of S₂≀S₇ closed under composition — in
particular the full group).  Then any satisfying assignment can be replaced
by one that also satisfies EVERY lex-leader constraint `LexLe y (y ∘ p)`,
`p ∈ S`: namely the lex-minimum of its orbit. -/
theorem lexLeader_sound
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop)
    (hC : ∀ p ∈ S, ∀ x, C x → C (permApply p x))
    (x : Fin n → Bool) (hx : C x) :
    ∃ y, C y ∧ ∀ p ∈ S, LexLe y (permApply p y) := by
  classical
  obtain ⟨y, hy_mem, hmin⟩ :=
    exists_lexLe_min (S.image fun p => permApply p x) (hne.image _)
  obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hy_mem
  refine ⟨permApply p₀ x, hC p₀ hp₀ x hx, fun p hp => ?_⟩
  have hmem : permApply p (permApply p₀ x) ∈ S.image fun q => permApply q x := by
    rw [permApply_permApply]
    exact Finset.mem_image_of_mem _ (hmul p₀ hp₀ p hp)
  exact hmin _ hmem

/-- Adding lex-leader constraints for ANY subset `T ⊆ S` preserves
satisfiability exactly.  (This is the license for breaking on 91 structured
elements + a random sample rather than all 645,120.) -/
theorem lexLeader_equisat
    (S T : Finset (Equiv.Perm (Fin n))) (hT : T ⊆ S) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop)
    (hC : ∀ p ∈ S, ∀ x, C x → C (permApply p x)) :
    (∃ x, C x) ↔ ∃ y, C y ∧ ∀ p ∈ T, LexLe y (permApply p y) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hall⟩ := lexLeader_sound S hne hmul C hC x hx
    exact ⟨y, hy, fun p hp => hall p (hT hp)⟩
  · rintro ⟨y, hy, -⟩
    exact ⟨y, hy⟩

/-! ### Prefix truncation -/

/-- The constraint actually emitted under `--prefix-*` truncation: lex
comparison restricted to positions `< L`. -/
def PrefixLexLe (L : ℕ) (x y : Fin n → Bool) : Prop :=
  (∀ i : Fin n, (i : ℕ) < L → x i = y i) ∨
  ∃ i : Fin n, (i : ℕ) < L ∧ x i = false ∧ y i = true ∧ ∀ j, j < i → x j = y j

/-- Truncation is sound: the full lex constraint implies every prefix
constraint. -/
theorem LexLe.prefixLexLe {x y : Fin n → Bool} (h : LexLe x y) (L : ℕ) :
    PrefixLexLe L x y := by
  rcases h with rfl | ⟨i, hx, hy, hp⟩
  · exact Or.inl fun _ _ => rfl
  · by_cases hi : (i : ℕ) < L
    · exact Or.inr ⟨i, hi, hx, hy, hp⟩
    · refine Or.inl fun j hj => hp j ?_
      exact Fin.lt_def.mpr (lt_of_lt_of_le hj (not_lt.mp hi))

/-- A full-length window is no truncation at all. -/
theorem prefixLexLe_top_iff (x y : Fin n → Bool) :
    PrefixLexLe n x y ↔ LexLe x y := by
  constructor
  · rintro (h | ⟨i, _, hx, hy, hp⟩)
    · exact Or.inl (funext fun i => h i i.isLt)
    · exact Or.inr ⟨i, hx, hy, hp⟩
  · exact fun h => h.prefixLexLe n

/-- **The theorem `symbreak.py` runs on.**  A mixed batch of constraints —
each a group element with its own window length, exactly the
`(element, prefix)` list `symbreak.py` assembles — preserves satisfiability
exactly. -/
theorem lexLeader_mixed_equisat
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop)
    (hC : ∀ p ∈ S, ∀ x, C x → C (permApply p x))
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, C x) ↔
      ∃ y, C y ∧ ∀ c ∈ cons, PrefixLexLe c.2 y (permApply c.1 y) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hall⟩ := lexLeader_sound S hne hmul C hC x hx
    exact ⟨y, hy, fun c hc => (hall c.1 (hcons c hc)).prefixLexLe c.2⟩
  · rintro ⟨y, hy, -⟩
    exact ⟨y, hy⟩

/-! ### Arbitrary comparison orders

`campaign.py gen --sb-order` compares positions through a custom order:
position `k`-most-significant is slot `o k`.  The emitted constraint for
element `p` with window `L` relates the sequences `k ↦ y (o k)` and
`k ↦ y (p (o k))` — that is, `PrefixLexLe L (permApply o y)
(permApply (p * o) y)`.  Soundness reduces to the identity-order theorem
by conjugating the whole situation with `o`; this is why ONE order per
instance is sound while mixing orders within an instance is not (each
order has its own orbit minimum). -/

/-- **Order-parameterized soundness — the theorem the v2/v3 per-orbit
instances run on.**  For any single fixed comparison order `o`, adding
the reordered (and possibly truncated) lex-leader constraints for any
subset of `S` preserves satisfiability exactly. -/
theorem lexLeader_mixed_equisat_order
    (o : Equiv.Perm (Fin n))
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop)
    (hC : ∀ p ∈ S, ∀ x, C x → C (permApply p x))
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, C x) ↔
      ∃ y, C y ∧ ∀ c ∈ cons,
        PrefixLexLe c.2 (permApply o y) (permApply (c.1 * o) y) := by
  classical
  have key := lexLeader_mixed_equisat
      (S.image fun p => o⁻¹ * p * o)
      (hne.image _)
      (by
        intro p' hp' q' hq'
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
        refine Finset.mem_image.mpr ⟨p * q, hmul p hp q hq, ?_⟩
        group)
      (fun z => C (permApply o⁻¹ z))
      (by
        intro p' hp' z hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
        show C (permApply o⁻¹ (permApply (o⁻¹ * p * o) z))
        rw [permApply_permApply]
        have h2 := hC p hp (permApply o⁻¹ z) hz
        rw [permApply_permApply] at h2
        have harr : o⁻¹ * p * o * o⁻¹ = o⁻¹ * p := by group
        rw [harr]
        exact h2)
      (cons.map fun c => (o⁻¹ * c.1 * o, c.2))
      (by
        intro c' hc'
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        exact Finset.mem_image.mpr ⟨c.1, hcons c hc, rfl⟩)
  constructor
  · rintro ⟨x, hx⟩
    have hx' : C (permApply o⁻¹ (permApply o x)) := by
      rw [permApply_permApply, mul_inv_cancel, permApply_one]
      exact hx
    obtain ⟨z, hz, hall⟩ := key.mp ⟨permApply o x, hx'⟩
    refine ⟨permApply o⁻¹ z, hz, ?_⟩
    intro c hc
    have hthis := hall (o⁻¹ * c.1 * o, c.2) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    simp only [permApply_permApply]
    rw [inv_mul_cancel, permApply_one, ← mul_assoc]
    exact hthis
  · rintro ⟨y, hy, -⟩
    exact ⟨y, hy⟩

end Conway99
