/-
Conway99.Matchings — machine-checked completeness of the perfect-matching
enumeration that generates the cube cover at EVERY level of the SAT campaign.

`src/cubes.py:matchings` enumerates the perfect matchings of a 12-element
block (S1 at level 1, S2 inside each per-orbit instance at level 2, S_a
blocks at level ≥ 3) by the classic recursion: pair the head with each later
element, recurse on the rest.  The campaign's soundness rests on the claim
"the 10,395 cubes cover every model": constraint family F2 forces each block
to induce SOME perfect matching, so the instance is UNSAT iff every cube is
UNSAT — but only if the enumeration really lists EVERY perfect matching,
exactly once.  That is what this file proves, about a Lean function
`matchingsL` that mirrors the Python generator line for line.

  * `pickEach`      — the loop `for i in range(1, len(elems))`: every way to
                      pick one element out of a list, with what remains.
  * `matchingsL`    — the enumerator itself (head pairs with each later
                      element; recurse on the rest), a structural mirror of
                      `cubes.py:matchings`.
  * `length_matchingsL` — a list of length 2k yields exactly (2k−1)!!
                      entries (no Nodup needed: the count is length-only);
                      `length_matchingsL_twelve` / `_range12` instantiate
                      12 ↦ 10,395, the constant `cubes.py:all_cubes` asserts.
  * `perm_of_mem_matchingsL` — SOUNDNESS: every entry is a perfect matching
                      of the input list: flattening its pairs gives a
                      permutation of the input (each element used exactly
                      once, with multiplicity).
  * `nodup_matchingsL` — no matching is listed twice (Nodup input).
  * `eq_of_sym2_perm_matchingsL` — distinctness holds at the CUBE level too:
                      two entries denoting the same multiset of unordered
                      pairs are the same entry, so no cube id repeats a cube.
  * `matchingsL_complete` — COMPLETENESS, the load-bearing theorem: ANY
                      perfect matching of a Nodup list (any pair list whose
                      flattened components are a permutation of it) appears
                      in `matchingsL`, up to the order of the pairs and the
                      orientation within each pair (same list of unordered
                      `Sym2` pairs, up to permutation).  This is the "the
                      cubes cover the space" step of the campaign argument.

What is certified for the SAT campaign: IF a total assignment satisfies F2
on a block (i.e. the block induces a perfect matching in the outside graph),
THEN that matching — as a set of unordered edges, which is all a cube's 66
literals mention — is one of the enumerated ones, so the assignment lies
inside one of the enumerated cubes; refuting all 10,395 cubes therefore
refutes the instance, with nothing falling between the cubes.  The remaining
glue (the Python `matchings` computes the same list as `matchingsL`) is a
line-by-line code correspondence, checked informally; see lean/README.md.
-/
import Mathlib

namespace Conway99

open List

variable {α : Type*}

/-! ### Picking one element out of a list -/

/-- `pickEach l` lists, in position order, every way to pick one element of
`l` together with the list that remains — `(l[i], l with slot i deleted)`
for `i = 0, 1, …`.  Applied to the tail, this is exactly the loop
`for i in range(1, len(elems)): b = elems[i]; rest = elems[1:i]+elems[i+1:]`
in `cubes.py:matchings`. -/
def pickEach : List α → List (α × List α)
  | [] => []
  | b :: r => (b, r) :: (pickEach r).map fun p => (p.1, b :: p.2)

/-- Membership characterization: picking `c` leaves `rest` iff the list
splits as `l₁ ++ c :: l₂` with `rest = l₁ ++ l₂`. -/
theorem mem_pickEach {l : List α} {c : α} {rest : List α} :
    (c, rest) ∈ pickEach l ↔ ∃ l₁ l₂, l = l₁ ++ c :: l₂ ∧ rest = l₁ ++ l₂ := by
  induction l generalizing rest with
  | nil => simp [pickEach]
  | cons b r ih =>
    simp only [pickEach, mem_cons, mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨hc, hrest⟩ | ⟨p, hp, hc, hrest⟩)
      · exact ⟨[], r, by simp [hc], by simp [hrest]⟩
      · subst hc
        subst hrest
        obtain ⟨l₁, l₂, hsplit, hrest2⟩ := ih.mp hp
        exact ⟨b :: l₁, l₂, by simp [hsplit], by simp [hrest2]⟩
    · rintro ⟨l₁, l₂, hsplit, hrest⟩
      cases l₁ with
      | nil =>
        simp only [nil_append] at hsplit hrest
        injection hsplit with h1 h2
        subst h1
        subst h2
        exact Or.inl ⟨rfl, hrest⟩
      | cons b' l₁' =>
        simp only [cons_append, cons.injEq] at hsplit
        obtain ⟨rfl, hsplit⟩ := hsplit
        refine Or.inr ⟨(c, l₁' ++ l₂),
          ih.mpr ⟨l₁', l₂, hsplit, rfl⟩, rfl, ?_⟩
        simp [hrest]

/-- The first components of `pickEach l` are exactly `l`, in order.
(Hence on a Nodup list all picks are at distinct elements — the fact that
makes the enumeration duplicate-free.) -/
theorem map_fst_pickEach (l : List α) : (pickEach l).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons b r ih =>
    simp only [pickEach, map_cons, map_map]
    congr 1

/-- Picking one element shortens the list by exactly one. -/
theorem length_of_mem_pickEach {l rest : List α} {c : α}
    (hp : (c, rest) ∈ pickEach l) : rest.length + 1 = l.length := by
  obtain ⟨l₁, l₂, rfl, rfl⟩ := mem_pickEach.mp hp
  simp only [length_append, length_cons]
  omega

/-- What remains after a pick is a sublist of the original (so Nodup is
inherited). -/
theorem sublist_of_mem_pickEach {l : List α} {p : α × List α}
    (hp : p ∈ pickEach l) : p.2 <+ l := by
  obtain ⟨c, rest⟩ := p
  obtain ⟨l₁, l₂, rfl, rfl⟩ := mem_pickEach.mp hp
  exact (sublist_cons_self c l₂).append_left l₁

/-- The picked element back on top of the remainder is a permutation of
the original list. -/
theorem cons_perm_of_mem_pickEach {l : List α} {p : α × List α}
    (hp : p ∈ pickEach l) : p.1 :: p.2 ~ l := by
  obtain ⟨c, rest⟩ := p
  obtain ⟨l₁, l₂, rfl, rfl⟩ := mem_pickEach.mp hp
  exact perm_middle.symm

/-- Conversely, every element of `l` is picked at least once. -/
theorem exists_mem_pickEach_of_mem {l : List α} {b : α} (hb : b ∈ l) :
    ∃ rest, (b, rest) ∈ pickEach l := by
  obtain ⟨l₁, l₂, rfl⟩ := append_of_mem hb
  exact ⟨l₁ ++ l₂, mem_pickEach.mpr ⟨l₁, l₂, rfl, rfl⟩⟩

/-! ### The enumerator -/

/-- The perfect-matching enumerator, a structural mirror of
`cubes.py:matchings`: the empty list has the one empty matching; otherwise
the head `a` pairs with each later element `b` in turn (that is the
`pickEach` of the tail) and we recurse on what remains.  The `attach` is
Lean bookkeeping only — it carries the membership fact `p ∈ pickEach t`
that justifies termination (the remainder is shorter); the clean unfolding
equation `matchingsL_cons` below erases it. -/
def matchingsL : List α → List (List (α × α))
  | [] => [[]]
  | a :: t =>
    (pickEach t).attach.flatMap fun p =>
      (matchingsL p.1.2).map fun m => (a, p.1.1) :: m
termination_by l => l.length
decreasing_by
  have h := length_of_mem_pickEach (l := t) (c := p.1.1) (rest := p.1.2) p.2
  simp only [length_cons]
  omega

@[simp] theorem matchingsL_nil : matchingsL ([] : List α) = [[]] := by
  simp [matchingsL]

/-- The clean unfolding equation (the `attach` of the definition erased):
head `a` pairs with each pick from the tail, recurse on the remainder. -/
theorem matchingsL_cons (a : α) (t : List α) :
    matchingsL (a :: t) =
      (pickEach t).flatMap fun p =>
        (matchingsL p.2).map fun m => (a, p.1) :: m := by
  conv_rhs => rw [← attach_map_subtype_val (pickEach t), flatMap_map]
  simp [matchingsL]

/-! ### Counting: (2k−1)!! entries -/

/-- Sum of a map that is constant on the list. -/
private theorem sum_map_const_on {β : Type*} {l : List β} {f : β → ℕ} {c : ℕ}
    (h : ∀ b ∈ l, f b = c) : (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons b r ih =>
    have hb := h b mem_cons_self
    have hr := ih fun x hx => h x (mem_cons_of_mem b hx)
    simp only [map_cons, sum_cons, length_cons, hb, hr]
    ring

/-- **The count.**  A list of length `2k` has exactly `(2k−1)!!` entries in
`matchingsL` — no Nodup hypothesis needed, the count depends on the length
alone.  (For odd lengths the enumeration is empty, as it should be.)
This is the arithmetic behind `cubes.py:all_cubes`'s
`assert len(cubes) == 10395`. -/
theorem length_matchingsL (k : ℕ) :
    ∀ l : List α, l.length = 2 * k →
      (matchingsL l).length = Nat.doubleFactorial (2 * k - 1) := by
  induction k with
  | zero =>
    intro l hl
    obtain rfl : l = [] := length_eq_zero_iff.mp (by omega)
    simp [Nat.doubleFactorial]
  | succ k ih =>
    intro l hl
    obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
      cases l with
      | nil => simp only [length_nil] at hl; omega
      | cons a t => exact ⟨a, t, rfl⟩
    have ht : t.length = 2 * k + 1 := by
      simp only [length_cons] at hl
      omega
    rw [matchingsL_cons]
    simp only [length_flatMap]
    have hconst : ∀ p ∈ pickEach t,
        ((matchingsL p.2).map fun m => (a, p.1) :: m).length =
          Nat.doubleFactorial (2 * k - 1) := by
      intro p hp
      rw [length_map]
      obtain ⟨c, rest⟩ := p
      exact ih rest (by have := length_of_mem_pickEach hp; omega)
    rw [sum_map_const_on hconst]
    have hlen : (pickEach t).length = t.length := by
      simpa using congrArg List.length (map_fst_pickEach t)
    have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [hlen, ht, h2, Nat.doubleFactorial_add_one]

/-- **The campaign constant.**  A 12-element block yields exactly
`11!! = 10395` matchings — the cube count asserted at every level of the
campaign (`cubes.py:all_cubes`). -/
theorem length_matchingsL_twelve (l : List α) (h : l.length = 12) :
    (matchingsL l).length = 10395 := by
  rw [length_matchingsL 6 l (by omega)]
  decide

/-- The literal instance the campaign runs on: the canonical block indices
`0, …, 11` (Python's `matchings(tuple(range(12)))`). -/
theorem length_matchingsL_range12 :
    (matchingsL (List.range 12)).length = 10395 :=
  length_matchingsL_twelve _ (by simp)

/-! ### Soundness: every entry is a perfect matching -/

/-- Flatten a pair list into its components, in order:
`[(a,b), (c,d), …] ↦ [a, b, c, d, …]`.  "`m` is a perfect matching of `l`"
is then simply `flatPairs m ~ l`: the pairs use exactly the elements of
`l`, each exactly once. -/
def flatPairs : List (α × α) → List α
  | [] => []
  | p :: m => p.1 :: p.2 :: flatPairs m

@[simp] theorem flatPairs_nil : flatPairs ([] : List (α × α)) = [] := rfl

@[simp] theorem flatPairs_cons (p : α × α) (m : List (α × α)) :
    flatPairs (p :: m) = p.1 :: p.2 :: flatPairs m := rfl

theorem flatPairs_append (m₁ m₂ : List (α × α)) :
    flatPairs (m₁ ++ m₂) = flatPairs m₁ ++ flatPairs m₂ := by
  induction m₁ with
  | nil => rfl
  | cons p m ih => simp [ih]

/-- An element is in the flattening iff some pair contains it. -/
theorem mem_flatPairs {m : List (α × α)} {x : α} :
    x ∈ flatPairs m ↔ ∃ p ∈ m, x = p.1 ∨ x = p.2 := by
  induction m with
  | nil => simp
  | cons p m ih =>
    simp only [flatPairs_cons, mem_cons, ih]
    constructor
    · rintro (h | h | ⟨q, hq, hx⟩)
      · exact ⟨p, Or.inl rfl, Or.inl h⟩
      · exact ⟨p, Or.inl rfl, Or.inr h⟩
      · exact ⟨q, Or.inr hq, hx⟩
    · rintro ⟨q, hq | hq, hx⟩
      · subst hq
        tauto
      · exact Or.inr (Or.inr ⟨q, hq, hx⟩)

/-- **Soundness.**  Every entry of `matchingsL l` is a perfect matching of
`l`: flattening its pairs gives a permutation of `l`, i.e. the pairs use
exactly the elements of `l`, each exactly once (with multiplicity — no
Nodup hypothesis needed). -/
theorem perm_of_mem_matchingsL {l : List α} {m : List (α × α)}
    (hm : m ∈ matchingsL l) : flatPairs m ~ l := by
  cases l with
  | nil =>
    rw [matchingsL_nil, mem_singleton] at hm
    subst hm
    exact Perm.refl _
  | cons a t =>
    rw [matchingsL_cons, mem_flatMap] at hm
    obtain ⟨p, hp, hm⟩ := hm
    rw [mem_map] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    have ih : flatPairs m' ~ p.2 := perm_of_mem_matchingsL hm'
    calc flatPairs ((a, p.1) :: m') = a :: p.1 :: flatPairs m' := rfl
      _ ~ a :: p.1 :: p.2 := (ih.cons p.1).cons a
      _ ~ a :: t := (cons_perm_of_mem_pickEach hp).cons a
termination_by l.length
decreasing_by
  subst_vars
  have h1 := length_of_mem_pickEach (l := t) (c := p.1) (rest := p.2) hp
  have h2 : (a :: t).length = t.length + 1 := rfl
  omega

/-! ### No duplicates in the enumeration -/

/-- **Nodup.**  On a duplicate-free list, `matchingsL` lists no matching
twice.  Combined with `length_matchingsL` this pins the enumeration to
exactly the (2k−1)!! distinct objects — the cube list is a partition, not
a multicover, so per-cube conflict counts add up honestly. -/
theorem nodup_matchingsL {l : List α} (hl : l.Nodup) :
    (matchingsL l).Nodup := by
  cases l with
  | nil =>
    rw [matchingsL_nil]
    simp
  | cons a t =>
    have ht : t.Nodup := hl.of_cons
    rw [matchingsL_cons, nodup_flatMap]
    constructor
    · intro p hp
      have hnd : p.2.Nodup := (sublist_of_mem_pickEach hp).nodup ht
      have hinj : Function.Injective fun m : List (α × α) => (a, p.1) :: m := by
        intro m₁ m₂ h
        injection h
      exact (nodup_matchingsL hnd).map hinj
    · have h2 : ((pickEach t).map Prod.fst).Nodup := by
        rw [map_fst_pickEach]
        exact ht
      have hfst : (pickEach t).Pairwise fun p q => p.1 ≠ q.1 :=
        pairwise_map.mp h2
      refine hfst.imp ?_
      intro p q hne mm hmp hmq
      rw [mem_map] at hmp hmq
      obtain ⟨m₁, -, rfl⟩ := hmp
      obtain ⟨m₂, -, heq⟩ := hmq
      injection heq with h1 h2
      injection h1 with g1 g2
      exact hne g2.symm
termination_by l.length
decreasing_by
  subst_vars
  have h1 := length_of_mem_pickEach (l := t) (c := p.1) (rest := p.2) hp
  have h2 : (a :: t).length = t.length + 1 := rfl
  omega

/-! ### Completeness: every perfect matching is listed -/

/-- The unordered-pair reading of a matching: forget the orientation of
each pair.  Two pair lists denote the SAME matching — the same set of
edges, hence the same cube (a cube's 66 literals only mention unordered
edges) — iff their `sym2List`s are permutations of each other. -/
def sym2List (m : List (α × α)) : List (Sym2 α) :=
  m.map fun p => Sym2.mk p.1 p.2

@[simp] theorem sym2List_nil : sym2List ([] : List (α × α)) = [] := rfl

@[simp] theorem sym2List_cons (p : α × α) (m : List (α × α)) :
    sym2List (p :: m) = Sym2.mk p.1 p.2 :: sym2List m := rfl

theorem sym2List_append (m₁ m₂ : List (α × α)) :
    sym2List (m₁ ++ m₂) = sym2List m₁ ++ sym2List m₂ := by
  simp [sym2List]

/-- **COMPLETENESS — the load-bearing theorem.**  Let `l` be duplicate-free
and let `m` be ANY perfect matching of `l` — any list of pairs whose
flattened components are a permutation of `l` (each element of `l` in
exactly one pair).  Then the enumeration contains an entry `m'` denoting
the same matching: the same unordered pairs, up to order
(`sym2List m' ~ sym2List m`).

For the SAT campaign this is exactly the cube-cover statement: a model of
an orbit instance induces SOME perfect matching `m` on the 12-vertex block
(constraint family F2); by this theorem `m` is — as a set of edges, which
is all a cube's 66 literals mention — one of the 10,395 enumerated
matchings, so the model satisfies that cube.  Refuting every enumerated
cube therefore refutes the instance; nothing falls between the cubes. -/
theorem matchingsL_complete {l : List α} (hl : l.Nodup) {m : List (α × α)}
    (hm : flatPairs m ~ l) :
    ∃ m' ∈ matchingsL l, sym2List m' ~ sym2List m := by
  cases l with
  | nil =>
    obtain rfl : m = [] := by
      cases m with
      | nil => rfl
      | cons p m => simp at hm
    exact ⟨[], by simp, Perm.refl _⟩
  | cons a t =>
    -- locate the pair of `m` containing `a`, and split `m` around it
    have ha : a ∈ flatPairs m := hm.mem_iff.mpr mem_cons_self
    obtain ⟨q, hq, hxa⟩ := mem_flatPairs.mp ha
    obtain ⟨m₁, m₂, rfl⟩ := append_of_mem hq
    -- name its other endpoint `b`; up to `Sym2`, `q` IS the pair `(a, b)`
    obtain ⟨b, hsym, hkey⟩ :
        ∃ b, Sym2.mk q.1 q.2 = Sym2.mk a b ∧
          flatPairs (m₁ ++ q :: m₂) ~ a :: b :: flatPairs (m₁ ++ m₂) := by
      rcases hxa with hxa | hxa
      · refine ⟨q.2, by rw [← hxa], ?_⟩
        simp only [flatPairs_append, flatPairs_cons]
        rw [← hxa]
        calc flatPairs m₁ ++ a :: q.2 :: flatPairs m₂
            ~ a :: (flatPairs m₁ ++ q.2 :: flatPairs m₂) := perm_middle
          _ ~ a :: q.2 :: (flatPairs m₁ ++ flatPairs m₂) := perm_middle.cons a
      · refine ⟨q.1, by rw [hxa]; exact Sym2.eq_swap, ?_⟩
        simp only [flatPairs_append, flatPairs_cons]
        rw [hxa]
        calc flatPairs m₁ ++ q.1 :: q.2 :: flatPairs m₂
            ~ q.1 :: (flatPairs m₁ ++ q.2 :: flatPairs m₂) := perm_middle
          _ ~ q.1 :: q.2 :: (flatPairs m₁ ++ flatPairs m₂) := perm_middle.cons q.1
          _ ~ q.2 :: q.1 :: (flatPairs m₁ ++ flatPairs m₂) := Perm.swap q.2 q.1 _
    -- peel `a`, then `b`, off both sides of the permutation
    have ht2 : t ~ b :: flatPairs (m₁ ++ m₂) := (hm.symm.trans hkey).cons_inv
    have hb : b ∈ t := ht2.mem_iff.mpr mem_cons_self
    obtain ⟨rest, hrest⟩ := exists_mem_pickEach_of_mem hb
    have hw : flatPairs (m₁ ++ m₂) ~ rest :=
      (((cons_perm_of_mem_pickEach hrest).trans ht2).cons_inv).symm
    -- recurse on the two-shorter remainder
    have hrestnd : rest.Nodup :=
      (sublist_of_mem_pickEach (p := (b, rest)) hrest).nodup hl.of_cons
    obtain ⟨m'', hmem'', hperm''⟩ := matchingsL_complete hrestnd hw
    refine ⟨(a, b) :: m'', ?_, ?_⟩
    · rw [matchingsL_cons, mem_flatMap]
      exact ⟨(b, rest), hrest, mem_map.mpr ⟨m'', hmem'', rfl⟩⟩
    · calc sym2List ((a, b) :: m'')
          = Sym2.mk a b :: sym2List m'' := rfl
        _ ~ Sym2.mk a b :: sym2List (m₁ ++ m₂) := hperm''.cons _
        _ = Sym2.mk a b :: (sym2List m₁ ++ sym2List m₂) := by
            rw [sym2List_append]
        _ = Sym2.mk q.1 q.2 :: (sym2List m₁ ++ sym2List m₂) := by rw [hsym]
        _ ~ sym2List m₁ ++ Sym2.mk q.1 q.2 :: sym2List m₂ := perm_middle.symm
        _ = sym2List (m₁ ++ q :: m₂) := by
            rw [sym2List_append, sym2List_cons]
termination_by l.length
decreasing_by
  subst_vars
  have h1 := length_of_mem_pickEach (l := t) (c := b) (rest := rest) hrest
  have h2 : (a :: t).length = t.length + 1 := rfl
  omega

/-! ### Distinctness at the cube level -/

/-- An unordered pair is in `sym2List m` iff some pair of `m` reads as it. -/
theorem mem_sym2List {m : List (α × α)} {e : Sym2 α} :
    e ∈ sym2List m ↔ ∃ p ∈ m, e = Sym2.mk p.1 p.2 := by
  simp [sym2List, eq_comm]

/-- On a Nodup list, the remainder of a pick is determined by the picked
element. -/
theorem pickEach_rest_unique {t : List α} (ht : t.Nodup) {b : α}
    {r₁ r₂ : List α} (h₁ : (b, r₁) ∈ pickEach t) (h₂ : (b, r₂) ∈ pickEach t) :
    r₁ = r₂ := by
  induction t generalizing r₁ r₂ with
  | nil => simp [pickEach] at h₁
  | cons c t' ih =>
    have hct' : c ∉ t' := (nodup_cons.mp ht).1
    simp only [pickEach, mem_cons, mem_map, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨hb₁, hr₁⟩ | ⟨p₁, hp₁, hb₁, hr₁⟩ <;>
      rcases h₂ with ⟨hb₂, hr₂⟩ | ⟨p₂, hp₂, hb₂, hr₂⟩
    · rw [hr₁, hr₂]
    · -- head pick vs tail pick: the picked element would be both `c` and in `t'`
      exfalso
      have hmem : p₂.1 ∈ t' := by
        rw [← map_fst_pickEach t']
        exact mem_map.mpr ⟨p₂, hp₂, rfl⟩
      rw [hb₂, hb₁] at hmem
      exact hct' hmem
    · exfalso
      have hmem : p₁.1 ∈ t' := by
        rw [← map_fst_pickEach t']
        exact mem_map.mpr ⟨p₁, hp₁, rfl⟩
      rw [hb₁, hb₂] at hmem
      exact hct' hmem
    · have h₁' : (b, p₁.2) ∈ pickEach t' := by rw [← hb₁]; exact hp₁
      have h₂' : (b, p₂.2) ∈ pickEach t' := by rw [← hb₂]; exact hp₂
      rw [← hr₁, ← hr₂, ih (nodup_cons.mp ht).2 h₁' h₂']

/-- **Cube-level distinctness.**  On a Nodup list the enumeration is
injective down to the unordered-edge reading: two entries with the same
multiset of unordered pairs (`sym2List m₁ ~ sym2List m₂` — the relation
under which a cube's 66 literals cannot tell them apart) are the SAME
entry.  `nodup_matchingsL` alone only forbids literal repetition of an
ordered pair list; THIS theorem is what makes the 10,395 cube ids denote
10,395 pairwise-distinct cubes, so the cube list is a partition of the
covered space, not a multicover. -/
theorem eq_of_sym2_perm_matchingsL {l : List α} (hl : l.Nodup)
    {m₁ m₂ : List (α × α)} (h₁ : m₁ ∈ matchingsL l) (h₂ : m₂ ∈ matchingsL l)
    (hs : sym2List m₁ ~ sym2List m₂) : m₁ = m₂ := by
  cases l with
  | nil =>
    rw [matchingsL_nil, mem_singleton] at h₁ h₂
    rw [h₁, h₂]
  | cons a t =>
    have hat : a ∉ t := (nodup_cons.mp hl).1
    rw [matchingsL_cons, mem_flatMap] at h₁ h₂
    obtain ⟨⟨b₁, r₁⟩, hp₁, hm₁⟩ := h₁
    obtain ⟨⟨b₂, r₂⟩, hp₂, hm₂⟩ := h₂
    rw [mem_map] at hm₁ hm₂
    obtain ⟨m₁', hm₁', rfl⟩ := hm₁
    obtain ⟨m₂', hm₂', rfl⟩ := hm₂
    simp only [sym2List_cons] at hs
    have hb₂t : b₂ ∈ t := by
      rw [← map_fst_pickEach t]
      exact mem_map.mpr ⟨(b₂, r₂), hp₂, rfl⟩
    -- entry 1's head edge appears among entry 2's edges …
    have hmem : Sym2.mk a b₁ ∈ Sym2.mk a b₂ :: sym2List m₂' :=
      hs.mem_iff.mp mem_cons_self
    -- … and only entry 2's head edge can contain `a`, so the heads agree
    have hb : b₁ = b₂ := by
      rcases mem_cons.mp hmem with heq | hmem'
      · rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨h1, -⟩
        · exact h
        · rw [← h1] at hb₂t
          exact absurd hb₂t hat
      · exfalso
        obtain ⟨q, hq, hq'⟩ := mem_sym2List.mp hmem'
        have haq : a ∈ Sym2.mk q.1 q.2 := by
          rw [← hq']
          exact Sym2.mem_mk_left a b₁
        have ha2 : a ∈ flatPairs m₂' :=
          mem_flatPairs.mpr ⟨q, hq, Sym2.mem_iff.mp haq⟩
        exact hat ((sublist_of_mem_pickEach hp₂).subset
          ((perm_of_mem_matchingsL hm₂').mem_iff.mp ha2))
    subst hb
    have hr : r₁ = r₂ := pickEach_rest_unique (nodup_cons.mp hl).2 hp₁ hp₂
    subst hr
    have hnd : r₁.Nodup :=
      (sublist_of_mem_pickEach (p := (b₁, r₁)) hp₁).nodup (nodup_cons.mp hl).2
    rw [eq_of_sym2_perm_matchingsL hnd hm₁' hm₂' hs.cons_inv]
termination_by l.length
decreasing_by
  subst_vars
  have h1 := length_of_mem_pickEach hp₁
  have h2 : (a :: t).length = t.length + 1 := rfl
  omega

end Conway99
