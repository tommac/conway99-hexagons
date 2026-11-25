/-
Conway99.Parity — the PER-ROOT PARITY obstruction: `D(x) ≠ 2r(r−1) − 1`.

**What this file is for.**  `FlagCount.lean` proves THEOREM C,
`2·n₃ = Σ_x (2r(r−1) − D(x))`, so every unit by which `D(x)` falls short of its
maximum `2r(r−1)` buys half a 2-join.  The SAT campaign's cheapest certificate
(log 031) is "no vertex is canonical", i.e. `D(x) ≤ 83` at `v = 99`; by itself
that gives `2n₃ ≥ 99`, hence (with `6 ∣ Σ D`, which `theoremC_n1` supplies)
`n₃ ≥ 51`.  This file proves that **`D(x) = 83` is unreachable**, which doubles
that rung to `n₃ ≥ 99` with no new solver work at all.

**The mathematics** (log 032's parenthetical "`D = 83` is the only unachievable
value; `d_a = 5` is impossible", here proved).  Slice the 84 transitions at `x`
by their first coordinate `a ∈ N(x)`.  For fixed `a`, the six transitions
`(a, {b,b′})` compare two perfect matchings on the same twelve points — the
twelve label vertices `z_ab`, `b ∈ N(x) ∖ {a,a′}`, which are exactly
`N(a) ∖ {x,a′}`: the matching `Γ[N(a)]` induces on them (λ = 1), and the
matching they inherit from the pairing of `N(x)`.  Two perfect matchings on
twelve points cannot agree in exactly five pairs: five agreements consume ten
points, and the remaining two must then be matched to each other by BOTH.  So
`d_a ∈ {0,1,2,3,4,6}`, never 5, and `D = Σ_a d_a = 83` (thirteen 6's and one 5)
is impossible.

**How it is proved here — no counting.**  Rather than formalise "five pairs
consume ten points", the file proves the sharper local statement directly:

  `exists_second_bad_transition` — a non-canonical transition `(a, C)` at `x`
  always has a COMPANION non-canonical transition `(a, C′)` at the same root,
  `C′ ≠ C`.

Given the bad transition `(a, {b,b′})` with label `z = z_ab`, take `w` = the
apex of the edge `a z` (λ = 1).  Then `w ∉ N[x]` (else `w` would be `a′`, which
`label_not_matched` forbids), so μ = 2 gives `x, w` a second common neighbour
`c ≠ a`; `(a,c)` is a flag with label `w`, and `c ∉ {b, b′}` — `c = b` would
force `z ~ z`, `c = b′` would make the original transition canonical.  Finally
`(a, {c,c′})` is itself non-canonical, because a canonical one would produce a
second common neighbour of the adjacent pair `a, w` and then a third common
neighbour of the non-adjacent pair `x, z`.  A singleton set cannot contain a
companion of its own element, so the bad count at `x` is never 1, and
`D(x) = 2r(r−1) − 1` is impossible.

**Grades.**  Everything below is PROVED (`Audit.lean` prints the axiom bases).
`hD : ∀ x, D G x ≤ 83` is NOT proved here: it is log 031's SAT/DRAT/LRAT
certificate, imported as a hypothesis exactly as in `FlagCount.lean` §F13, and
tied to the CNF by the encoder correspondence (lean/README.md informal item
7(c)).  `conway99_n3_ge_99_of_skeleton_root` states the chain in the form the
certificate actually licenses — a bound at the SKELETON's root — by routing
through `WLOG.forall_D_le_of_skeleton_root`.

**Non-vacuity, stated honestly.**  `exists_second_bad_transition` has no
witness inside the srg(1+2r², 2r, 1, 2) family: both known members (Paley(9),
BvLS(243)) are canonical, so their bad-transition sets are EMPTY and the lemma
never fires on them.  This is the same situation `FlagCount.lean` §F15 records
for the `m = 2` fibre branch, and there is no way around it short of a
counterexample to Conway's problem.  What IS checkable is the split identity
this file's arithmetic rests on, and §P4 pins it with `decide` computations on
Paley(9) beside the values the theorems predict.
-/
import Mathlib
import Conway99.FlagCount
import Conway99.WLOG

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k : ℕ}

/-! ### P1 — the bad (non-canonical) transitions at a root -/

/-- The **NON-CANONICAL transitions** at `x`: those transitions `(a, {b,b′})`
whose flags are not canonical.  `D(x)` counts the complement inside
`transitionsAt G x`. -/
def badTransitionsAt (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset (V × Finset V) :=
  transitionsAt G x \ canonTransitionsAt G x

theorem canonTransitionsAt_subset (x : V) :
    canonTransitionsAt G x ⊆ transitionsAt G x := by
  refine Finset.image_subset_image ?_
  intro p hp
  simp only [canonFlagsAt, flagsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.1

theorem mem_badTransitionsAt {x : V} {t : V × Finset V} :
    t ∈ badTransitionsAt G x ↔ t ∈ transitionsAt G x ∧ t ∉ canonTransitionsAt G x :=
  Finset.mem_sdiff

/-- **THE SPLIT AT A ROOT**: `D(x) + #bad = #transitions`.  With
`card_transitionsAt` this is `D(x) + #bad = 2r(r−1)`. -/
theorem card_badTransitionsAt_add (x : V) :
    D G x + (badTransitionsAt G x).card = (transitionsAt G x).card := by
  have hsub := canonTransitionsAt_subset (G := G) x
  have hle := Finset.card_le_card hsub
  have hcard : (badTransitionsAt G x).card
      = (transitionsAt G x).card - (canonTransitionsAt G x).card :=
    Finset.card_sdiff_of_subset hsub
  simp only [D]
  omega

/-! ### P2 — the parity lemma: bad transitions come in pairs at a root -/

/-- **THE PER-ROOT PARITY LEMMA.**  A non-canonical transition `(a, C)` at `x`
never stands alone at its own root: there is a second non-canonical transition
`(a, C′)` with `C′ ≠ C`.

This is the Lean form of "two perfect matchings on twelve points never agree in
exactly five pairs" — stated as the production of a companion rather than as a
count, which is what makes it a short proof from `Transition.lean`'s local
lemmas alone. -/
theorem exists_second_bad_transition (h : G.IsSRGWith n k 1 2) {x a : V} {C : Finset V}
    (ht : (a, C) ∈ badTransitionsAt G x) :
    ∃ C', (a, C') ∈ badTransitionsAt G x ∧ C' ≠ C := by
  classical
  rw [mem_badTransitionsAt] at ht
  obtain ⟨htr, hbad⟩ := ht
  obtain ⟨b, hf', hCeq'⟩ := mem_transitionsAt.mp htr
  -- strip the `(a, C).1` / `(a, C).2` projections (definitional)
  have hf : IsFlag G x a b := hf'
  have hCeq : C = classOf G x b := hCeq'
  clear hf' hCeq'
  obtain ⟨b', z, y, z', hp, hab', hnab', hz, -, hz'⟩ := flag_data h hf
  -- the transition is bad, so the flag `(a,b)` is not canonical, so `z ≁ z′`
  have hncan : ¬ IsCanonFlag G x a b := fun hc =>
    hbad (mem_canonTransitionsAt.mpr ⟨b, hf, hc, hCeq⟩)
  have hzz' : ¬ G.Adj z z' := fun hadj => hncan ⟨b', z, z', hp, hz, hz', hadj⟩
  -- `w` = the apex of the edge `a z` (λ = 1)
  obtain ⟨w, hw, -⟩ := exists_apex h hz.1
  -- `w ≠ x`, because `x ≁ z` while `z ~ w`
  have hwx : w ≠ x := by
    rintro rfl
    exact hz.2.2.2 hw.2.2.symm
  -- `w ∉ N(x)`: otherwise `w` would be the partner `a′`, which cannot see `z`
  have hxw : ¬ G.Adj x w := by
    intro hxw
    obtain ⟨a', hpa, -⟩ := exists_unique_partner h hf.1
    have hwa' : w = a' :=
      unique_common_of_adj h hf.1
        ((mem_commonNeighbors G).mpr ⟨hxw, hw.2.1⟩)
        ((mem_commonNeighbors G).mpr ⟨hpa.2.1, hpa.2.2⟩)
    refine label_not_matched h hpa hz.1 hz.2.2.1 ?_
    rw [← hwa']
    exact hw.2.2.symm
  -- μ = 2: `x` and `w` are non-adjacent with common neighbour `a`, so there is a
  -- second common neighbour `c`
  obtain ⟨c, hca, hxc, hwc⟩ :=
    exists_second_common h (Ne.symm hwx) hxw hf.1 hw.2.1.symm
  -- `(a,c)` is a flag: `a ~ c` would give the edge `a c` two common neighbours
  have hac : ¬ G.Adj a c := by
    intro hadj
    exact hwx (unique_common_of_adj h hadj
      ((mem_commonNeighbors G).mpr ⟨hw.2.1, hwc.symm⟩)
      ((mem_commonNeighbors G).mpr ⟨hf.1.symm, hxc.symm⟩))
  have hfc : IsFlag G x a c := ⟨hf.1, hxc, Ne.symm hca, hac⟩
  -- ... and `w` is its label
  have hlc : IsLabel G x a c w := ⟨hw.2.1, hwc.symm, hwx, hxw⟩
  -- `c ≠ b`: else `w = z`, and `z ~ w` would be a loop
  have hcb : c ≠ b := by
    intro hcb
    subst hcb
    have hwz : w = z := label_unique h hf.1 hf.2.1 hf.2.2.2 hf.2.2.1 hlc hz
    rw [hwz] at hw
    exact G.irrefl hw.2.2
  -- `c ≠ b′`: else `w = z′`, and `z ~ w` would make `(a,b)` canonical
  have hcb' : c ≠ b' := by
    intro hcb'
    subst hcb'
    have hwz' : w = z' := label_unique h hf.1 hp.2.1 hnab' hab' hlc hz'
    rw [hwz'] at hw
    exact hzz' hw.2.2
  -- `classOf G x b = {b, b′}` — used for both remaining obligations
  have hclb : classOf G x b = {b, b'} := classOf_eq h hp
  refine ⟨classOf G x c, ?_, ?_⟩
  · -- the companion is a transition at `a`, and it is bad
    rw [mem_badTransitionsAt]
    refine ⟨mem_transitionsAt.mpr ⟨c, hfc, rfl⟩, ?_⟩
    intro hmem
    obtain ⟨d, hfd', hcd', hclcd'⟩ := mem_canonTransitionsAt.mp hmem
    have hcd : IsCanonFlag G x a d := hcd'
    have hclcd : classOf G x c = classOf G x d := hclcd'
    clear hfd' hcd' hclcd'
    -- the canonical representative `d` lies in `c`'s class, so `(a,c)` is canonical too
    obtain ⟨c', hpc, -⟩ := exists_unique_partner h hxc
    have hdmem : d ∈ ({c, c'} : Finset V) := by
      rw [← classOf_eq h hpc, hclcd, classOf]
      exact Finset.mem_insert_self _ _
    have hcanc : IsCanonFlag G x a c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
      rcases hdmem with rfl | rfl
      · exact hcd
      · exact isCanonFlag_partner h hpc.symm hcd
    obtain ⟨c₂, w₁, w₂, hpc₂, hlw₁, hlw₂, hadjw⟩ := hcanc
    -- `w₁ = w`, so `w ~ w₂`; then `w₂` and `z` are both apexes of the edge `a w`
    have hw₁ : w₁ = w := label_unique h hf.1 hxc hac (Ne.symm hca) hlw₁ hlc
    subst hw₁
    have hw₂z : w₂ = z :=
      unique_common_of_adj h hw.2.1
        ((mem_commonNeighbors G).mpr ⟨hlw₂.1, hadjw⟩)
        ((mem_commonNeighbors G).mpr ⟨hz.1, hw.2.2.symm⟩)
    subst hw₂z
    -- now `a`, `b` and `c₂` are three common neighbours of the non-adjacent pair `x, z`
    rcases two_common h (Ne.symm hz.2.2.1) hz.2.2.2
        hf.1 hz.1.symm hf.2.1 hz.2.1.symm hpc₂.2.1 hlw₂.2.1.symm with hcase | hcase | hcase
    · exact hf.2.2.1 hcase
    · exact hac (by rw [hcase]; exact hpc₂.2.2.symm)
    · subst hcase
      exact hcb' (partner_unique h hpc₂.symm hp)
  · -- and it is a DIFFERENT class, because `c ∉ {b, b′}`
    rw [hCeq]
    intro hEq
    have hcmem : c ∈ ({b, b'} : Finset V) := by
      rw [← hclb, ← hEq, classOf]
      exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcmem
    rcases hcmem with hcase | hcase
    · exact hcb hcase
    · exact hcb' hcase

/-- **THE BAD COUNT AT A ROOT IS NEVER 1.**  Immediate from
`exists_second_bad_transition`: a singleton contains no companion of its own
element. -/
theorem card_badTransitionsAt_ne_one (h : G.IsSRGWith n k 1 2) (x : V) :
    (badTransitionsAt G x).card ≠ 1 := by
  intro hcard
  obtain ⟨t, hteq⟩ := Finset.card_eq_one.mp hcard
  have hmem : (t.1, t.2) ∈ badTransitionsAt G x := by
    rw [hteq]; simp
  obtain ⟨C', hC'mem, hC'ne⟩ := exists_second_bad_transition h hmem
  rw [hteq, Finset.mem_singleton] at hC'mem
  exact hC'ne (congrArg Prod.snd hC'mem)

/-! ### P3 — the consequence for `D`, and the `n₃` rungs at `v = 99` -/

/-- **`D(x)` NEVER TAKES THE VALUE `2r(r−1) − 1`** (`= 83` at `v = 99`).  One
short of the maximum would mean exactly one bad transition at `x`, and
`card_badTransitionsAt_ne_one` forbids that. -/
theorem D_ne_pred (h : G.IsSRGWith n k 1 2) {r : ℕ} (hk : k = 2 * r) (hr : 2 ≤ r) (x : V) :
    D G x ≠ 2 * r * (r - 1) - 1 := by
  have h1 := card_badTransitionsAt_add (G := G) x
  have h2 := card_transitionsAt h hk x
  have h3 := card_badTransitionsAt_ne_one h x
  have h4 : 4 ≤ 2 * r * (r - 1) := by
    have hr1 : 1 ≤ r - 1 := by omega
    have hr2 : 2 * 2 ≤ 2 * r := by omega
    calc (4 : ℕ) = 2 * 2 * 1 := by norm_num
      _ ≤ 2 * r * (r - 1) := Nat.mul_le_mul hr2 hr1
  generalize 2 * r * (r - 1) = N at h2 h4 ⊢
  omega

/-- `v = 99`: `D(x) ≠ 83`.  This is the per-root parity result of log 032,
proved. -/
theorem conway99_D_ne_83 (h : G.IsSRGWith 99 14 1 2) (x : V) : D G x ≠ 83 := by
  have hne := D_ne_pred h (r := 7) (by norm_num) (by norm_num) x
  norm_num at hne
  exact hne

/-- `3 ∣ n₃` at `v = 99`, straight from `reimbayev_prop5`
(`12n₁ + 4n₃ = 99·14·12`, i.e. `3n₁ + n₃ = 4158`).  Recorded because the
literature quotes the divisibility-free rung `n₃ ≥ 1`; ours is `n₃ ≥ 3`
already at that level. -/
theorem conway99_three_dvd_n3 (h : G.IsSRGWith 99 14 1 2) : 3 ∣ n3 G := by
  have hr := reimbayev_prop5 h
  norm_num at hr
  omega

/-- **THE LOG-031 RUNG, division included**: from "no vertex is canonical"
(`D(x) ≤ 83`) alone, `n₃ ≥ 51`.  `6 ∣ Σ_x D(x)` comes from `theoremC_n1`. -/
theorem conway99_n3_ge_51 (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 83) :
    51 ≤ n3 G := by
  have hDle : ∀ x : V, D G x ≤ 84 := by
    intro x
    have := D_le h (r := 7) (by norm_num) x
    omega
  have hsplit : (∑ x : V, (84 - D G x)) + ∑ x : V, D G x = 8316 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ => by have := hDle x; omega : ∀ x ∈ Finset.univ,
        (84 - D G x) + D G x = 84),
      Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul]
  have h3 : 2 * n3 G = ∑ x : V, (84 - D G x) := by
    have := theoremC_n3 h (r := 7) (by norm_num)
    norm_num at this
    exact this
  have h1 := theoremC_n1 h
  have hub : ∑ x : V, D G x ≤ 8217 := by
    have hle : ∑ x : V, D G x ≤ ∑ _x : V, 83 := Finset.sum_le_sum fun x _ => hD x
    rwa [Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul] at hle
  omega

/-- **THE PARITY RUNG**: the SAME certificate, `D(x) ≤ 83`, now gives
`n₃ ≥ 99` — because `D(x) = 83` is unreachable, so `D(x) ≤ 82`.  The quantifier
swap of log 031 buys `n₃ ≥ 51`; this lemma nearly doubles it for free. -/
theorem conway99_n3_ge_99 (h : G.IsSRGWith 99 14 1 2) (hD : ∀ x : V, D G x ≤ 83) :
    99 ≤ n3 G := by
  have hD82 : ∀ x : V, D G x ≤ 82 := by
    intro x
    have h1 := conway99_D_ne_83 h x
    have h2 := hD x
    omega
  have hDle : ∀ x : V, D G x ≤ 84 := fun x => le_trans (hD82 x) (by norm_num)
  have hsplit : (∑ x : V, (84 - D G x)) + ∑ x : V, D G x = 8316 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ => by have := hDle x; omega : ∀ x ∈ Finset.univ,
        (84 - D G x) + D G x = 84),
      Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul]
  have h3 : 2 * n3 G = ∑ x : V, (84 - D G x) := by
    have := theoremC_n3 h (r := 7) (by norm_num)
    norm_num at this
    exact this
  have hub : ∑ x : V, D G x ≤ 8118 := by
    have hle : ∑ x : V, D G x ≤ ∑ _x : V, 82 := Finset.sum_le_sum fun x _ => hD82 x
    rwa [Finset.sum_const, Finset.card_univ, h.card, smul_eq_mul] at hle
  omega

/-- The same rung stated from the GEOMETRY rather than the counter: log 031's
certificate says no vertex of a Conway 99-graph is canonical. -/
theorem conway99_n3_ge_99_of_not_canonical (h : G.IsSRGWith 99 14 1 2)
    (hnc : ∀ x : V, ¬ CanonicalAt G x) : 99 ≤ n3 G := by
  refine conway99_n3_ge_99 h fun x => ?_
  have hle := D_le h (r := 7) (by norm_num) x
  have hne : D G x ≠ 84 := by
    intro hD
    exact hnc x (canonicalAt_of_D_eq h (r := 7) (by norm_num) (by rw [hD]))
  norm_num at hle
  omega

/-- **THE RUNG IN THE FORM THE CERTIFICATE LICENSES.**  `hskel` is log 031's
SAT/DRAT/LRAT result — a bound on `D` at the SKELETON's root, over every
completion that is an srg(99,14,1,2) — and `forall_D_le_of_skeleton_root`
(rooted WLOG + `D_iso`) is what turns it into a bound at every vertex of every
abstract srg(99,14,1,2).  Everything between `hskel` and the conclusion is
proved; `hskel` itself is not a Lean theorem (see lean/README.md item 7(c)). -/
theorem conway99_n3_ge_99_of_skeleton_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (hskel : ∀ (X : Fin 84 → Fin 84 → Bool) (hsymm : ∀ i j, X i j = X j i)
      (hirrefl : ∀ i, X i i = false),
      (skeletonGraph X hsymm hirrefl).IsSRGWith 99 14 1 2 →
        D (skeletonGraph X hsymm hirrefl) rootV ≤ 83) :
    99 ≤ n3 G :=
  conway99_n3_ge_99 h (forall_D_le_of_skeleton_root h hskel)

/-! ### P4 — NON-VACUITY

Read the grade.  `exists_second_bad_transition` CANNOT fire inside this family:
Paley(9) and BvLS(243) are canonical, so `badTransitionsAt` is empty at every
one of their vertices and the lemma is quantified over an empty set there.  A
witness would be a non-canonical srg(v, 2r, 1, 2), which is precisely the open
object.  What the two `decide`s below pin is the SPLIT this file's arithmetic
uses — `D(x) + #bad = #transitions` — at a concrete graph, stated beside the
values `card_transitionsAt` and `card_badTransitionsAt_add` predict (`4 + 0 =
4` at `r = 2`).  They are computations off the definitions and can fail. -/

set_option maxRecDepth 100000 in
/-- Paley(9) has four transitions at a root — `card_transitionsAt` at `r = 2`
predicts `2·2·(2−1) = 4`. -/
theorem paley9_transitionsAt_card :
    (transitionsAt paley9 ((0 : Fin 3), (0 : Fin 3))).card = 4 := by decide

set_option maxRecDepth 100000 in
/-- ... and none of them is bad, Paley(9) being canonical.  With
`paley9_D_computed = 4` this pins `card_badTransitionsAt_add`. -/
theorem paley9_badTransitionsAt_card :
    (badTransitionsAt paley9 ((0 : Fin 3), (0 : Fin 3))).card = 0 := by decide

end Conway99
