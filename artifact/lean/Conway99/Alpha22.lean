/-
Conway99.Alpha22 — the "C2" filter of the α = 22 branch has provably ZERO
POWER (log 043), formalized.

CONTEXT.  An external deliverable on the α = 22 branch proposed to filter
candidate 2-(22,4,2) designs by two predicates:

  C1 — every two blocks meet in at most 2 points;
  C2 — at every point `s`, the 14 blocks through `s` pair up into 7 couples
       meeting exactly in `{s}`.

Their theorem was **C1 ⟹ C2**: under C1 the "partner graph" on the 14 blocks
through `s` is 10-REGULAR, and Dirac's matching bound then supplies a perfect
matching.  That theorem is CORRECT and is not disputed here.  The audit of
log 043 found something strictly stronger: the degree bound needs no C1
hypothesis at all.  Hence C2 holds in EVERY 2-(22,4,2) design whatsoever, and
a search that filters candidates by C2 removes nothing.  Counting the three
zero-power hunts that log 034's audit found in the same external author's
srg(243,22,1,2) deliverable (`Switch2.lean` formalizes one of them), this is a
FOURTH provably zero-power search from that author, and it is zero-power over
the entire 2-(22,4,2) design universe rather than merely over the C1
survivors.  It is NOT the project's first universe-wide zero-power result:
`Conway99.not_isSRGWith_switch` (`Switch2.lean`) already quantifies over every
srg(v,k,1,2) and every valid 2-switch.

WHAT IS PROVED, AND IN WHICH ORDER.

  * `card_heavy_le` — THE HEART of the file.  In any indexed block family
    in which every block has `k` points and every pair of distinct points lies
    in exactly `λ` blocks, fix a point `s` and a block `i` through `s`.  The
    number of OTHER blocks through `s` that meet `blocks i` in ≥ 2 points is at
    most `(k-1)(λ-1)`.  Read the statement: it quantifies over an arbitrary
    `blocks : ι → Finset P` and assumes NOTHING about how blocks intersect.
    That unconditionality is the entire content.
    ON PROVENANCE: this is an elementary union bound of the kind design theory
    is full of, and NO literature search has been made for it.  "Ours" can
    therefore mean only "not taken from the deliverable under audit" — that
    deliverable reaches the same `10` through C1 instead.  Like everything
    else in this file it is proved outright rather than quoted, so nothing
    downstream depends on its provenance either way.
  * `replication_mul` — the standard double count `r(k-1) = (v-1)λ`, proved
    rather than assumed.  So `r = 14` at `(22,4,2)` is DERIVED, and the
    headline `c2_always_holds` carries no replication hypothesis; only the
    GENERIC theorem `exists_perfectMatching_partnerGraph` takes the block
    count `2m` as a hypothesis (`hr`), and `c2_always_holds` discharges it.
  * `card_le_degree_partnerGraph` — the min-degree corollary, subtraction-free:
    `#(blocks through s) ≤ deg(i) + 1 + (k-1)(λ-1)` in the partner graph.
  * `exists_perfectMatching_partnerGraph` — the generic headline: if the number
    of blocks through `s` is `2m` and `1 + (k-1)(λ-1) ≤ m`, the partner graph at
    `s` has a perfect matching.  `Conway99.Dirac` supplies the matching step.
  * `c2_always_holds` — the concrete headline at `(v,k,λ) = (22,4,2)`, where
    `replication_mul` forces `r = 14 = 2·7` and the bound reads
    `deg ≥ 14 - 1 - 3·1 = 10 ≥ 7`.

BLOCKS MAY REPEAT.  The design is presented as an INDEXED family
`blocks : ι → Finset P`, never as a set of blocks, so repeated blocks and
heavily-overlapping blocks are inside the scope.  This is load-bearing: the
claim is that C2 cannot fail for ANY 2-(22,4,2) design, and dropping
repetitions would quietly narrow the universe.  The non-vacuity witness
`fano2Blocks` is deliberately a design WITH repeated blocks.

NON-VACUITY (mandatory here, and the premises are shown to FIRE, not merely to
typecheck).  Two witnesses on `Fin 7`:
  * the Fano plane `fanoBlocks i = {i, i+1, i+3}`, a 2-(7,3,1) design with
    `r = 3`.  `fano_heavy_empty` runs `card_heavy_le` on it and gets the sharp
    conclusion `0` (λ = 1 kills the bound outright).  Note that this is a
    bound on an EMPTY set, so on its own it would be the classic vacuous
    instantiation — which is why the next witness exists;
  * its doubling `fano2Blocks (i, b) = fanoBlocks i`, a 2-(7,3,2) design on 14
    indices WITH EVERY BLOCK REPEATED, `r = 6 = 2·3`, where
    `1 + (k-1)(λ-1) = 3 ≤ 3` so `exists_perfectMatching_partnerGraph` fires
    (`fano2_partner_perfectMatching`).  There `fano2_heavy_nonempty` shows
    Lemma 1's left-hand side is INHABITED (count 1, against the allowed 2), so
    the lemma is not being instantiated at an empty set; `fano2_partner_adj`
    exhibits an actual partner pair and `fano2_partner_not_adj` a NON-EDGE
    (the two copies of one block are not partners), so the partner graph there
    is neither empty nor complete and the conclusion is not free.
    HOW MUCH SLACK: that partner graph is `K_{2,2,2}`, so EVERY degree is
    `4` against the `3` the theorem needs (`fano2_degree_eq_four`), and the
    heavy count `1` is under the allowed `2`.  The witness shows the
    hypotheses FIRE; it does not show them tight.  Tightness is exhibited in
    `Conway99.Dirac` instead, by `C4` (four vertices, every degree exactly 2).

NON-CLAIMS — read these before quoting anything above.

  1. The **Hoffman ratio bound is not proved here** (the spectral theory is
     absent from this Mathlib).  Consequently the v = 99 chain
     "α(Γ) ≤ 22  ⟹  the neighbourhoods of a maximum coclique form a
     2-(22,4,2) design" is NOT formalized — and it is NOT a hypothesis of
     anything here either, so it is a WEAKER kind of input than `C2.lean`'s
     `hfix`: `hfix` is a hypothesis of Lean theorems, which makes everything
     consuming it visibly conditional, whereas this chain is carried by
     NO Lean statement in this file at all — no theorem here so much as
     mentions v = 99 or Γ.  The file starts from a design, says nothing about
     where the design came from, and its own results are unconditional.  The
     chain is cited in prose only, and is registered as such in
     `lean/README.md`'s informal list (item 4(c)).
  2. **No α value is computed here.**  `α(BvLS(243)) = 45` and
     `α(srg(27,10,1,5)) = 6 < 9` (so the ratio bound is NOT tight in the
     nearest λ = 1 relative) are Python computations recorded in log 043;
     they are cited, not Lean theorems.
  3. `alpha22_chain_arithmetic` and `hoffman_ratio_value_99` /
     `hoffman_ratio_value_27` are **arithmetic identities only**.  They record
     that the numbers in the derivation chain are consistent
     (`99 - 22 = 77`, `77·C(4,2) = 2·C(22,2)`, `14·3 = 2·21`) and that the
     ratio-bound EXPRESSION evaluates to 22 and to 9 respectively.  They do
     not assert the ratio bound, and they do not assert that α equals those
     values.
  4. **Nothing here bears on whether srg(99,14,1,2) exists.**  The theorem is a
     statement about 2-(22,4,2) designs; its only role in the project is to
     retire a search filter.
  5. **No 2-(22,4,2) design is exhibited.**  `c2_always_holds` is a universally
     quantified statement that is not shown IN LEAN to be non-vacuous at
     v = 22.  Such designs do exist — log 043 enumerates 738,100 distinct
     2-(22,4,2) designs in one stratum, 800/800 of a sample machine-verified
     to be genuine BIBDs — but that is a Python computation, cited here, not a
     theorem of this file.  (The headline survives either way: over an empty
     class a filter also removes nothing.)  The Lean non-vacuity witnesses are
     at v = 7, and they witness the GENERAL hypotheses
     (`exists_perfectMatching_partnerGraph`), which is what "the theorem is not
     about an empty class" requires.
  6. The external theorem **C1 ⟹ C2 is correct**; this file does not refute it.
     It shows the hypothesis was unnecessary, i.e. the true statement is
     strictly stronger.
-/
import Mathlib
import Conway99.Dirac

namespace Conway99

open Finset

/-! ### The design setting

Points `P`, an INDEX type `ι`, and a block family `blocks : ι → Finset P`.
Nothing forces `blocks` to be injective, so repeated blocks are allowed. -/

section Designs

variable {P : Type*} [DecidableEq P]
variable {ι : Type*} [Fintype ι]

/-- The indices of the blocks through a point `s`.  Its cardinality is the
replication number `r` at `s`. -/
def blocksThrough (blocks : ι → Finset P) (s : P) : Finset ι :=
  Finset.univ.filter fun i => s ∈ blocks i

@[simp] theorem mem_blocksThrough {blocks : ι → Finset P} {s : P} {i : ι} :
    i ∈ blocksThrough blocks s ↔ s ∈ blocks i := by
  simp [blocksThrough]

/-- A 2-`(v, k, λ)` design, presented with an indexed block family: every block
has `k` points, and every pair of DISTINCT points lies in exactly `λ` blocks.
Repeated blocks are permitted — `blocks` is a function, not a set. -/
structure IsDesignWith [Fintype P] (blocks : ι → Finset P) (v k lam : ℕ) : Prop where
  /-- there are `v` points -/
  card_points : Fintype.card P = v
  /-- every block has `k` points -/
  block_card : ∀ i, (blocks i).card = k
  /-- every pair of distinct points lies in exactly `lam` blocks -/
  pair_count : ∀ p q : P, p ≠ q →
    (Finset.univ.filter fun i => p ∈ blocks i ∧ q ∈ blocks i).card = lam

/-! ### Lemma 1 — the unconditional bound

The heart of the file.  NO hypothesis about pairwise block intersections is
used, and none is available: `blocks` is an arbitrary function. -/

/-- **The unconditional heavy-neighbour bound.**  Fix a point `s` and a block
`i` through `s`.  Among the other blocks through `s`, at most `(k-1)(λ-1)` meet
`blocks i` in two or more points.

PROOF.  Such a block `j` shares with `blocks i` some point `x ≠ s`, and there
are only `k - 1` candidates for `x` (the points of `blocks i` other than `s`).
For each fixed `x`, the pair `{s, x}` lies in exactly `λ` blocks and `blocks i`
is one of them, so at most `λ - 1` other blocks through `s` contain `x`.  Union
bound over the `k - 1` choices of `x`. -/
theorem card_heavy_le [DecidableEq ι] {blocks : ι → Finset P} {k lam : ℕ}
    (hk : ∀ i, (blocks i).card = k)
    (hlam : ∀ p q : P, p ≠ q →
      (Finset.univ.filter fun i => p ∈ blocks i ∧ q ∈ blocks i).card = lam)
    (s : P) {i : ι} (hi : s ∈ blocks i) :
    ((blocksThrough blocks s).filter
        fun j => j ≠ i ∧ 2 ≤ (blocks i ∩ blocks j).card).card ≤ (k - 1) * (lam - 1) := by
  classical
  -- the `k - 1` candidate shared points
  have hXcard : ((blocks i).erase s).card = k - 1 := by
    rw [Finset.card_erase_of_mem hi, hk]
  -- for each candidate `x`, at most `λ - 1` other blocks through `s` contain it
  have key : ∀ x ∈ (blocks i).erase s,
      ((blocksThrough blocks s).filter fun j => j ≠ i ∧ x ∈ blocks j).card = lam - 1 := by
    intro x hx
    obtain ⟨hxs, hxi⟩ := Finset.mem_erase.mp hx
    have heq : ((blocksThrough blocks s).filter fun j => j ≠ i ∧ x ∈ blocks j)
        = (Finset.univ.filter fun j => s ∈ blocks j ∧ x ∈ blocks j).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
        mem_blocksThrough]
      tauto
    rw [heq, Finset.card_erase_of_mem (by simp [hi, hxi]), hlam s x (Ne.symm hxs)]
  -- every heavy block is caught by one of the candidates
  have hsub : ((blocksThrough blocks s).filter
        fun j => j ≠ i ∧ 2 ≤ (blocks i ∩ blocks j).card)
      ⊆ ((blocks i).erase s).biUnion
          fun x => (blocksThrough blocks s).filter fun j => j ≠ i ∧ x ∈ blocks j := by
    intro j hj
    simp only [Finset.mem_filter, mem_blocksThrough] at hj
    obtain ⟨hjs, hji, hj2⟩ := hj
    -- the two blocks share `s`, so the ≥ 2 forces a shared point OTHER than `s`
    have hsmem : s ∈ blocks i ∩ blocks j := Finset.mem_inter.mpr ⟨hi, hjs⟩
    have hpos : 0 < ((blocks i ∩ blocks j).erase s).card := by
      rw [Finset.card_erase_of_mem hsmem]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxs, hxmem⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hxmem
    refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_erase.mpr ⟨hxs, hxi⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_blocksThrough.mpr hjs, hji, hxj⟩
  calc ((blocksThrough blocks s).filter
          fun j => j ≠ i ∧ 2 ≤ (blocks i ∩ blocks j).card).card
      ≤ (((blocks i).erase s).biUnion
          fun x => (blocksThrough blocks s).filter
            fun j => j ≠ i ∧ x ∈ blocks j).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ (blocks i).erase s,
          ((blocksThrough blocks s).filter fun j => j ≠ i ∧ x ∈ blocks j).card :=
        Finset.card_biUnion_le
    _ = ∑ _x ∈ (blocks i).erase s, (lam - 1) := Finset.sum_congr rfl key
    _ = (k - 1) * (lam - 1) := by rw [Finset.sum_const, smul_eq_mul, hXcard]

/-! ### The replication number, by double counting

`r(k-1) = (v-1)λ`.  This is standard and is proved here rather than assumed, so
that the headline at `(22,4,2)` does not carry `r = 14` as a hypothesis. -/

/-- **The replication identity** `r·(k-1) = (v-1)·λ`, where `r` is the number of
blocks through `s`.  Counted over the pairs `(i, x)` with `s, x ∈ blocks i`,
`x ≠ s`. -/
theorem replication_mul [Fintype P] {blocks : ι → Finset P} {k lam : ℕ}
    (hk : ∀ i, (blocks i).card = k)
    (hlam : ∀ p q : P, p ≠ q →
      (Finset.univ.filter fun i => p ∈ blocks i ∧ q ∈ blocks i).card = lam)
    (s : P) :
    (blocksThrough blocks s).card * (k - 1) = (Fintype.card P - 1) * lam := by
  classical
  have hcards : (Finset.univ.erase s).card = Fintype.card P - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ]
  have hL : ∀ i ∈ blocksThrough blocks s,
      ((Finset.univ.erase s).filter fun x => x ∈ blocks i).card = k - 1 := by
    intro i hi
    have hrw : ((Finset.univ.erase s).filter fun x => x ∈ blocks i) = (blocks i).erase s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      tauto
    rw [hrw, Finset.card_erase_of_mem (mem_blocksThrough.mp hi), hk]
  have hR : ∀ x ∈ Finset.univ.erase s,
      ((blocksThrough blocks s).filter fun i => x ∈ blocks i).card = lam := by
    intro x hx
    have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
    have hrw : ((blocksThrough blocks s).filter fun i => x ∈ blocks i)
        = Finset.univ.filter fun i => s ∈ blocks i ∧ x ∈ blocks i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_blocksThrough]
    rw [hrw, hlam s x (Ne.symm hxs)]
  calc (blocksThrough blocks s).card * (k - 1)
      = ∑ _i ∈ blocksThrough blocks s, (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ i ∈ blocksThrough blocks s,
          ((Finset.univ.erase s).filter fun x => x ∈ blocks i).card :=
        (Finset.sum_congr rfl hL).symm
    _ = ∑ i ∈ blocksThrough blocks s, ∑ x ∈ Finset.univ.erase s,
          (if x ∈ blocks i then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.card_filter _ _
    _ = ∑ x ∈ Finset.univ.erase s, ∑ i ∈ blocksThrough blocks s,
          (if x ∈ blocks i then 1 else 0) := Finset.sum_comm
    _ = ∑ x ∈ Finset.univ.erase s,
          ((blocksThrough blocks s).filter fun i => x ∈ blocks i).card :=
        Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
    _ = ∑ _x ∈ Finset.univ.erase s, lam := Finset.sum_congr rfl hR
    _ = (Fintype.card P - 1) * lam := by rw [Finset.sum_const, smul_eq_mul, hcards]

/-! ### The partner graph -/

/-- The **partner graph** at a point `s`: vertices are the blocks through `s`,
and two of them are adjacent when they meet in `{s}` and nothing else. -/
def partnerGraph (blocks : ι → Finset P) (s : P) : SimpleGraph {i : ι // s ∈ blocks i} where
  Adj i j := i ≠ j ∧ blocks i.1 ∩ blocks j.1 = {s}
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance partnerGraphDecidableRel [DecidableEq ι] (blocks : ι → Finset P) (s : P) :
    DecidableRel (partnerGraph blocks s).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ blocks i.1 ∩ blocks j.1 = {s}))

omit [Fintype ι] in
@[simp] theorem partnerGraph_adj_iff (blocks : ι → Finset P) (s : P)
    (i j : {i : ι // s ∈ blocks i}) :
    (partnerGraph blocks s).Adj i j ↔ i ≠ j ∧ blocks i.1 ∩ blocks j.1 = {s} :=
  Iff.rfl

theorem card_blocksThrough_eq (blocks : ι → Finset P) (s : P) :
    Fintype.card {i : ι // s ∈ blocks i} = (blocksThrough blocks s).card := by
  rw [Fintype.card_subtype]
  rfl

/-- **The min-degree corollary**, stated subtraction-free.  In the partner graph
at `s`, every vertex misses at most `(k-1)(λ-1)` of the other vertices — so its
degree is at least `r - 1 - (k-1)(λ-1)`. -/
theorem card_le_degree_partnerGraph {blocks : ι → Finset P} (s : P)
    [DecidableRel (partnerGraph blocks s).Adj] {k lam : ℕ}
    (hk : ∀ i, (blocks i).card = k)
    (hlam : ∀ p q : P, p ≠ q →
      (Finset.univ.filter fun i => p ∈ blocks i ∧ q ∈ blocks i).card = lam)
    (i : {i : ι // s ∈ blocks i}) :
    Fintype.card {i : ι // s ∈ blocks i}
      ≤ (partnerGraph blocks s).degree i + 1 + (k - 1) * (lam - 1) := by
  classical
  -- the closed neighbourhood of `i`
  have hnotmem : i ∉ (partnerGraph blocks s).neighborFinset i := by simp
  have hAcard : (insert i ((partnerGraph blocks s).neighborFinset i)).card
      = (partnerGraph blocks s).degree i + 1 := Finset.card_insert_of_notMem hnotmem
  -- everything outside it is a HEAVY block
  have hsub : (Finset.univ \ insert i ((partnerGraph blocks s).neighborFinset i))
      ⊆ Finset.univ.filter fun j : {i : ι // s ∈ blocks i} =>
          j ≠ i ∧ 2 ≤ (blocks i.1 ∩ blocks j.1).card := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    obtain ⟨-, hj⟩ := hj
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, partnerGraph_adj_iff,
      not_or, not_and] at hj
    obtain ⟨hji, hjadj⟩ := hj
    have hnesing : blocks i.1 ∩ blocks j.1 ≠ {s} := hjadj (Ne.symm hji)
    have hmem : s ∈ blocks i.1 ∩ blocks j.1 := Finset.mem_inter.mpr ⟨i.2, j.2⟩
    have h2 : 2 ≤ (blocks i.1 ∩ blocks j.1).card := by
      by_contra hcon
      have h1 : 1 ≤ (blocks i.1 ∩ blocks j.1).card := Finset.card_pos.mpr ⟨s, hmem⟩
      have hcard1 : (blocks i.1 ∩ blocks j.1).card = 1 := by omega
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard1
      rw [ht, Finset.mem_singleton] at hmem
      exact hnesing (by rw [ht, hmem])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji, h2⟩
  -- and the heavy blocks are few, by Lemma 1 (transported along `Subtype.val`)
  have hbad : (Finset.univ.filter fun j : {i : ι // s ∈ blocks i} =>
      j ≠ i ∧ 2 ≤ (blocks i.1 ∩ blocks j.1).card).card ≤ (k - 1) * (lam - 1) := by
    have himg : ((Finset.univ.filter fun j : {i : ι // s ∈ blocks i} =>
          j ≠ i ∧ 2 ≤ (blocks i.1 ∩ blocks j.1).card).image Subtype.val)
        ⊆ (blocksThrough blocks s).filter
            fun j => j ≠ i.1 ∧ 2 ≤ (blocks i.1 ∩ blocks j).card := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨j, ⟨hji, hjc⟩, rfl⟩ := hx
      exact Finset.mem_filter.mpr
        ⟨mem_blocksThrough.mpr j.2, fun h => hji (Subtype.ext h), hjc⟩
    calc (Finset.univ.filter fun j : {i : ι // s ∈ blocks i} =>
            j ≠ i ∧ 2 ≤ (blocks i.1 ∩ blocks j.1).card).card
        = ((Finset.univ.filter fun j : {i : ι // s ∈ blocks i} =>
            j ≠ i ∧ 2 ≤ (blocks i.1 ∩ blocks j.1).card).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ ((blocksThrough blocks s).filter
            fun j => j ≠ i.1 ∧ 2 ≤ (blocks i.1 ∩ blocks j).card).card :=
          Finset.card_le_card himg
      _ ≤ (k - 1) * (lam - 1) := card_heavy_le hk hlam s i.2
  have hsplit : (Finset.univ \ insert i ((partnerGraph blocks s).neighborFinset i)).card
      + (insert i ((partnerGraph blocks s).neighborFinset i)).card
      = (Finset.univ : Finset {i : ι // s ∈ blocks i}).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ] at hsplit
  omega

/-! ### The generic headline

Composition with `Conway99.Dirac`: an even replication number and a small enough
`(k-1)(λ-1)` force a perfect matching of the partner graph. -/

/-- **Generic zero-power theorem.**  If the number of blocks through `s` is
`2m` and `1 + (k-1)(λ-1) ≤ m`, then the partner graph at `s` has minimum degree
`≥ m` and therefore a perfect matching.  No hypothesis on block intersections
appears anywhere. -/
theorem exists_perfectMatching_partnerGraph {blocks : ι → Finset P} {k lam m : ℕ}
    (hk : ∀ i, (blocks i).card = k)
    (hlam : ∀ p q : P, p ≠ q →
      (Finset.univ.filter fun i => p ∈ blocks i ∧ q ∈ blocks i).card = lam)
    (s : P) (hr : Fintype.card {i : ι // s ∈ blocks i} = 2 * m)
    (hsmall : 1 + (k - 1) * (lam - 1) ≤ m) :
    ∃ M : (partnerGraph blocks s).Subgraph, M.IsPerfectMatching := by
  classical
  refine exists_perfectMatching_of_card_eq_two_mul (partnerGraph blocks s) hr fun i => ?_
  have hdeg := card_le_degree_partnerGraph s hk hlam i
  rw [hr] at hdeg
  set Q := (k - 1) * (lam - 1)
  omega

end Designs

/-! ### The 2-(22,4,2) instantiation: `r = 14`, degree `≥ 10 ≥ 7` -/

section TwentyTwo

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {ι : Type*} [Fintype ι]

/-- In a 2-(22,4,2) design every point lies in exactly 14 blocks (`14·3 = 21·2`,
from `replication_mul`). -/
theorem card_blocksThrough_22_4_2 {blocks : ι → Finset P}
    (h : IsDesignWith blocks 22 4 2) (s : P) :
    (blocksThrough blocks s).card = 14 := by
  have hrep := replication_mul h.block_card h.pair_count s
  rw [h.card_points] at hrep
  omega

/-- The partner graph of a 2-(22,4,2) design has exactly 14 vertices at every
point — an EVEN number, which is what the matching lemma needs. -/
theorem card_partner_vertices_22_4_2 {blocks : ι → Finset P}
    (h : IsDesignWith blocks 22 4 2) (s : P) :
    Fintype.card {i : ι // s ∈ blocks i} = 14 := by
  rw [card_blocksThrough_eq, card_blocksThrough_22_4_2 h s]

/-- **Degree ten, unconditionally.**  In every 2-(22,4,2) design, every vertex of
every partner graph has degree at least `13 - 3·1 = 10`.  The external
deliverable obtained `10` only under C1 (where the graph is 10-REGULAR); the
bound here needs no such hypothesis. -/
theorem ten_le_partner_degree {blocks : ι → Finset P} (s : P)
    [DecidableRel (partnerGraph blocks s).Adj]
    (h : IsDesignWith blocks 22 4 2) (i : {i : ι // s ∈ blocks i}) :
    10 ≤ (partnerGraph blocks s).degree i := by
  have hb := card_le_degree_partnerGraph s h.block_card h.pair_count i
  rw [card_blocksThrough_eq, card_blocksThrough_22_4_2 h s] at hb
  omega

/-- **THE HEADLINE — "C2" can never fail.**  In EVERY 2-(22,4,2) design
whatsoever, at every point `s`, the 14 blocks through `s` pair up into 7
couples that meet exactly in `{s}`.  A search that filters candidate designs by
this predicate therefore has provably ZERO POWER: it removes nothing.

This is unconditional — in particular it does not assume C1 ("every two blocks
meet in at most 2 points"), which is what the external argument needed. -/
theorem c2_always_holds {blocks : ι → Finset P}
    (h : IsDesignWith blocks 22 4 2) (s : P) :
    ∃ M : (partnerGraph blocks s).Subgraph, M.IsPerfectMatching := by
  refine exists_perfectMatching_partnerGraph (m := 7) h.block_card h.pair_count s ?_ (by norm_num)
  rw [card_blocksThrough_eq, card_blocksThrough_22_4_2 h s]

end TwentyTwo

/-! ### Non-vacuity: the Fano plane, and the Fano plane DOUBLED

The doubling is the important one — it is a genuine 2-(7,3,2) design in which
every block occurs twice, so it exercises the "repeated blocks allowed"
presentation, and it has an EVEN replication number, so the perfect-matching
theorem actually fires on it. -/

section Fano

/-- The Fano plane 2-(7,3,1) on `Fin 7`, from the difference set `{0,1,3}`. -/
def fanoBlocks (i : Fin 7) : Finset (Fin 7) := {i, i + 1, i + 3}

theorem fanoBlocks_card : ∀ i, (fanoBlocks i).card = 3 := by decide

theorem fano_pair_count : ∀ p q : Fin 7, p ≠ q →
    (Finset.univ.filter fun i => p ∈ fanoBlocks i ∧ q ∈ fanoBlocks i).card = 1 := by decide

theorem fano_isDesign : IsDesignWith fanoBlocks 7 3 1 :=
  ⟨by simp, fanoBlocks_card, fano_pair_count⟩

/-- `card_heavy_le` FIRES on the Fano plane and gives the sharp answer: with
λ = 1 the bound is `(3-1)·(1-1) = 0`, i.e. two distinct lines through a point
never meet in two points.

This is a bound on an EMPTY set, so it does not by itself show the lemma is
non-vacuous; `fano2_heavy_nonempty` below does that. -/
theorem fano_heavy_empty (s : Fin 7) {i : Fin 7} (hi : s ∈ fanoBlocks i) :
    ((blocksThrough fanoBlocks s).filter
      fun j => j ≠ i ∧ 2 ≤ (fanoBlocks i ∩ fanoBlocks j).card).card = 0 := by
  have h := card_heavy_le fanoBlocks_card fano_pair_count s hi
  omega

/-- The Fano plane with every block DOUBLED: a 2-(7,3,2) design on 14 indices in
which `blocks` is very far from injective. -/
def fano2Blocks (i : Fin 7 × Bool) : Finset (Fin 7) := fanoBlocks i.1

theorem fano2_pair_count : ∀ p q : Fin 7, p ≠ q →
    (Finset.univ.filter fun i => p ∈ fano2Blocks i ∧ q ∈ fano2Blocks i).card = 2 := by decide

theorem fano2_isDesign : IsDesignWith fano2Blocks 7 3 2 :=
  ⟨by simp, fun i => fanoBlocks_card i.1, fano2_pair_count⟩

/-- Every point lies in `6 = 2·3` of the doubled blocks (`6·2 = 6·2`, from
`replication_mul`) — an EVEN replication number, so the matching theorem
applies. -/
theorem fano2_replication (s : Fin 7) : (blocksThrough fano2Blocks s).card = 6 := by
  have hrep := replication_mul fano2_isDesign.block_card fano2_isDesign.pair_count s
  rw [fano2_isDesign.card_points] at hrep
  omega

/-- The generic theorem FIRES: `1 + (3-1)(2-1) = 3 ≤ 3`, so the partner graph of
the doubled Fano plane at any point has a perfect matching. -/
theorem fano2_partner_perfectMatching (s : Fin 7) :
    ∃ M : (partnerGraph fano2Blocks s).Subgraph, M.IsPerfectMatching := by
  refine exists_perfectMatching_partnerGraph (m := 3) fano2_isDesign.block_card
    fano2_isDesign.pair_count s ?_ (by norm_num)
  rw [card_blocksThrough_eq, fano2_replication s]

/-- **Lemma 1 is instantiated at an INHABITED set here.**  At `s = 0` the block
`(0, true)` has exactly one heavy companion among the blocks through `0` — its
own duplicate `(0, false)`, which meets it in all three points.  So the set
`card_heavy_le` bounds is not empty, and the bound is not the classic vacuous
"≤ something, of an empty set". -/
theorem fano2_heavy_card :
    ((blocksThrough fano2Blocks (0 : Fin 7)).filter fun j =>
      j ≠ (0, true) ∧ 2 ≤ (fano2Blocks (0, true) ∩ fano2Blocks j).card).card = 1 := by
  decide

/-- The same fact in the shape the audit asks for, paired with the instance of
`card_heavy_le` that bounds it: the heavy set at `s = 0`, `i = (0, true)` is
NONEMPTY, and Lemma 1 caps it at `(3-1)·(2-1) = 2`. -/
theorem fano2_heavy_nonempty :
    0 < ((blocksThrough fano2Blocks (0 : Fin 7)).filter fun j =>
          j ≠ (0, true) ∧ 2 ≤ (fano2Blocks (0, true) ∩ fano2Blocks j).card).card ∧
      ((blocksThrough fano2Blocks (0 : Fin 7)).filter fun j =>
          j ≠ (0, true) ∧ 2 ≤ (fano2Blocks (0, true) ∩ fano2Blocks j).card).card
        ≤ (3 - 1) * (2 - 1) :=
  ⟨by rw [fano2_heavy_card]; exact Nat.one_pos,
   card_heavy_le fano2_isDesign.block_card fano2_isDesign.pair_count 0 (by decide)⟩

/-- The partner graph is INHABITED: two different lines through `0` are
partners. -/
theorem fano2_partner_adj :
    (partnerGraph fano2Blocks (0 : Fin 7)).Adj ⟨(0, true), by decide⟩ ⟨(4, true), by decide⟩ := by
  decide

/-- …and it is NOT complete: the two copies of one line meet in three points, so
they are not partners.  So the partner graph here is neither empty nor
complete, and the conclusion of the matching theorem is not free. -/
theorem fano2_partner_not_adj :
    ¬ (partnerGraph fano2Blocks (0 : Fin 7)).Adj
        ⟨(0, true), by decide⟩ ⟨(0, false), by decide⟩ := by
  decide

/-- HOW MUCH SLACK the witness has, checked rather than asserted in prose: the
doubled-Fano partner graph at `0` is `K_{2,2,2}` (only the duplicate pairs are
non-edges), so EVERY degree is `4` — one MORE than the `m = 3` the matching
theorem needs.  The witness therefore shows the hypotheses fire, not that they
are tight.  For tightness see `Conway99.C4` in `Dirac.lean`. -/
theorem fano2_degree_eq_four :
    ∀ i : {i : Fin 7 × Bool // (0 : Fin 7) ∈ fano2Blocks i},
      (partnerGraph fano2Blocks (0 : Fin 7)).degree i = 4 := by
  decide

/-- The min-degree corollary FIRES on the doubled Fano plane: `6 ≤ deg + 1 + 2`,
so every degree is at least 3 — exactly the `m = 3` that Dirac needs. -/
theorem fano2_three_le_degree (s : Fin 7) (i : {i : Fin 7 × Bool // s ∈ fano2Blocks i}) :
    3 ≤ (partnerGraph fano2Blocks s).degree i := by
  have hb := card_le_degree_partnerGraph s fano2_isDesign.block_card
    fano2_isDesign.pair_count i
  rw [card_blocksThrough_eq, fano2_replication s] at hb
  omega

end Fano

/-! ### Arithmetic of the derivation chain — ARITHMETIC ONLY

Everything in this section is a numeric identity.  None of it asserts the
Hoffman ratio bound (which this Mathlib cannot state for lack of the spectral
theory), and none of it asserts any value of the independence number α. -/

/-- The design identities behind "α ≤ 22 ⟹ a 2-(22,4,2) design with b = 77,
r = 14": the block count `99 - 22 = 77`, the pair count
`b·C(k,2) = λ·C(v,2)` with `C(22,2) = 231`, and the replication identity
`r(k-1) = λ(v-1)`.  ARITHMETIC ONLY — the implication itself is a literature
input (see the file docstring, non-claim 1). -/
theorem alpha22_chain_arithmetic :
    99 - 22 = 77 ∧ Nat.choose 22 2 = 231 ∧
      77 * Nat.choose 4 2 = 2 * Nat.choose 22 2 ∧ 14 * (4 - 1) = 2 * (22 - 1) := by
  refine ⟨by norm_num, by decide, by decide, by norm_num⟩

/-- The Hoffman ratio-bound EXPRESSION `v·(-s)/(k-s)` evaluates to `22` at
`(v,k,λ,μ) = (99,14,1,2)`, whose smallest eigenvalue is `s = -4`: written
without division, `99·4 = 22·(14 - (-4))`.  This is arithmetic; it is NOT the
ratio bound, and it does NOT claim `α = 22`. -/
theorem hoffman_ratio_value_99 : (99 : ℤ) * 4 = 22 * (14 - (-4)) := by norm_num

/-- The same expression evaluates to `9` at `(27,10,1,5)`, whose smallest
eigenvalue is `s = -5`: `27·5 = 9·(10 - (-5))`.  Recorded because the ratio
bound is NOT tight there — log 043 computes `α(srg(27,10,1,5)) = 6 < 9` in
Python, which is a citation and not a theorem of this file. -/
theorem hoffman_ratio_value_27 : (27 : ℤ) * 5 = 9 * (10 - (-5)) := by norm_num

end Conway99
