/-
Conway99.GradedInvariant — the composition principle that logs 031/032/037
run on, and the invariance of the two constraint SHAPES the campaign uses.

THE GAP THIS CLOSES.  `notes/math/graded-canonical.md` §1 states, as prose:

> **PROPOSITION.**  Let `Base` be the skeleton/SRG constraint set, `Lex` a
> lex-leader layer for the residual group `G`, and `C` any extra constraint
> set whose edge-variable projection is a union of `G`-orbits.  Then
> `Base ∧ Lex ∧ C` is satisfiable iff `Base ∧ C` is.

Three certified theorems ride on it — log 031's canonical-transition
exclusion and log 032's Theorems A and B — and until now it existed only as
that paragraph plus exhaustive computational checks (`g(POS) = POS` over all
645,120 group elements; `graded_canonical.py verify --full-group`).  This
file supplies the Lean name the paper must cite.

WHAT IS ACTUALLY NEW HERE — stated honestly.  `lexLeader_sound` was ALREADY
proved for an ARBITRARY constraint predicate `C` with an arbitrary invariance
hypothesis `hC`; it never cared what `C` says.  So the Proposition is an
INSTANTIATION of an existing theorem, not new mathematics, and the honest
content of this file is the glue that makes the instantiation explicit:

  * `SInvariant`        — the hypothesis `hC` of `lexLeader_sound`, named.
  * `SInvariant.and` / `.all` — invariance is closed under conjunction, so
                        `Base ∧ Extra` (or `Base ∧ C₁ ∧ … ∧ C_r`) satisfies
                        the hypothesis as soon as each conjunct does.  This
                        is the *whole* mathematical step of the Proposition's
                        (⇐) direction beyond `lexLeader_sound`.
  * `gradedInvariant_equisat` — the Proposition in the shape the campaign
                        uses: `Base ∧ Extra` both `S`-invariant, lex-leader
                        constraints for ANY subset of `S`, with ANY prefix
                        windows, under ANY single comparison order.  It
                        VISIBLY subsumes `lexLeader_mixed_equisat` and
                        `lexLeader_mixed_equisat_order`: both are re-derived
                        from it below (`gradedInvariant_subsumes_mixed`,
                        `gradedInvariant_subsumes_order`) by taking
                        `Extra = True`, resp. also `o = 1`.
  * `sInvariant_exists` — the Proposition's "extendable on its own
                        auxiliaries" hypothesis, named: a constraint set that
                        is the projection of a relation on (assignment, aux)
                        pairs is invariant as soon as the relation's
                        projection is.  What `cardtest` checks on the Python
                        side is exactly this hypothesis for the sequential
                        counter; nothing here proves it OF that encoding
                        (that is the CNF layer — informal item 1).

THE TWO SHAPES (the second half of the file).  Every `G`-invariant family
built in logs 031/032/037 has one of exactly two shapes, and each is proved
`S`-invariant here ONCE, for all of them:

  * FIXED-SET (`AgreesOn` / `agreesOn_sInvariant`) — "the assignment agrees
    with a fixed partial assignment `v` on a position set `U`", where `U` is
    setwise invariant and `v` is invariant along the action.  This is log
    031's 924 canonical unit clauses (84 positive + 840 negative).  Its two
    hypotheses `hU` / `hv` are also EXACTLY the hypotheses of log 032 §9's
    Proposition ("a `G`-invariant unit set cannot benefit from lex
    reordering"), whose content — every position of `U` is a lex TIE — is
    proved here too, as `agreesOn_lex_tie`.
  * COUNTING (`countProfile` / `counting_sInvariant`) — positions are
    partitioned into blocks permuted by `S` (for the campaign: the 14
    canonical sextets, `G` permuting them as blocks — log 037's check S2),
    and the constraint depends only on the MULTISET of per-block counts.
    This covers `D ≥ m`, `NBAD ≤ k`, `MAXD ≥ t` and log 037's second-root
    deficit cells `SEC ≤ j` / `SEC ≥ t` — see the three named corollaries at
    the end, which are the campaign's families verbatim.
  * AGREEMENT COUNTING (`agreeProfile` / `agree_sInvariant`) — the counting
    shape against a fixed reference valuation `v` instead of against `true`.
    `graded_canonical.py`'s FOURTH family, `--cmin` (`c ≥ m` of the 924
    SIGNED canonical literals — 84 positive + 840 negative), is a
    cardinality constraint over MIXED-SIGN literals and is therefore NOT a
    function of the multiset of per-block TRUE counts: it needs this shape.
    `agreeCount_true` / `countProfile_eq_agreeProfile` show the plain
    counting shape is the special case `v ≡ true`, so this section subsumes
    the previous one; both are kept because `NBAD` / `MAXD` / `SEC` read
    more naturally as true-counts.  (No CERTIFIED rung uses `--cmin` — the
    certified `D` rungs are `--dmin`, a cardinality over the 84 positives
    alone, hence genuinely a true-count — but the family is live in the
    code and in `graded-canonical.md` §2, so it is covered here rather than
    left as a caveat.)

SCOPE — what this file does NOT do.  Exactly as in `T2Lex.lean`: everything
here is about abstract position vectors `Fin n → Bool` and finite sets of
position permutations.  Two links stay where they already were, neither
improved nor degraded:
  (a) that the CNF clause sets the solver saw project onto these predicates
      (the encoder/lex-clause layer — informal items 1 and 6b of
      `lean/README.md`), and
  (b) that the concrete edge-slot frame `EdgeSlot` is numbered by
      `Fin 3486` in `symmetry.edge_positions()`' order, and that the wreath
      image `edgeSlotPerm` is the `S` used (its nonemptiness and
      composition-closure ARE proved — `Group.edgeSlotPerm_comp`).
The block-permutation hypothesis `BlocksPermuted` is likewise a HYPOTHESIS
here; that `G` permutes the 14 canonical sextets as blocks is the exhaustive
645,120-element Python check (log 037 S2), not a Lean theorem.
-/
import Mathlib
import Conway99.LexLeader

namespace Conway99

variable {n : ℕ}

/-! ### `S`-invariance, and closure under conjunction -/

/-- `SInvariant S C`: the constraint predicate `C` is preserved by every
element of `S`.  This is verbatim the hypothesis `hC` of `lexLeader_sound`
(`∀ p ∈ S, ∀ x, C x → C (permApply p x)`), given a name so that the
composition principle can be stated in the campaign's vocabulary. -/
def SInvariant (S : Finset (Equiv.Perm (Fin n))) (C : (Fin n → Bool) → Prop) : Prop :=
  ∀ p ∈ S, ∀ x, C x → C (permApply p x)

/-- **Conjunction of invariant constraints is invariant.**  This is the only
mathematical step the graded Proposition adds to `lexLeader_sound`: the base
instance and the extra `G`-invariant family are conjoined, and the conjunction
still satisfies the hypothesis the lex-leader theorem consumes. -/
theorem SInvariant.and {S : Finset (Equiv.Perm (Fin n))} {C₁ C₂ : (Fin n → Bool) → Prop}
    (h₁ : SInvariant S C₁) (h₂ : SInvariant S C₂) :
    SInvariant S (fun x => C₁ x ∧ C₂ x) :=
  fun p hp x hx => ⟨h₁ p hp x hx.1, h₂ p hp x hx.2⟩

/-- The same for a finite list of constraint families (the campaign adds
several `G`-invariant families at once — e.g. a cardinality ladder rung
together with a nesting constraint). -/
theorem SInvariant.all {S : Finset (Equiv.Perm (Fin n))}
    (Cs : List ((Fin n → Bool) → Prop)) (h : ∀ C ∈ Cs, SInvariant S C) :
    SInvariant S (fun x => ∀ C ∈ Cs, C x) :=
  fun p hp x hx C hC => h C hC p hp x (hx C hC)

/-- The trivial constraint is invariant (used to exhibit the earlier
lex-leader theorems as special cases of `gradedInvariant_equisat`). -/
theorem sInvariant_true (S : Finset (Equiv.Perm (Fin n))) :
    SInvariant S (fun _ : Fin n → Bool => True) :=
  fun _ _ _ _ => trivial

/-- **The "extendable on its own auxiliaries" hypothesis of the graded
Proposition, named.**  A constraint family presented as the projection of a
relation `Ψ` between edge assignments and auxiliary assignments (the
sequential-counter aux variables of `graded_canonical.py`) is `S`-invariant as
soon as every moved assignment still admits SOME auxiliary extension.  On the
Python side that is what `cardtest` verifies exhaustively for `n ≤ 8`; this
lemma only records where the hypothesis enters, it does not prove it of any
particular encoding. -/
theorem sInvariant_exists {α : Type*} {S : Finset (Equiv.Perm (Fin n))}
    (Ψ : (Fin n → Bool) → α → Prop)
    (hΨ : ∀ p ∈ S, ∀ x a, Ψ x a → ∃ a', Ψ (permApply p x) a') :
    SInvariant S (fun x => ∃ a, Ψ x a) :=
  fun p hp x hx => hΨ p hp x hx.choose hx.choose_spec

/-! ### The composition principle -/

/-- **THE COMPOSITION PRINCIPLE** (`notes/math/graded-canonical.md` §1;
log 031, log 032 Theorems A and B).  Let `S` be a finite nonempty
composition-closed set of position permutations, `Base` an `S`-invariant
constraint set (the skeleton + SRG conditions) and `Extra` any other
`S`-invariant constraint set (a `G`-invariant graded family).  Then adding
lex-leader constraints for ANY subset of `S`, each with ITS OWN prefix window,
under ANY single comparison order `o`, preserves satisfiability EXACTLY.

In the campaign's words: any clause set whose edge-variable projection is a
union of `G`-orbits may be added to a lex-leader instance for free.

The proof is one line — `lexLeader_mixed_equisat_order` applied to the
conjunction — which is the point: this is an instantiation of a theorem that
was already proved for an arbitrary invariant predicate, not new mathematics.
The content is that the campaign's use is literally that instantiation. -/
theorem gradedInvariant_equisat
    (o : Equiv.Perm (Fin n))
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (Base Extra : (Fin n → Bool) → Prop)
    (hBase : SInvariant S Base) (hExtra : SInvariant S Extra)
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, Base x ∧ Extra x) ↔
      ∃ y, (Base y ∧ Extra y) ∧
        ∀ c ∈ cons, PrefixLexLe c.2 (permApply o y) (permApply (c.1 * o) y) :=
  lexLeader_mixed_equisat_order o S hne hmul (fun x => Base x ∧ Extra x)
    (hBase.and hExtra) cons hcons

/-- `lexLeader_mixed_equisat_order` is the special case `Extra = True`: the
composition principle VISIBLY subsumes the order-parameterized theorem the
v2/v3 per-orbit instances run on. -/
theorem gradedInvariant_subsumes_order
    (o : Equiv.Perm (Fin n))
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop) (hC : SInvariant S C)
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, C x) ↔
      ∃ y, C y ∧
        ∀ c ∈ cons, PrefixLexLe c.2 (permApply o y) (permApply (c.1 * o) y) := by
  simpa using
    gradedInvariant_equisat o S hne hmul C (fun _ => True) hC (sInvariant_true S) cons hcons

/-- `lexLeader_mixed_equisat` — the theorem `symbreak.py` runs on — is the
further special case `o = 1` (identity comparison order).  Together with
`gradedInvariant_subsumes_order` this exhibits BOTH pre-existing lex-leader
equisatisfiability theorems as instances of the composition principle. -/
theorem gradedInvariant_subsumes_mixed
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (C : (Fin n → Bool) → Prop) (hC : SInvariant S C)
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, C x) ↔ ∃ y, C y ∧ ∀ c ∈ cons, PrefixLexLe c.2 y (permApply c.1 y) := by
  have h := gradedInvariant_subsumes_order 1 S hne hmul C hC cons hcons
  simpa using h

/-! ### SHAPE 1 — the fixed-set family (log 031) -/

/-- `AgreesOn U v x`: the assignment `x` agrees with the fixed partial
assignment `v` on the position set `U`.  Log 031's constraint is exactly this
with `U` = the 924 canonical positions and `v` = the canonical valuation
(true on the 84 canonical transition slots, false on the other 840). -/
def AgreesOn (U : Finset (Fin n)) (v x : Fin n → Bool) : Prop := ∀ i ∈ U, x i = v i

/-- **SHAPE 1 IS `S`-INVARIANT.**  If the position set `U` is mapped into
itself by every element of `S`, and the fixed assignment `v` is itself
invariant along the action on `U`, then "agrees with `v` on `U`" is an
`S`-invariant constraint — so the composition principle applies and the
lex layer may be added for free.

For log 031: `U` is the canonical literal set, `hU` is `g(POS) = POS`
(machine-checked for all 645,120 group elements), and `hv` says the moved
position carries the same canonical value — jointly the statement that the
canonical transition system is the unique `G`-invariant one. -/
theorem agreesOn_sInvariant (S : Finset (Equiv.Perm (Fin n))) (U : Finset (Fin n))
    (v : Fin n → Bool)
    (hU : ∀ p ∈ S, ∀ i ∈ U, p i ∈ U)
    (hv : ∀ p ∈ S, ∀ i ∈ U, v (p i) = v i) :
    SInvariant S (AgreesOn U v) := by
  intro p hp x hx i hi
  change x (p i) = v i
  rw [hx (p i) (hU p hp i hi), hv p hp i hi]

/-- **Log 032 §9's Proposition, proved: a `G`-invariant unit set is all
ties.**  Under exactly the hypotheses of `agreesOn_sInvariant`, an assignment
satisfying the fixed-set constraint agrees with its own image at EVERY
position of `U`.  So in the lex comparison `x ≤ x ∘ p` those positions can
never fire the `¬x ∨ y` clause and pass the equality prefix through
unchanged: ordering `U` first is a no-op, which is why `D ≥ 84` and `D ≤ 0`
were unmoved by the canon-first order while partially-free rungs moved
several steps. -/
theorem agreesOn_lex_tie {S : Finset (Equiv.Perm (Fin n))} {U : Finset (Fin n)}
    {v : Fin n → Bool}
    (hU : ∀ p ∈ S, ∀ i ∈ U, p i ∈ U)
    (hv : ∀ p ∈ S, ∀ i ∈ U, v (p i) = v i)
    {x : Fin n → Bool} (hx : AgreesOn U v x) {p : Equiv.Perm (Fin n)} (hp : p ∈ S) :
    ∀ i ∈ U, permApply p x i = x i := by
  intro i hi
  change x (p i) = x i
  rw [hx (p i) (hU p hp i hi), hv p hp i hi, hx i hi]

/-! ### SHAPE 2 — the counting families (logs 032 and 037) -/

variable {β : Type*}

/-- `blockCount blk X b` — how many positions of block `b` the assignment `X`
sets to true.  Positions with `blk i = none` belong to no block and are
counted nowhere (for the campaign: the 3,402 edge slots outside the 84
canonical ones).  For the campaign's blocks, `blockCount` is the statistic
`d_a = |M_a ∩ canonical_a|` of root `a`. -/
def blockCount [DecidableEq β] (blk : Fin n → Option β) (X : Fin n → Bool) (b : β) : ℕ :=
  (Finset.univ.filter fun i => blk i = some b ∧ X i = true).card

/-- The MULTISET of per-block counts — the campaign's `(d_a)_{a ∈ N(x)}` read
without an ordering of the roots, which is the only thing a `G`-invariant
statistic may depend on. -/
def countProfile [Fintype β] [DecidableEq β] (blk : Fin n → Option β)
    (X : Fin n → Bool) : Multiset ℕ :=
  (Finset.univ : Finset β).val.map (blockCount blk X)

/-- `BlocksPermuted S blk`: every element of `S` permutes the blocks — it
carries block `b` onto block `τ b` for some permutation `τ` of the block
index type, and carries non-block positions to non-block positions.  For the
campaign this is "`G` permutes the 14 canonical sextets as blocks", checked
exhaustively over all 645,120 elements (log 037, check S2), both at label
level and through `symmetry.element_edge_perm`. -/
def BlocksPermuted (S : Finset (Equiv.Perm (Fin n))) (blk : Fin n → Option β) : Prop :=
  ∀ p ∈ S, ∃ τ : Equiv.Perm β, ∀ i, blk (p i) = (blk i).map τ

/-- Moving the assignment moves the block counts along `τ`. -/
theorem blockCount_permApply [DecidableEq β] (blk : Fin n → Option β)
    (X : Fin n → Bool) (p : Equiv.Perm (Fin n)) (τ : Equiv.Perm β)
    (hτ : ∀ i, blk (p i) = (blk i).map τ) (b : β) :
    blockCount blk (permApply p X) b = blockCount blk X (τ b) := by
  unfold blockCount
  refine Finset.card_equiv p ?_
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, permApply, hτ i]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; rfl, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases hb : blk i with
    | none => rw [hb] at h1; simp at h1
    | some y =>
      rw [hb] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      exact congrArg some (τ.injective h1)

/-- **The count profile is an invariant of the orbit.**  Permuting the
positions by any element that permutes the blocks leaves the MULTISET of
per-block counts unchanged (the individual counts are permuted). -/
theorem countProfile_permApply [Fintype β] [DecidableEq β] (blk : Fin n → Option β)
    (X : Fin n → Bool) (p : Equiv.Perm (Fin n)) (τ : Equiv.Perm β)
    (hτ : ∀ i, blk (p i) = (blk i).map τ) :
    countProfile blk (permApply p X) = countProfile blk X := by
  unfold countProfile
  have h1 : (Finset.univ : Finset β).val.map (blockCount blk (permApply p X))
      = (Finset.univ : Finset β).val.map (fun b => blockCount blk X (τ b)) :=
    Multiset.map_congr rfl fun b _ => blockCount_permApply blk X p τ hτ b
  have hperm : Multiset.map (⇑τ) (Finset.univ : Finset β).val
      = (Finset.univ : Finset β).val := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_val, Finset.map_univ_equiv]
  rw [h1, show (fun b => blockCount blk X (τ b)) = blockCount blk X ∘ (⇑τ) from rfl,
    ← Multiset.map_map, hperm]

/-- **SHAPE 2 IS `S`-INVARIANT.**  Any predicate whatsoever on the multiset of
per-block counts gives an `S`-invariant constraint — hence one that the
composition principle lets us add to a lex-leader instance for free.

This is the single theorem that covers EVERY graded family of logs 032 and
037 at once: `D ≥ m`, `NBAD ≤ k`, `MAXD ≥ t`, and the second-root deficit
cells `SEC ≤ j` / `SEC ≥ t`.  The three named corollaries below spell out the
first three; the `SEC` cells are predicates of the same kind (a bound on the
largest count together with a bound on the second largest). -/
theorem counting_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (hblk : BlocksPermuted S blk) (P : Multiset ℕ → Prop) :
    SInvariant S (fun X => P (countProfile blk X)) := by
  intro p hp X hX
  obtain ⟨τ, hτ⟩ := hblk p hp
  rwa [countProfile_permApply blk X p τ hτ]

/-- The `D ≥ m` family of log 032: the SUM of the per-block counts is at
least `m` (`Σ_a d_a ≥ m`, the certified rungs `m = 81, 79, 78`). -/
theorem graded_D_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (hblk : BlocksPermuted S blk) (m : ℕ) :
    SInvariant S (fun X => m ≤ (countProfile blk X).sum) :=
  counting_sInvariant blk hblk (fun ms => m ≤ ms.sum)

/-- The `NBAD ≤ k` family of log 032 — the best axis of the three, and the
one Theorem B is stated on: at most `k` blocks fail to be full (`w` = the
block width, 6 for the canonical sextets).  Certified at `k = 2`. -/
theorem graded_NBAD_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (hblk : BlocksPermuted S blk) (w k : ℕ) :
    SInvariant S (fun X => (countProfile blk X).countP (fun c => c < w) ≤ k) :=
  counting_sInvariant blk hblk (fun ms => ms.countP (fun c => c < w) ≤ k)

/-- Reading the `MAXD` predicate back off the profile: "some entry of the
count multiset is ≥ `t`" is "some block has count ≥ `t`". -/
theorem exists_mem_countProfile_iff [Fintype β] [DecidableEq β] (blk : Fin n → Option β)
    (X : Fin n → Bool) (t : ℕ) :
    (∃ c ∈ countProfile blk X, t ≤ c) ↔ ∃ b, t ≤ blockCount blk X b := by
  unfold countProfile
  constructor
  · rintro ⟨c, hc, hct⟩
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp hc
    exact ⟨b, hct⟩
  · rintro ⟨b, hb⟩
    exact ⟨blockCount blk X b, Multiset.mem_map.mpr ⟨b, by simp, rfl⟩, hb⟩

/-- The `MAXD ≥ t` family of log 032: SOME block has count at least `t`.
`MAXD ≥ 6` is, up to `G`-transport, exactly campaign orbit 00. -/
theorem graded_MAXD_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (hblk : BlocksPermuted S blk) (t : ℕ) :
    SInvariant S (fun X => ∃ c ∈ countProfile blk X, t ≤ c) :=
  counting_sInvariant blk hblk (fun ms => ∃ c ∈ ms, t ≤ c)

/-- **The principle, assembled on a counting family.**  The exact statement
the graded campaign consumes: base instance plus any multiset-of-block-counts
constraint, plus a lex-leader layer for any subset of `S` with any windows
under any single order — satisfiability preserved exactly.  Logs 031/032's
certified UNSAT results are refutations of the right-hand side; this theorem
is what transfers them to the left-hand side, i.e. to statements about
Conway 99-graphs. -/
theorem gradedInvariant_counting_equisat [Fintype β] [DecidableEq β]
    (o : Equiv.Perm (Fin n))
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (Base : (Fin n → Bool) → Prop) (hBase : SInvariant S Base)
    (blk : Fin n → Option β) (hblk : BlocksPermuted S blk) (P : Multiset ℕ → Prop)
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, Base x ∧ P (countProfile blk x)) ↔
      ∃ y, (Base y ∧ P (countProfile blk y)) ∧
        ∀ c ∈ cons, PrefixLexLe c.2 (permApply o y) (permApply (c.1 * o) y) :=
  gradedInvariant_equisat o S hne hmul Base _ hBase (counting_sInvariant blk hblk P) cons hcons

/-! ### SHAPE 2′ — agreement counting, for the MIXED-SIGN family (`--cmin`)

`graded_canonical.py --cmin` adds `c(X) ≥ m` where
`c(X) = #{POS slots set true} + #{NEG slots set false}` over the 924 SIGNED
canonical literals.  That is NOT a function of the multiset of per-block TRUE
counts — a true-count profile cannot see the 840 negative literals'
agreements — so `counting_sInvariant` does not reach it.  Counting
AGREEMENTS with a fixed reference valuation `v` does, and specializes back to
the true-count shape at `v ≡ true` (`agreeCount_true`,
`countProfile_eq_agreeProfile`). -/

/-- `agreeCount blk v X b` — how many positions of block `b` the assignment
`X` AGREES with the fixed reference valuation `v` on.  One block containing
all 924 canonical slots, with `v` the canonical valuation, gives `c(X)`. -/
def agreeCount [DecidableEq β] (blk : Fin n → Option β) (v X : Fin n → Bool) (b : β) : ℕ :=
  (Finset.univ.filter fun i => blk i = some b ∧ X i = v i).card

/-- The MULTISET of per-block agreement counts. -/
def agreeProfile [Fintype β] [DecidableEq β] (blk : Fin n → Option β)
    (v X : Fin n → Bool) : Multiset ℕ :=
  (Finset.univ : Finset β).val.map (agreeCount blk v X)

/-- Agreement with the constant-`true` valuation IS the true-count: SHAPE 2
is the special case `v ≡ true` of SHAPE 2′. -/
theorem agreeCount_true [DecidableEq β] (blk : Fin n → Option β) (X : Fin n → Bool) (b : β) :
    agreeCount blk (fun _ => true) X b = blockCount blk X b := rfl

theorem countProfile_eq_agreeProfile [Fintype β] [DecidableEq β]
    (blk : Fin n → Option β) (X : Fin n → Bool) :
    countProfile blk X = agreeProfile blk (fun _ => true) X := rfl

/-- `BlockValInvariant S blk v`: the reference valuation is constant along the
action at every position that lies in a block.  For log 031's 924 literals
this is `v(g t) = v(t)`, i.e. `g(POS) = POS` together with `g(NEG) = NEG` —
log 032's check V3, exhaustive over all 645,120 elements. -/
def BlockValInvariant (S : Finset (Equiv.Perm (Fin n))) (blk : Fin n → Option β)
    (v : Fin n → Bool) : Prop :=
  ∀ p ∈ S, ∀ i, blk i ≠ none → v (p i) = v i

/-- Moving the assignment moves the agreement counts along `τ`. -/
theorem agreeCount_permApply [DecidableEq β] (blk : Fin n → Option β)
    (v X : Fin n → Bool) (p : Equiv.Perm (Fin n)) (τ : Equiv.Perm β)
    (hτ : ∀ i, blk (p i) = (blk i).map τ)
    (hv : ∀ i, blk i ≠ none → v (p i) = v i) (b : β) :
    agreeCount blk v (permApply p X) b = agreeCount blk v X (τ b) := by
  unfold agreeCount
  refine Finset.card_equiv p ?_
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, permApply, hτ i]
  constructor
  · rintro ⟨h1, h2⟩
    have hne : blk i ≠ none := by rw [h1]; simp
    refine ⟨by rw [h1]; rfl, ?_⟩
    rw [h2]; exact (hv i hne).symm
  · rintro ⟨h1, h2⟩
    have hbi : blk i = some b := by
      cases hb : blk i with
      | none => rw [hb] at h1; simp at h1
      | some y =>
        rw [hb] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        exact congrArg some (τ.injective h1)
    have hne : blk i ≠ none := by rw [hbi]; simp
    refine ⟨hbi, ?_⟩
    rw [h2]; exact hv i hne

/-- The agreement profile is an invariant of the orbit. -/
theorem agreeProfile_permApply [Fintype β] [DecidableEq β] (blk : Fin n → Option β)
    (v X : Fin n → Bool) (p : Equiv.Perm (Fin n)) (τ : Equiv.Perm β)
    (hτ : ∀ i, blk (p i) = (blk i).map τ)
    (hv : ∀ i, blk i ≠ none → v (p i) = v i) :
    agreeProfile blk v (permApply p X) = agreeProfile blk v X := by
  unfold agreeProfile
  have h1 : (Finset.univ : Finset β).val.map (agreeCount blk v (permApply p X))
      = (Finset.univ : Finset β).val.map (fun b => agreeCount blk v X (τ b)) :=
    Multiset.map_congr rfl fun b _ => agreeCount_permApply blk v X p τ hτ hv b
  have hperm : Multiset.map (⇑τ) (Finset.univ : Finset β).val
      = (Finset.univ : Finset β).val := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_val, Finset.map_univ_equiv]
  rw [h1, show (fun b => agreeCount blk v X (τ b)) = agreeCount blk v X ∘ (⇑τ) from rfl,
    ← Multiset.map_map, hperm]

/-- **SHAPE 2′ IS `S`-INVARIANT.**  Any predicate on the multiset of per-block
AGREEMENT counts is `S`-invariant, given that `S` permutes the blocks and
fixes the reference valuation along the action. -/
theorem agree_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (v : Fin n → Bool)
    (hblk : BlocksPermuted S blk) (hv : BlockValInvariant S blk v)
    (P : Multiset ℕ → Prop) :
    SInvariant S (fun X => P (agreeProfile blk v X)) := by
  intro p hp X hX
  obtain ⟨τ, hτ⟩ := hblk p hp
  rwa [agreeProfile_permApply blk v X p τ hτ (hv p hp)]

/-- The `c ≥ m` family of `graded_canonical.py --cmin`: at least `m` of the
924 SIGNED canonical literals satisfied.  Take one block containing exactly
the 924 canonical slots and `v` the canonical valuation; then
`(agreeProfile blk v X).sum = c(X)`.  (No CERTIFIED rung uses this family —
the certified `D` rungs are `--dmin`, a cardinality over the 84 POSITIVES
alone, hence a genuine true-count covered by `graded_D_sInvariant` — but the
family is live in the code and in `graded-canonical.md` §2.) -/
theorem graded_c_sInvariant [Fintype β] [DecidableEq β] {S : Finset (Equiv.Perm (Fin n))}
    (blk : Fin n → Option β) (v : Fin n → Bool)
    (hblk : BlocksPermuted S blk) (hv : BlockValInvariant S blk v) (m : ℕ) :
    SInvariant S (fun X => m ≤ (agreeProfile blk v X).sum) :=
  agree_sInvariant blk v hblk hv (fun ms => m ≤ ms.sum)

/-- The principle assembled on an agreement-counting family — the `--cmin`
counterpart of `gradedInvariant_counting_equisat`. -/
theorem gradedInvariant_agree_equisat [Fintype β] [DecidableEq β]
    (o : Equiv.Perm (Fin n))
    (S : Finset (Equiv.Perm (Fin n))) (hne : S.Nonempty)
    (hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S)
    (Base : (Fin n → Bool) → Prop) (hBase : SInvariant S Base)
    (blk : Fin n → Option β) (v : Fin n → Bool)
    (hblk : BlocksPermuted S blk) (hv : BlockValInvariant S blk v)
    (P : Multiset ℕ → Prop)
    (cons : List (Equiv.Perm (Fin n) × ℕ))
    (hcons : ∀ c ∈ cons, c.1 ∈ S) :
    (∃ x, Base x ∧ P (agreeProfile blk v x)) ↔
      ∃ y, (Base y ∧ P (agreeProfile blk v y)) ∧
        ∀ c ∈ cons, PrefixLexLe c.2 (permApply o y) (permApply (c.1 * o) y) :=
  gradedInvariant_equisat o S hne hmul Base _ hBase (agree_sInvariant blk v hblk hv P)
    cons hcons

/-! ### NON-VACUITY — the hypotheses are neither empty nor free

Same discipline as `T2Lex.lean`'s `blockFull_falsifiable` /
`e2_needs_sigmaInvariant`.  Everything above is TRUE for degenerate data
(`U = ∅`, `blk ≡ none`, `β` empty, `P` constant) and would then say nothing.
The theorems here rule that reading out: the hypotheses are jointly
satisfiable with a NON-identity group element, a NON-constant reference
valuation and a FALSIFIABLE constraint that genuinely reads the block
structure — and each of the two invariance hypotheses is load-bearing, i.e.
dropping it makes the conclusion FALSE. -/

/-- The witness action: the double transposition `(0 2)(1 3)` of `Fin 4`. -/
def exPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- Two blocks of two, `{0,1}` and `{2,3}` — the toy model of the 14
canonical sextets. -/
def exBlk : Fin 4 → Option (Fin 2) := ![some 0, some 0, some 1, some 1]

theorem exPerm_apply : exPerm 0 = 2 ∧ exPerm 1 = 3 ∧ exPerm 2 = 0 ∧ exPerm 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `exPerm` permutes `exBlk`'s blocks (it swaps them), so `BlocksPermuted`
is satisfiable by a set containing a NON-identity element. -/
theorem exBlocksPermuted : BlocksPermuted {1, exPerm} exBlk := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact ⟨1, by decide⟩
  · rw [Finset.mem_singleton.mp hp]
    exact ⟨Equiv.swap 0 1, by decide⟩

/-- **The counting shape is not vacuous, and it genuinely reads the BLOCK
structure.**  Two assignments with the SAME total number of true positions —
so indistinguishable by any predicate on the raw count — are separated by the
`MAXD ≥ 2` predicate on the block-count multiset.  So `counting_sInvariant`
is not the invariance of a constant. -/
theorem counting_nondegenerate :
    (∃ c ∈ countProfile exBlk ![true, true, false, false], 2 ≤ c) ∧
    ¬ (∃ c ∈ countProfile exBlk ![true, false, true, false], 2 ≤ c) ∧
    (countProfile exBlk ![true, true, false, false]).sum
      = (countProfile exBlk ![true, false, true, false]).sum := by
  refine ⟨?_, ?_, ?_⟩
  · rw [exists_mem_countProfile_iff]; decide
  · rw [exists_mem_countProfile_iff]; decide
  · decide

/-- **`BlocksPermuted` is load-bearing.**  With blocks the SAME permutation
does NOT permute (sizes 3 and 1), the very same `MAXD ≥ 2` predicate holds at
an assignment and FAILS at its image — so `counting_sInvariant` without its
hypothesis is false, and log 037's exhaustive 645,120-element check S2 is
doing real work. -/
theorem counting_needs_blocksPermuted :
    ∃ (blk : Fin 4 → Option (Fin 2)) (X : Fin 4 → Bool),
      (∃ c ∈ countProfile blk X, 2 ≤ c) ∧
      ¬ (∃ c ∈ countProfile blk (permApply exPerm X), 2 ≤ c) := by
  refine ⟨![some 0, some 0, some 0, some 1], ![true, true, false, false], ?_, ?_⟩
  · rw [exists_mem_countProfile_iff]; decide
  · rw [exists_mem_countProfile_iff]; decide

/-- **The fixed-set shape is not vacuous either**: `U` nonempty, `v`
NON-constant on `U` (as log 031's is — 84 true, 840 false), a NON-identity
element satisfying both `hU` and `hv`, and a constraint that is both
satisfiable and falsifiable. -/
theorem agreesOn_nondegenerate :
    (∀ p ∈ ({1, exPerm} : Finset (Equiv.Perm (Fin 4))),
        ∀ i ∈ (Finset.univ : Finset (Fin 4)), p i ∈ (Finset.univ : Finset (Fin 4))) ∧
    (∀ p ∈ ({1, exPerm} : Finset (Equiv.Perm (Fin 4))),
        ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        (![true, false, true, false] : Fin 4 → Bool) (p i)
          = (![true, false, true, false] : Fin 4 → Bool) i) ∧
    (![true, false, true, false] : Fin 4 → Bool) 0
      ≠ (![true, false, true, false] : Fin 4 → Bool) 1 ∧
    AgreesOn Finset.univ (![true, false, true, false] : Fin 4 → Bool)
      ![true, false, true, false] ∧
    ¬ AgreesOn Finset.univ (![true, false, true, false] : Fin 4 → Bool) (fun _ => false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _ i _
    exact Finset.mem_univ _
  · intro p hp i hi
    clear hi
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rfl
    · have hpe : p = exPerm := Finset.mem_singleton.mp hp
      subst hpe
      revert i
      decide
  · decide
  · intro i _
    rfl
  · intro h
    have := h 0 (Finset.mem_univ 0)
    revert this
    decide

/-- **`hv` is load-bearing in `agreesOn_sInvariant`.**  With `U` setwise
invariant (`hU` holds) but the valuation NOT constant along the action, the
fixed-set constraint holds at an assignment and fails at its image. -/
theorem agreesOn_needs_hv :
    ∃ (v X : Fin 2 → Bool) (p : Equiv.Perm (Fin 2)),
      (∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ∈ (Finset.univ : Finset (Fin 2))) ∧
      AgreesOn Finset.univ v X ∧ ¬ AgreesOn Finset.univ v (permApply p X) := by
  refine ⟨![true, false], ![true, false], Equiv.swap 0 1, fun i _ => Finset.mem_univ _,
    fun i _ => rfl, ?_⟩
  intro h
  have := h 0 (Finset.mem_univ 0)
  revert this
  decide

end Conway99
