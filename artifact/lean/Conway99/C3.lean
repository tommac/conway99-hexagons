/-
Conway99.C3 — the canonical form of an order-3 automorphism of a Conway
99-graph, machine-checked (asymmetry-theorem campaign; sibling of C2.lean;
design inputs: src/c3_instance.py, notes/deep-research-c2c3-final.md).

INPUTS FROM THE LITERATURE (not re-proved here, mirroring how C2.lean
consumes Makhnev–Minakova through `hfix`):

  * Behbahani–Lam 2011 (doi:10.1016/j.disc.2010.10.005): an order-3
    automorphism of an srg(99,14,1,2) is FIXED-POINT-FREE.  It enters the
    theorems of section A below as the hypothesis `hfpf`; nothing in this
    file claims to derive it.

  * Equitable-partition spectral containment (standard algebraic graph
    theory — Godsil–Royle, *Algebraic Graph Theory*, ch. 9; applied to
    srg orbit matrices by Behbahani's 2009 thesis and Behbahani–Lam
    2011): the orbit partition of an automorphism is equitable, and the
    eigenvalue multiset of its quotient matrix is contained in the
    graph's spectrum with quotient multiplicities bounded by graph
    multiplicities.  For srg(99,14,1,2) (spectrum 14¹ 3⁵⁴ (−4)⁴⁴, and 14
    is an eigenvalue of the quotient since its rows sum to 14) this says:
    the 33 quotient eigenvalues are 14 (exactly once) plus 32 values in
    {3, −4}, and the trace is their sum.  That EXACT package — nothing
    stronger — enters `c3_trace_lemma` as the hypotheses `hcard`, `hmem`,
    `hsum`.  (Mathlib check, 2026-08-08: `Matrix.IsHermitian.eigenvalues`
    and the spectral theorem exist, but eigenvalue interlacing, equitable
    partitions/quotient spectra, and srg spectra do not — so the
    containment stays a clearly-marked hypothesis, not a `sorry`.)

WHAT IS PROVED HERE, sorry-free:

  A. CONJUGACY WLOG (no literature input).
     `cycleType_of_orderThree_fpf`: a fixed-point-free order-3 element of
     the symmetric group on 99 points has cycle type 3³³.
     `isConj_of_orderThree_fpf`: any two such elements are conjugate.
     `canonicalC3` with `canonicalC3_orderOf` / `canonicalC3_fpf` /
     `canonicalC3_orbit_apply` / `orbitEquiv_val`: the concrete
     g = (0 1 2)(3 4 5)⋯(96 97 98) of src/c3_instance.py, i.e.
     3i+a ↦ 3i+((a+1) mod 3), is such an element.
     `relabel_to_canonicalC3`: every fixed-point-free order-3 σ on Fin 99
     admits a relabeling p with p ∘ σ = canonicalC3 ∘ p (conjugation IS
     relabeling: the relabeled graph p(G) has automorphism p σ p⁻¹ = g).
     This is exactly the WLOG step of c3_instance.py's docstring.

  B. TRACE LEMMA t ∈ {6,13,20,27} (derivation input 2 of c3_instance.py,
     enrichment E1 / --fix-t).
     `c3_trace_core`: the sorry-free arithmetic core — 0 ≤ t ≤ 33,
     0 ≤ a ≤ 32 and 2t + 114 = 7a force
     (t,a) ∈ {(6,18), (13,20), (20,22), (27,24)}.
     `c3_trace_lemma`: the wrapper — from the spectral facts ABOVE as
     hypotheses plus the definitional facts tr C = 2t (a K₃ orbit
     contributes diagonal entry 2, others 0) and t ≤ 33, conclude
     t ∈ {6,13,20,27}.  The four --fix-t slices of c3_instance.py
     therefore exhaust the C3 search, modulo exactly the two literature
     inputs named above.
-/
import Mathlib
import Conway99.SRG

namespace Conway99

/-! ### A. Conjugacy WLOG for fixed-point-free order-3 permutations -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed-point-free element of order 3 in the symmetric group on a
99-element type has cycle type `3³³`: prime order makes every cycle a
3-cycle, and fixed-point-freeness makes the support all 99 points. -/
theorem cycleType_of_orderThree_fpf (hV : Fintype.card V = 99)
    (σ : Equiv.Perm V) (h3 : orderOf σ = 3) (hfpf : ∀ v, σ v ≠ v) :
    σ.cycleType = Multiset.replicate 33 3 := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order
    (show (orderOf σ).Prime by rw [h3]; exact Nat.prime_three)
  have hsupp : σ.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun v => Equiv.Perm.mem_support.mpr (hfpf v)
  have hsum : σ.cycleType.sum = 99 := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, hV]
  rw [hn, h3, Multiset.sum_replicate, smul_eq_mul] at hsum
  have h32 : n = 32 := by omega
  simpa [h3, h32] using hn

/-- Any two fixed-point-free order-3 elements of the symmetric group on a
99-element type are conjugate (equal cycle types `3³³`). -/
theorem isConj_of_orderThree_fpf (hV : Fintype.card V = 99)
    (σ τ : Equiv.Perm V) (hσ3 : orderOf σ = 3) (hσf : ∀ v, σ v ≠ v)
    (hτ3 : orderOf τ = 3) (hτf : ∀ v, τ v ≠ v) : IsConj σ τ :=
  Equiv.Perm.isConj_iff_cycleType_eq.mpr
    ((cycleType_of_orderThree_fpf hV σ hσ3 hσf).trans
      (cycleType_of_orderThree_fpf hV τ hτ3 hτf).symm)

/-- The orbit-structure equivalence `Fin 33 × Fin 3 ≃ Fin 99`, sending
`(i, a)` to the vertex `3i + a` (`orbitEquiv_val`): orbit `i` of the
canonical `g` is `{3i, 3i+1, 3i+2}`, the convention of
`src/c3_instance.py`. -/
def orbitEquiv : Fin 33 × Fin 3 ≃ Fin 99 :=
  finProdFinEquiv.trans (finCongr (by norm_num))

/-- `orbitEquiv` realizes the numeric labeling `(i, a) ↦ 3i + a`. -/
theorem orbitEquiv_val (i : Fin 33) (a : Fin 3) :
    (orbitEquiv (i, a) : ℕ) = 3 * (i : ℕ) + (a : ℕ) := by
  have h : (orbitEquiv (i, a) : ℕ) = (a : ℕ) + 3 * (i : ℕ) := rfl
  omega

/-- The canonical fixed-point-free order-3 permutation of `Fin 99`
prescribed by `src/c3_instance.py`: `g = (0 1 2)(3 4 5)⋯(96 97 98)`,
acting as the cyclic shift `a ↦ a + 1` on the `Fin 3` coordinate of every
orbit. -/
def canonicalC3 : Equiv.Perm (Fin 99) :=
  orbitEquiv.permCongr ((Equiv.refl (Fin 33)).prodCongr (finRotate 3))

/-- On orbit coordinates, `canonicalC3` is `3i+a ↦ 3i+((a+1) mod 3)` —
the exact adjacency-preserving shift `c3_instance.py` encodes. -/
theorem canonicalC3_orbit_apply (i : Fin 33) (a : Fin 3) :
    canonicalC3 (orbitEquiv (i, a)) = orbitEquiv (i, a + 1) := by
  have h : ∀ b : Fin 3, finRotate 3 b = b + 1 := by decide
  simp [canonicalC3, h]

/-- `canonicalC3` is fixed-point-free. -/
theorem canonicalC3_fpf (v : Fin 99) : canonicalC3 v ≠ v := by
  intro h
  have h2 := congrArg (fun w => (orbitEquiv.symm w).2) h
  -- the Fin 3 coordinate would satisfy `b + 1 = b` — impossible
  simp [canonicalC3] at h2

/-- `canonicalC3` cubes to the identity. -/
theorem canonicalC3_pow_three : canonicalC3 ^ 3 = 1 := by
  have hrot : ∀ b : Fin 3, finRotate 3 (finRotate 3 (finRotate 3 b)) = b := by
    decide
  ext v
  have h1 : ∀ w : Fin 99, canonicalC3 w =
      orbitEquiv ((orbitEquiv.symm w).1, finRotate 3 (orbitEquiv.symm w).2) :=
    fun _ => rfl
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, h1, Equiv.symm_apply_apply]
  rw [hrot]
  simp

/-- `canonicalC3` has order exactly 3. -/
theorem canonicalC3_orderOf : orderOf canonicalC3 = 3 :=
  orderOf_eq_prime canonicalC3_pow_three
    (fun h => canonicalC3_fpf 0 (by rw [h]; rfl))

/-- CONJUGACY WLOG, campaign form: every fixed-point-free order-3
permutation of `Fin 99` is carried to the canonical `g` by a relabeling
`p` — `p ∘ σ = g ∘ p`, i.e. `p σ p⁻¹ = g`.  If a graph `G` has
automorphism `σ`, the relabeled graph `p(G)` is invariant under `g`, so
prescribing `g` (as `c3_instance.py` does) loses no models. -/
theorem relabel_to_canonicalC3 (σ : Equiv.Perm (Fin 99))
    (h3 : orderOf σ = 3) (hfpf : ∀ v, σ v ≠ v) :
    ∃ p : Equiv.Perm (Fin 99), ∀ v, p (σ v) = canonicalC3 (p v) := by
  have hconj : IsConj σ canonicalC3 :=
    isConj_of_orderThree_fpf (Fintype.card_fin 99) σ canonicalC3 h3 hfpf
      canonicalC3_orderOf canonicalC3_fpf
  obtain ⟨p, hp⟩ := isConj_iff.mp hconj
  refine ⟨p, fun v => ?_⟩
  have hmul : p * σ = canonicalC3 * p := mul_inv_eq_iff_eq_mul.mp hp
  calc p (σ v) = (p * σ) v := (Equiv.Perm.mul_apply _ _ _).symm
    _ = (canonicalC3 * p) v := by rw [hmul]
    _ = canonicalC3 (p v) := Equiv.Perm.mul_apply _ _ _

/-! ### B. The trace lemma `t ∈ {6, 13, 20, 27}` -/

/-- Arithmetic core of the C3 trace lemma, fully proved: if `t ≤ 33`,
`a ≤ 32` and `2t + 114 = 7a` (the trace/multiplicity identity
`2t = 14 + 3a − 4(32 − a)` in ℕ-form), then `(t, a)` is one of
`(6,18), (13,20), (20,22), (27,24)`. -/
theorem c3_trace_core {t a : ℕ} (ht : t ≤ 33) (_ha : a ≤ 32)
    (heq : 2 * t + 114 = 7 * a) :
    (t = 6 ∧ a = 18) ∨ (t = 13 ∧ a = 20) ∨ (t = 20 ∧ a = 22) ∨
      (t = 27 ∧ a = 24) := by
  omega

/-- Bookkeeping: a multiset of integers drawn from `{3, −4}` sums to
`3a − 4b` where `a + b` is its cardinality. -/
theorem sum_of_mem_pair (s : Multiset ℤ) :
    (∀ x ∈ s, x = 3 ∨ x = -4) →
    ∃ a b : ℕ, a + b = Multiset.card s ∧
      s.sum = 3 * (a : ℤ) - 4 * (b : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, 0, by simp, by simp⟩
  | cons x s ih =>
    intro h
    obtain ⟨a, b, hab, hsum⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rcases h x (Multiset.mem_cons_self x s) with rfl | rfl
    · exact ⟨a + 1, b, by rw [Multiset.card_cons]; omega,
        by rw [Multiset.sum_cons, hsum]; push_cast; ring⟩
    · exact ⟨a, b + 1, by rw [Multiset.card_cons]; omega,
        by rw [Multiset.sum_cons, hsum]; push_cast; ring⟩

/-- TRACE LEMMA (hypothesis form — mirrors C2.lean's `hfix` discipline).
Let `t` be the number of K₃-inducing orbits of a fixed-point-free order-3
automorphism of an srg(99,14,1,2) and `C` its 33×33 quotient matrix.

Hypotheses `hcard`/`hmem`/`hsum` are EXACTLY the equitable-partition
spectral containment package (LITERATURE INPUT, see the file header:
Godsil–Royle ch. 9; Behbahani 2009; Behbahani–Lam 2011): `s` is the
multiset of the 32 non-Perron quotient eigenvalues, each of them 3 or −4,
and `tr C` is `14 + s.sum`.  Hypotheses `ht` and `htrace` are
definitional facts of the quotient construction: `t ≤ 33` counts orbits,
and each K₃ orbit contributes diagonal entry 2 (others 0), so
`tr C = 2t`.

Conclusion: `t ∈ {6, 13, 20, 27}` — the four `--fix-t` slices of
`src/c3_instance.py` exhaust the C3 search. -/
theorem c3_trace_lemma (t : ℕ) (ht : t ≤ 33)
    (C : Matrix (Fin 33) (Fin 33) ℤ) (s : Multiset ℤ)
    (hcard : Multiset.card s = 32)
    (hmem : ∀ x ∈ s, x = 3 ∨ x = -4)
    (htrace : C.trace = 2 * (t : ℤ))
    (hsum : C.trace = 14 + s.sum) :
    t = 6 ∨ t = 13 ∨ t = 20 ∨ t = 27 := by
  obtain ⟨a, b, hab, hs⟩ := sum_of_mem_pair s hmem
  rw [hcard] at hab
  rw [htrace, hs] at hsum
  have heq : 2 * t + 114 = 7 * a := by omega
  rcases c3_trace_core ht (by omega) heq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end Conway99
