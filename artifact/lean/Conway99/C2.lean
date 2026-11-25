/-
Conway99.C2 — the canonical form of an involution of a Conway 99-graph,
machine-checked (asymmetry-theorem campaign, notes/c2-quotient-design.md).

INPUT FROM THE LITERATURE (not re-proved here; Makhnev–Minakova 2004):
an order-2 automorphism of an srg(99,14,1,2) fixes EXACTLY ONE vertex.
That hypothesis enters below as `hfix`.

WHAT IS PROVED HERE (formalizing the design note's steps 1–2, previously
prose): given an automorphism σ with σ² = id fixing exactly the vertex f,

  * `nbhd_orbit_matched` (λ=1, μ=2): every neighbor u of f is ADJACENT to
    its image σu — i.e. every σ-orbit on N(f) is one of the matched pairs
    of the neighborhood matching.  Rooted at f, σ is therefore exactly
    the partner-swap, which is what `src/c2_instance.py` prescribes.
    (Proof: if u ≁ σu, the unique outside common neighbor w of the
    non-adjacent pair {u, σu} — `outside_common_neighbor` — has σw again
    a common neighbor, so σw ∈ {f, w}; either case forces a second fixed
    vertex.  Contradiction.)

  * `outside_orbit_coclique` (λ=1, any μ): for z not adjacent to f and
    z ≠ f, z is NOT adjacent to σz — the outside σ-orbits are cocliques.
    This is enrichment family E1 of the C2 instance (42 forced-false
    merged variables).  (Proof: the unique common neighbor of an
    adjacent pair {z, σz} would be σ-fixed, hence f, making z a neighbor
    of f.)

Together with the Lean lex-leader layer (the C2 instance is sbA plus
invariance equalities; the partner-swap is central in the residual
group, so `lexLeader_mixed_equisat` applies verbatim), this closes the
mathematical links of the C2 claim chain except the literature input.
-/
import Mathlib
import Conway99.SRG

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-- Every σ-orbit on the neighborhood of the unique fixed vertex is a
matched pair of the neighborhood matching. -/
theorem nbhd_orbit_matched
    (h : G.IsSRGWith n k 1 2) (σ : G ≃g G) (f : V)
    (hfix : ∀ v, σ v = v ↔ v = f) (hσ2 : ∀ v, σ (σ v) = v)
    {u : V} (hu : G.Adj f u) : G.Adj u (σ u) := by
  have hσf : σ f = f := (hfix f).mpr rfl
  have huf : u ≠ f := by
    rintro rfl
    exact G.irrefl hu
  have hσu_ne : σ u ≠ u := fun he => huf ((hfix u).mp he)
  by_contra hnadj
  have hu2 : G.Adj f (σ u) := by
    have hmap := σ.map_adj_iff.mpr hu
    rwa [hσf] at hmap
  obtain ⟨w, ⟨hwf, hwa, hwb, _⟩, huniq⟩ :=
    outside_common_neighbor h hu hu2 hnadj (Ne.symm hσu_ne)
  have h1 : G.Adj u (σ w) := by
    have hmap := σ.map_adj_iff.mpr hwb
    rwa [hσ2] at hmap
  have h2 : G.Adj (σ u) (σ w) := σ.map_adj_iff.mpr hwa
  rcases huniq (σ w) h1 h2 with hcase | hcase
  · -- σ w = f forces w = f (apply σ and use σ² = id)
    apply hwf
    have := congrArg σ hcase
    rwa [hσ2, hσf] at this
  · -- σ w = w forces w = f by the fixed-point hypothesis
    exact hwf ((hfix w).mp hcase)

/-- σ-orbits outside the closed neighborhood of the fixed vertex are
cocliques (enrichment family E1 of the C2 instance). -/
theorem outside_orbit_coclique
    (h : G.IsSRGWith n k 1 μ) (σ : G ≃g G) (f : V)
    (hfix : ∀ v, σ v = v ↔ v = f) (hσ2 : ∀ v, σ (σ v) = v)
    {z : V} (hz : ¬G.Adj f z) : ¬G.Adj z (σ z) := by
  intro hadj
  have hcard := h.of_adj z (σ z) hadj
  rw [Fintype.card_eq_one_iff] at hcard
  obtain ⟨⟨w, hw⟩, hall⟩ := hcard
  have hw' := (mem_commonNeighbors G).mp hw
  have h1 : G.Adj z (σ w) := by
    have hmap := σ.map_adj_iff.mpr hw'.2
    rwa [hσ2] at hmap
  have h2 : G.Adj (σ z) (σ w) := σ.map_adj_iff.mpr hw'.1
  have hmem : σ w ∈ G.commonNeighbors z (σ z) :=
    (mem_commonNeighbors G).mpr ⟨h1, h2⟩
  have heq := (hall ⟨σ w, hmem⟩).trans (hall ⟨w, hw⟩).symm
  have hww : σ w = w := congrArg Subtype.val heq
  have hwf : w = f := (hfix w).mp hww
  exact hz (hwf ▸ hw'.1).symm

end Conway99
