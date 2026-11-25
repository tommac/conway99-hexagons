/-
Conway99.SRG — the local structure theorems behind the canonical skeleton,
stated for ANY strongly regular graph with λ = 1 (and μ = 2 where needed),
using Mathlib's standard `SimpleGraph.IsSRGWith`.

These are the two mathematical facts the README's skeleton derivation
rests on:

  * `neighborhood_matching` (λ = 1): every neighbor `u` of `v` has exactly
    one common neighbor with `v` — i.e. the graph induced on ANY
    neighborhood is 1-regular, a perfect matching.  For srg(99,14,1,2)
    this is why N(0) carries the matching {1,2},...,{13,14}.

  * `outside_common_neighbor` (λ = 1, μ = 2): for non-adjacent neighbors
    `a ≠ b` of `v`, there is EXACTLY ONE vertex besides `v` adjacent to
    both — and it is NOT a neighbor of `v`.  For srg(99,14,1,2) this is
    the outside-vertex ↔ non-matched-pair bijection: each non-matched pair
    of N(0) has a unique outside common neighbor.

Together with `eq_of_common_adj` (adjacent pairs have v as their ONLY
other common neighbor — why no outside vertex attaches to a matched pair),
these justify steps 2–3 of the skeleton construction.  The remaining
formalization step — assembling them into the full WLOG theorem "srg
exists iff one extending the canonical skeleton exists" — is future work,
tracked in lean/README.md.
-/
import Mathlib

namespace Conway99

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {n k μ : ℕ}

/-- λ = 1: any two elements of a common neighborhood of an adjacent pair
coincide. -/
theorem unique_common_of_adj (h : G.IsSRGWith n k 1 μ) {a b : V}
    (hab : G.Adj a b) {x y : V}
    (hx : x ∈ G.commonNeighbors a b) (hy : y ∈ G.commonNeighbors a b) :
    x = y := by
  have hcard := h.of_adj a b hab
  rw [Fintype.card_eq_one_iff] at hcard
  obtain ⟨z, hz⟩ := hcard
  have h1 := hz ⟨x, hx⟩
  have h2 := hz ⟨y, hy⟩
  exact (congrArg Subtype.val h1).trans (congrArg Subtype.val h2).symm

/-- λ = 1: if `a ~ b` are adjacent and `v` is a common neighbor, then `v`
is the ONLY common neighbor.  (Skeleton use: vertex 0 is the unique common
neighbor of each matched pair, so no outside vertex attaches to both ends
of a matched pair.) -/
theorem eq_of_common_adj (h : G.IsSRGWith n k 1 μ) {v a b x : V}
    (hab : G.Adj a b) (hva : G.Adj a v) (hvb : G.Adj b v)
    (hxa : G.Adj a x) (hxb : G.Adj b x) : x = v :=
  unique_common_of_adj h hab
    ((mem_commonNeighbors G).mpr ⟨hxa, hxb⟩)
    ((mem_commonNeighbors G).mpr ⟨hva, hvb⟩)

/-- λ = 1: every neighbor `u` of `v` has EXACTLY ONE common neighbor with
`v`: the induced graph on any neighborhood is a perfect matching.  (For
srg(99,14,1,2): N(0) carries the fixed matching {1,2},...,{13,14}.) -/
theorem neighborhood_matching (h : G.IsSRGWith n k 1 μ) {v u : V}
    (huv : G.Adj v u) : ∃! w, G.Adj v w ∧ G.Adj u w := by
  have hcard := h.of_adj v u huv
  rw [Fintype.card_eq_one_iff] at hcard
  obtain ⟨⟨z, hz⟩, hall⟩ := hcard
  rw [mem_commonNeighbors] at hz
  refine ⟨z, hz, fun w hw => ?_⟩
  exact congrArg Subtype.val (hall ⟨w, (mem_commonNeighbors G).mpr hw⟩)

/-- λ = 1, μ = 2, the skeleton's key step: for non-adjacent neighbors
`a ≠ b` of `v` there is exactly one vertex `w ≠ v` adjacent to both `a`
and `b`; moreover `w` is NOT a neighbor of `v`.  (For srg(99,14,1,2):
each non-matched pair of N(0) has a unique common neighbor among the 84
outside vertices — the label bijection.) -/
theorem outside_common_neighbor (h : G.IsSRGWith n k 1 2) {v a b : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : ¬G.Adj a b) (hne : a ≠ b) :
    ∃ w, (w ≠ v ∧ G.Adj a w ∧ G.Adj b w ∧ ¬G.Adj v w) ∧
      ∀ x, G.Adj a x → G.Adj b x → x = v ∨ x = w := by
  classical
  have hcard : Fintype.card (G.commonNeighbors a b) = 2 :=
    h.of_not_adj hne hab
  have hfin : (G.commonNeighbors a b).toFinset.card = 2 := by
    rw [Set.toFinset_card]; exact hcard
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hfin
  have hv_mem : v ∈ (G.commonNeighbors a b).toFinset := by
    rw [Set.mem_toFinset, mem_commonNeighbors]
    exact ⟨hva.symm, hvb.symm⟩
  -- the common neighbor besides v is not itself a neighbor of v:
  -- otherwise a and b would be two distinct common neighbors of the
  -- ADJACENT pair (v, w), contradicting λ = 1.
  have hnot_nbr : ∀ w, w ∈ (G.commonNeighbors a b).toFinset → w ≠ v →
      ¬G.Adj v w := by
    intro w hw hwv hvw
    have hmem := Set.mem_toFinset.mp hw
    rw [mem_commonNeighbors] at hmem
    exact hne (unique_common_of_adj h hvw
      ((mem_commonNeighbors G).mpr ⟨hva, hmem.1.symm⟩)
      ((mem_commonNeighbors G).mpr ⟨hvb, hmem.2.symm⟩))
  have hmem_iff : ∀ z, z ∈ (G.commonNeighbors a b).toFinset ↔
      G.Adj a z ∧ G.Adj b z := by
    intro z
    rw [Set.mem_toFinset, mem_commonNeighbors]
  rw [hset] at hv_mem
  rcases Finset.mem_insert.mp hv_mem with rfl | hv_y
  · -- v = x, the other common neighbor is y
    refine ⟨y, ⟨fun hyv => hxy hyv.symm, ?_, ?_, ?_⟩, ?_⟩
    · exact ((hmem_iff y).mp (by rw [hset]; simp)).1
    · exact ((hmem_iff y).mp (by rw [hset]; simp)).2
    · exact hnot_nbr y (by rw [hset]; simp) fun hyv => hxy hyv.symm
    · intro z hza hzb
      have hz : z ∈ ({v, y} : Finset V) := by
        rw [← hset, hmem_iff]; exact ⟨hza, hzb⟩
      rcases Finset.mem_insert.mp hz with rfl | hzy
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_singleton.mp hzy)
  · -- v = y, the other common neighbor is x
    have hv_eq : v = y := Finset.mem_singleton.mp hv_y
    subst hv_eq
    refine ⟨x, ⟨fun hxv => hxy hxv, ?_, ?_, ?_⟩, ?_⟩
    · exact ((hmem_iff x).mp (by rw [hset]; simp)).1
    · exact ((hmem_iff x).mp (by rw [hset]; simp)).2
    · exact hnot_nbr x (by rw [hset]; simp) fun hxv => hxy hxv
    · intro z hza hzb
      have hz : z ∈ ({x, v} : Finset V) := by
        rw [← hset, hmem_iff]; exact ⟨hza, hzb⟩
      rcases Finset.mem_insert.mp hz with rfl | hzv
      · exact Or.inr rfl
      · exact Or.inl (Finset.mem_singleton.mp hzv)

end Conway99
