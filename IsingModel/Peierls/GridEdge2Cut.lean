import IsingModel.Peierls.GridEdge2

/-!
# Surjectivity of the coordinate-edge representation (FV §3.7.2)

Every undirected `latticeGraph 2` edge has a directed coordinate-edge representative: the
adjacency `∑ᵢ |xᵢ - yᵢ| = 1` forces the two endpoints to differ by a single unit vector, which
is exactly a `GridEdge2`. Together with `toSym2_injective` this makes `GridEdge2.toSym2` a
bijection onto the lattice edges, so the primal cut `cutEdges F` (a set of `Sym2` edges) can be
transported to a set of `GridEdge2` and dualized.

* `exists_axis_of_adj` — adjacency decomposes into a single coordinate step.
* `exists_gridEdge2_toSym2_eq` — surjectivity onto the lattice edges.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Adjacency is a single coordinate step**: if `x` and `y` are adjacent in `latticeGraph 2`,
they differ by exactly one unit vector (in one of the two orientations). -/
theorem exists_axis_of_adj {x y : Fin 2 → ℤ} (h : (latticeGraph 2).Adj x y) :
    ∃ k : Fin 2, y = x + unitVec2 k ∨ x = y + unitVec2 k := by
  have hsum : |x 0 - y 0| + |x 1 - y 1| = 1 := by
    have h' : (∑ i : Fin 2, |x i - y i|) = 1 := h
    rwa [Fin.sum_univ_two] at h'
  have ha := abs_nonneg (x 0 - y 0)
  have hb := abs_nonneg (x 1 - y 1)
  by_cases h0 : x 0 = y 0
  · -- the difference is in coordinate 1
    rw [h0, sub_self, abs_zero, zero_add] at hsum
    refine ⟨1, ?_⟩
    rcases (abs_eq zero_le_one).mp hsum with h1 | h1
    · -- `x 1 - y 1 = 1`: `x = y + e₁`
      right
      funext i; fin_cases i <;> simp [GridEdge2.unitVec2_apply, Pi.add_apply] <;> omega
    · -- `x 1 - y 1 = -1`: `y = x + e₁`
      left
      funext i; fin_cases i <;> simp [GridEdge2.unitVec2_apply, Pi.add_apply] <;> omega
  · -- the difference is in coordinate 0; coordinate 1 must agree
    have hx0 : x 0 - y 0 ≠ 0 := sub_ne_zero.mpr h0
    have hge : 1 ≤ |x 0 - y 0| := Int.one_le_abs hx0
    have hb1 : x 1 = y 1 := by
      have hz : |x 1 - y 1| = 0 := by omega
      rwa [abs_eq_zero, sub_eq_zero] at hz
    have hx1 : |x 0 - y 0| = 1 := by omega
    refine ⟨0, ?_⟩
    rcases (abs_eq zero_le_one).mp hx1 with hk | hk
    · -- `x 0 - y 0 = 1`: `x = y + e₀`
      right
      funext i; fin_cases i <;> simp [GridEdge2.unitVec2_apply, Pi.add_apply] <;> omega
    · -- `x 0 - y 0 = -1`: `y = x + e₀`
      left
      funext i; fin_cases i <;> simp [GridEdge2.unitVec2_apply, Pi.add_apply] <;> omega

/-- **Surjectivity onto the lattice edges**: every edge of `latticeGraph 2` is `GridEdge2.toSym2`
of some directed coordinate edge. -/
theorem exists_gridEdge2_toSym2_eq {e : Sym2 (Fin 2 → ℤ)}
    (he : e ∈ (latticeGraph 2).edgeSet) : ∃ g : GridEdge2, g.toSym2 = e := by
  induction e with
  | h x y =>
    have hadj : (latticeGraph 2).Adj x y := by rwa [SimpleGraph.mem_edgeSet] at he
    obtain ⟨k, hk | hk⟩ := exists_axis_of_adj hadj
    · -- `y = x + e_k`: the edge is `⟨x, k⟩`
      exact ⟨⟨x, k⟩, by rw [GridEdge2.toSym2, hk]⟩
    · -- `x = y + e_k`: the edge is `⟨y, k⟩`
      refine ⟨⟨y, k⟩, ?_⟩
      rw [GridEdge2.toSym2, ← hk, Sym2.eq_swap]

/-- The lattice edge of a directed coordinate edge, as an element of the edge set. -/
def GridEdge2.toEdgeSet (g : GridEdge2) : (latticeGraph 2).edgeSet :=
  ⟨g.toSym2, g.toSym2_isLatticeEdge⟩

/-- **`GridEdge2.toEdgeSet` is a bijection**: injective by `toSym2_injective` and surjective by
`exists_gridEdge2_toSym2_eq`. -/
theorem gridEdge2_toEdgeSet_bijective : Function.Bijective GridEdge2.toEdgeSet := by
  refine ⟨fun a b hab => GridEdge2.toSym2_injective (Subtype.ext_iff.mp hab), ?_⟩
  rintro ⟨e, he⟩
  obtain ⟨g, hg⟩ := exists_gridEdge2_toSym2_eq he
  exact ⟨g, Subtype.ext hg⟩

/-- **Directed coordinate edges biject with the lattice edges**: `GridEdge2 ≃
(latticeGraph 2).edgeSet`. The primal cut (a set of lattice edges) thus transports faithfully to
a set of `GridEdge2`, to be dualized for the contour count. -/
noncomputable def gridEdge2Equiv : GridEdge2 ≃ (latticeGraph 2).edgeSet :=
  Equiv.ofBijective GridEdge2.toEdgeSet gridEdge2_toEdgeSet_bijective

end IsingModel
