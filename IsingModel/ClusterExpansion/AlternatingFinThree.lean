import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Alternating connected-spanning sum on three vertices (GJ §18.4)

The complete classification of `alternatingConnectedSubgraphSum` for graphs on
`Fin 3`, extending the complete-graph value `alternatingConnectedSubgraphSum_K3`
(`= 2`).  A connected graph on three vertices is either the triangle (3 edges,
sum `2`) or a path (2 edges, sum `1`); a disconnected graph has sum `0`.  The
three path values (`alternatingConnectedSubgraphSum_fin_three_path_*`) are the
`n = 3` Mayer/Ursell numerators for a path-shaped incompatibility cluster
(`ϕ^T = 1/3! = 1/6`), the remaining connected case beyond the fully-incompatible
triangle (`ϕ^T = 2/3! = 1/3`, `ursellCoefficient_complete_eq`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer expansion), pp. 378–386.
-/

namespace IsingModel

open Finset

/-- **Path `0–1–2` alternating connected-spanning sum** (`edges {s(0,1), s(1,2)}`):
the only connected spanning edge-subset is the full pair, so the sum is `(-1)^2 = 1`. -/
theorem alternatingConnectedSubgraphSum_fin_three_path_01_12 :
    alternatingConnectedSubgraphSum (SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_set : connectedSpanningEdgeSubsets (SimpleGraph.fromEdgeSet
      (↑({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))
      = ({{s(0, 1), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3)))) := by decide
  rw [h_set]
  simp [Finset.sum_singleton]

/-- **Path `0–1, 0–2` alternating connected-spanning sum** (`edges {s(0,1), s(0,2)}`). -/
theorem alternatingConnectedSubgraphSum_fin_three_path_01_02 :
    alternatingConnectedSubgraphSum (SimpleGraph.fromEdgeSet
        (↑({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_set : connectedSpanningEdgeSubsets (SimpleGraph.fromEdgeSet
      (↑({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))
      = ({{s(0, 1), s(0, 2)}} : Finset (Finset (Sym2 (Fin 3)))) := by decide
  rw [h_set]
  simp [Finset.sum_singleton]

/-- **Path `0–2, 1–2` alternating connected-spanning sum** (`edges {s(0,2), s(1,2)}`). -/
theorem alternatingConnectedSubgraphSum_fin_three_path_02_12 :
    alternatingConnectedSubgraphSum (SimpleGraph.fromEdgeSet
        (↑({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_set : connectedSpanningEdgeSubsets (SimpleGraph.fromEdgeSet
      (↑({s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))
      = ({{s(0, 2), s(1, 2)}} : Finset (Finset (Sym2 (Fin 3)))) := by decide
  rw [h_set]
  simp [Finset.sum_singleton]

end IsingModel
