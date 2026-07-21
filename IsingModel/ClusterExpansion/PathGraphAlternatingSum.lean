import IsingModel.ClusterExpansion.AlternatingCompleteGraph.SignedSums
import IsingModel.TransferMatrix.PathGraphEdges
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# General closed form for the path-graph alternating connected-spanning sum

This file proves the general-`n` closed form

  `alternatingConnectedSubgraphSum (pathGraph (n+1)) = (-1)^n`,

replacing the previous family of per-`n` `decide`-based lemmas (which only covered
`n = 3, …, 8` vertices and required a raised `maxHeartbeats` budget at `pathGraph 8`).

The combinatorics is a pure edge count, with no tree/bridge theory involved: a
connected spanning subgraph of a graph on `n+1` vertices needs at least `n` edges
(`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`), while the path has
exactly `n` edges (`TransferMatrix.card_pathGraph_edgeFinset`).  The two bounds
squeeze, so the only connected spanning edge-subset is the full edge set and the
alternating sum collapses to the single term `(-1)^n`.

Besides subsuming the former per-`n` family this also covers the boundary cases
`n = 0` (`pathGraph 1`: one vertex, no edge, sum `1`) and `n = 1` (`pathGraph 2`:
one edge, sum `-1`).  The statement is deliberately given in the `pathGraph (n+1)`
form: `pathGraph 0` lives on the empty type `Fin 0`, which is never `Connected`,
so there `connectedSpanningEdgeSubsets = ∅` and the sum is `0`, not a power of `-1`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer expansion, Ursell coefficients).
-/

namespace IsingModel

open Finset SimpleGraph

/-- **Characterization of connected spanning edge-subsets of the path**: the only
connected spanning subset of `pathGraph (n+1)` is the full edge set `E`.

Forward direction: a connected spanning subgraph on `n+1` vertices has at least `n`
edges (`Connected.card_vert_le_card_edgeSet_add_one`); combined with `S ⊆ E` and
`|E| = n` (`TransferMatrix.card_pathGraph_edgeFinset`) this forces `S = E`.
Backward direction: `E` is connected (`SimpleGraph.pathGraph_connected`).

This is the path analogue of `cycleGraph_connectedSpanning_charac`; it is the
"the path is a tree" fact in the form needed for Glimm–Jaffe §18.4. -/
private theorem pathGraph_connectedSpanning_charac (n : ℕ) :
    connectedSpanningEdgeSubsets (pathGraph (n + 1))
      = {(pathGraph (n + 1)).edgeFinset} := by
  have hEcard : (pathGraph (n + 1)).edgeFinset.card = n :=
    TransferMatrix.card_pathGraph_edgeFinset n
  have hGE : SimpleGraph.fromEdgeSet
        (↑((pathGraph (n + 1)).edgeFinset) : Set (Sym2 (Fin (n + 1))))
      = pathGraph (n + 1) := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  ext S
  rw [mem_connectedSpanningEdgeSubsets, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hconn⟩
    -- The edge set of `fromEdgeSet ↑S` is `↑S` (no diagonal edges since `S ⊆ E`).
    have hES : (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin (n + 1))))).edgeSet
        = (↑S : Set (Sym2 (Fin (n + 1)))) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
      intro x hxS hxdiag
      have hxE : x ∈ (pathGraph (n + 1)).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp (hsub (Finset.mem_coe.mp hxS))
      have hnd : ¬ x.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ hxE
      exact hnd (Sym2.mem_diagSet.mp hxdiag)
    -- A connected spanning subgraph on `n+1` vertices has at least `n` edges.
    have hSge : n ≤ S.card := by
      have hc := hconn.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hES, Nat.card_coe_set_eq,
        Set.ncard_coe_finset] at hc
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hEcard]; exact hSge)
  · rintro rfl
    exact ⟨Finset.Subset.refl _, by rw [hGE]; exact pathGraph_connected n⟩

/-- **General closed form for the path-graph alternating connected-spanning sum**
(Mayer Phase B, Glimm–Jaffe §18.4): for every `n`,

  `alternatingConnectedSubgraphSum (pathGraph (n+1)) = (-1)^n`.

The full edge set is the unique connected spanning subset
(`pathGraph_connectedSpanning_charac`), so the alternating sum has the single term
`(-1)^|E| = (-1)^n`.  This subsumes the former per-`n` `decide` lemmas for
`pathGraph 3, …, 8` and additionally covers `pathGraph 1` (value `1`) and
`pathGraph 2` (value `-1`).  Spelled out in terms of the exponent `n`:
`n = 2 ↦ pathGraph 3 = 1`, `n = 3 ↦ pathGraph 4 = -1`, `n = 4 ↦ pathGraph 5 = 1`,
`n = 5 ↦ pathGraph 6 = -1`, `n = 6 ↦ pathGraph 7 = 1`, `n = 7 ↦ pathGraph 8 = -1`;
the corresponding Ursell coefficient of an `(n+1)`-vertex path cluster is
`ϕ^T = (-1)^n / (n+1)!`. -/
theorem alternatingConnectedSubgraphSum_pathGraph (n : ℕ) :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph (n + 1)) = (-1 : ℝ) ^ n := by
  unfold alternatingConnectedSubgraphSum
  rw [pathGraph_connectedSpanning_charac n, Finset.sum_singleton,
    TransferMatrix.card_pathGraph_edgeFinset n]

end IsingModel
