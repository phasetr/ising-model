import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.SignedSums

/-!
# Cluster expansion complete-graph alternating sums (3/4): the complete graph `K_4`

Structural split (3/4) of `IsingModel.ClusterExpansion.AlternatingCompleteGraph`.
This child holds the single Mayer Phase B base value `c(K_4) = -6`, proved by `decide` over
the powerset of the six edges of `K_4`.  It is isolated in its own module because that
kernel computation dominates the elaboration cost of the family.  See the
`IsingModel.ClusterExpansion.AlternatingCompleteGraph` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

set_option maxRecDepth 2000 in
/-- **`K_4` alternating sum = -6** (Mayer Phase B base case):
`(-1)^(4-1) · (4-1)! = -1 · 6 = -6`. The `connectedSpanningEdgeSubsets`
of K_4 has 38 elements (16 spanning trees of size 3, plus larger
connected subgraphs); the alternating sum of `(-1)^|S|` collapses to
`-6` by `decide` on the integer-valued sum, which reduces to a
finite filter over the powerset of K_4's 6 edges. -/
theorem alternatingConnectedSubgraphSum_K4 :
    alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin 4)) = -6 := by
  unfold alternatingConnectedSubgraphSum connectedSpanningEdgeSubsets
  -- Convert the real-valued sum to an integer-valued sum via cast.
  have h_int :
      (∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 4)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -6 := by decide +kernel
  have h_cast :
      (∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 4)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 4)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

end IsingModel
