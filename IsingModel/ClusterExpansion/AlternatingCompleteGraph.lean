import IsingModel.ClusterExpansion.AlternatingCompleteGraph.SignedSums
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.CompleteGraphSmallCases
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.CompleteGraphK4
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.MayerConnectedFilter

/-!
# Cluster expansion complete-graph alternating sums

Mechanical child split from `ClusterExpansion.lean`.

## Contents

The declarations live in four child modules, re-exported by this declaration-free facade:

* `….AlternatingCompleteGraph.SignedSums` — the two signed-sum definitions
  (`alternatingConnectedSubgraphSum` over connected spanning edge-subsets,
  `allSignedSubgraphSum` = `D(G)` over all spanning edge-subsets), the general
  `D(G) = 0 / 1` evaluations, the edge-relabelling machinery and the graph-isomorphism
  invariance of both sums, the `K_V ≅ K_{Fin |V|}` card-transfer corollaries, the
  crossing-edge-free component lemma, and the complete-graph `D_n` boundary values.
* `….AlternatingCompleteGraph.CompleteGraphSmallCases` — the Mayer Phase B base values
  `c(K_0) = 0`, `c(K_1) = 1`, `c(K_2) = -1`, `c(K_3) = 2`, together with the `Fin 1 / Fin 2 /
  Fin 3` edge-set and connectivity helpers they need.
* `….AlternatingCompleteGraph.CompleteGraphK4` — the Mayer Phase B base value `c(K_4) = -6`,
  proved by `decide` over the powerset of the six edges of `K_4`.  Isolated in its own module
  because that kernel computation dominates the elaboration cost of the family.
* `….AlternatingCompleteGraph.MayerConnectedFilter` — the restriction of `mayerExpansionTerm`
  and `mayerPartialSum` to cluster sequences (polymer sequences whose index-side
  incompatibility graph is connected), plus the `n = 0` and `n = 1` evaluations of that
  filter.  Independent of the other three children.
-/
