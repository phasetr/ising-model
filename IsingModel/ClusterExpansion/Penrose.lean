import IsingModel.ClusterExpansion.Penrose.BooleanInterval
import IsingModel.ClusterExpansion.Penrose.SpanningTree
import IsingModel.ClusterExpansion.Penrose.PartitionScheme
import IsingModel.ClusterExpansion.Penrose.KruskalConnected
import IsingModel.ClusterExpansion.Penrose.KruskalAcyclic
import IsingModel.ClusterExpansion.Penrose.IntervalPartition
import IsingModel.ClusterExpansion.Penrose.TreeGraphBound
import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound
import IsingModel.ClusterExpansion.Penrose.SpanningTreeSummable

/-!
# Penrose tree-graph inequality (GJ §18.4-18.5) — umbrella

Unconditional, from-scratch development of the Penrose tree-graph (Ursell)
inequality `|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`, a key
remaining combinatorial input of general interacting cluster-expansion
convergence (Issue #3954).  Child modules:

* `BooleanInterval` — Boolean-interval signed-sum cancellation.
* `SpanningTree` — spanning-tree edge-subsets and their count.
* `PartitionScheme` — the Kruskal `treeOf` retraction and `addable` edges.
* `KruskalConnected` — `treeOf` preserves reachability, hence connectivity.
* `KruskalAcyclic` — `treeOf` is acyclic; for connected spanning `S`, `treeOf S` is a spanning tree.
* `IntervalPartition` — the `treeOf` fiber over a spanning tree is its Boolean interval.
* `TreeGraphBound` — the Penrose inequality
  `|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`.
* `CompleteGraphTreeBound` — the complete-graph spanning-tree count bound
  `numSpanningTrees (⊤ : SimpleGraph (Fin n)) ≤ n ^ (n - 1)` (summable majorant for M2).
* `SpanningTreeSummable` — absolute convergence of the Mayer majorant
  `∑ₙ numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n! · Rⁿ` for `e·|R| < 1` (radius `1/e`).
-/
