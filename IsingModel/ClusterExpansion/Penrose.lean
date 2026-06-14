import IsingModel.ClusterExpansion.Penrose.BooleanInterval
import IsingModel.ClusterExpansion.Penrose.SpanningTree
import IsingModel.ClusterExpansion.Penrose.PartitionScheme
import IsingModel.ClusterExpansion.Penrose.KruskalConnected
import IsingModel.ClusterExpansion.Penrose.KruskalAcyclic

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
-/
