import IsingModel.ClusterExpansion.Penrose.BooleanInterval
import IsingModel.ClusterExpansion.Penrose.SpanningTree

/-!
# Penrose tree-graph inequality (GJ §18.4-18.5) — umbrella

Unconditional, from-scratch development of the Penrose tree-graph (Ursell)
inequality `|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`, the sole
remaining hard input of general interacting cluster-expansion convergence
(Issue #3954).  Child modules:

* `BooleanInterval` — Boolean-interval signed-sum cancellation.
* `SpanningTree` — spanning-tree edge-subsets and their count.
-/
