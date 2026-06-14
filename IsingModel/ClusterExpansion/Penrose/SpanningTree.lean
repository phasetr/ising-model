import IsingModel.ClusterExpansion.Incompatibility
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Spanning-tree edge-subsets of a finite graph (Penrose tree-graph, GJ §18.4-18.5)

Unconditional infrastructure for the from-scratch Penrose tree-graph inequality
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G` (Issue #3954, the sole
remaining input of general interacting cluster-expansion convergence).

A *spanning tree* of a finite graph `G` is recorded as an edge-subset
`S ⊆ G.edgeFinset` whose spanned subgraph `fromEdgeSet ↑S` is connected and has
exactly `|V| - 1` edges (equivalently, a tree on `V`); `numSpanningTrees G`
counts them.  No hypothesis structures are introduced.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
- O. Penrose (1967); A. Cayley (1889).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.Penrose

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Spanning-tree edge-subsets**: connected spanning edge-subsets of `G` with
exactly `|V| - 1` edges (the spanning trees of `G`, recorded as edge sets). -/
noncomputable def spanningTreeEdgeSubsets : Finset (Finset (Sym2 V)) :=
  (connectedSpanningEdgeSubsets G).filter (fun S => S.card = Fintype.card V - 1)

/-- **Number of spanning trees** of a finite graph `G`. -/
noncomputable def numSpanningTrees : ℕ := (spanningTreeEdgeSubsets G).card

variable {G}

/-- **Membership in `spanningTreeEdgeSubsets`**: `S` is a spanning tree iff it is
a connected spanning edge-subset with `|V| - 1` edges. -/
theorem mem_spanningTreeEdgeSubsets {S : Finset (Sym2 V)} :
    S ∈ spanningTreeEdgeSubsets G ↔
      (S ⊆ G.edgeFinset ∧ (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).Connected)
        ∧ S.card = Fintype.card V - 1 := by
  rw [spanningTreeEdgeSubsets, Finset.mem_filter, mem_connectedSpanningEdgeSubsets]

/-- **Spanning trees are connected spanning edge-subsets**. -/
theorem spanningTreeEdgeSubsets_subset_connectedSpanning :
    spanningTreeEdgeSubsets G ⊆ connectedSpanningEdgeSubsets G :=
  Finset.filter_subset _ _

/-- **Spanning-tree edge-subsets are subsets of the edge set**. -/
theorem spanningTreeEdgeSubsets_subset_powerset :
    spanningTreeEdgeSubsets G ⊆ G.edgeFinset.powerset := by
  intro S hS
  exact Finset.mem_powerset.mpr
    (mem_connectedSpanningEdgeSubsets.mp
      (spanningTreeEdgeSubsets_subset_connectedSpanning hS)).1

variable (G)

/-- **The spanning-tree count is at most the connected-spanning-subgraph count**. -/
theorem numSpanningTrees_le_connectedSpanningEdgeSubsets_card :
    numSpanningTrees G ≤ (connectedSpanningEdgeSubsets G).card :=
  Finset.card_le_card spanningTreeEdgeSubsets_subset_connectedSpanning

/-- **The spanning-tree count is at most `2^{|E|}`**: every spanning tree is an
edge-subset of `G.edgeFinset`. -/
theorem numSpanningTrees_le_two_pow :
    numSpanningTrees G ≤ 2 ^ G.edgeFinset.card := by
  calc numSpanningTrees G
      = (spanningTreeEdgeSubsets G).card := rfl
    _ ≤ (G.edgeFinset.powerset).card :=
        Finset.card_le_card spanningTreeEdgeSubsets_subset_powerset
    _ = 2 ^ G.edgeFinset.card := Finset.card_powerset _

/-- **Monotonicity of the spanning-tree count in the graph**: a subgraph has no
more spanning-tree edge-subsets than the ambient graph, since every connected
spanning edge-subset of the subgraph is one of the ambient graph and the
cardinality filter `|V| - 1` is identical. -/
theorem numSpanningTrees_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : G ≤ H) :
    numSpanningTrees G ≤ numSpanningTrees H := by
  refine Finset.card_le_card (fun S hS => ?_)
  rw [mem_spanningTreeEdgeSubsets] at hS ⊢
  refine ⟨⟨hS.1.1.trans ?_, hS.1.2⟩, hS.2⟩
  exact (SimpleGraph.edgeFinset_subset_edgeFinset.mpr h)

end IsingModel.Penrose
