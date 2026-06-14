import IsingModel.ClusterExpansion.Incompatibility
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Spanning-tree count of a finite graph (GJ §18.4, toward the Penrose bound)

Infrastructure for the tree-graph (Penrose) Ursell bound — the sole remaining
input of the general cluster-expansion convergence (Issue #3954).  A *spanning
tree* of a finite graph `G` is recorded here as an edge-subset `S ⊆ G.edgeFinset`
whose spanning subgraph `fromEdgeSet ↑S` is connected and has exactly
`|V| - 1` edges (equivalently, is a tree on `V`); `numSpanningTrees G` counts
them.

The Penrose tree-graph inequality
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`
(and Cayley's `numSpanningTrees K_n = n^{n-2}`) remain for a later PR of #3954;
together with `summable_mayerExpansionTerm_of_ursell_le` and the majorant
summability `summable_nat_pow_self_sub_two_mul_geometric_div_factorial` they
would close the full convergence.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
* O. Penrose (1967); A. Cayley (1889).
-/

namespace IsingModel

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

variable (G)

/-- **The spanning-tree count is at most the connected-spanning-subgraph count**. -/
theorem numSpanningTrees_le_connectedSpanningEdgeSubsets_card :
    numSpanningTrees G ≤ (connectedSpanningEdgeSubsets G).card :=
  Finset.card_le_card spanningTreeEdgeSubsets_subset_connectedSpanning

/-- **The spanning-tree count is at most `2^{|E|}`**: every spanning tree is an
edge-subset of `G.edgeFinset`. -/
theorem numSpanningTrees_le_two_pow :
    numSpanningTrees G ≤ 2 ^ G.edgeFinset.card := by
  have h1 : spanningTreeEdgeSubsets G ⊆ G.edgeFinset.powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr
      (mem_connectedSpanningEdgeSubsets.mp
        (spanningTreeEdgeSubsets_subset_connectedSpanning hS)).1
  calc numSpanningTrees G
      = (spanningTreeEdgeSubsets G).card := rfl
    _ ≤ (G.edgeFinset.powerset).card := Finset.card_le_card h1
    _ = 2 ^ G.edgeFinset.card := Finset.card_powerset _

/-- **Monotonicity of spanning-tree edge-subsets**: a spanning tree of `G` is a
spanning tree of any supergraph `H ≥ G` (its edges lie in `H.edgeFinset` and the
spanning subgraph is unchanged).  More edges, more spanning trees. -/
theorem spanningTreeEdgeSubsets_mono {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) :
    spanningTreeEdgeSubsets G ⊆ spanningTreeEdgeSubsets H := by
  intro S hS
  rw [mem_spanningTreeEdgeSubsets] at hS ⊢
  exact ⟨⟨hS.1.1.trans (SimpleGraph.edgeFinset_mono h), hS.1.2⟩, hS.2⟩

/-- **Monotonicity of the spanning-tree count**: `G ≤ H → numSpanningTrees G ≤
numSpanningTrees H`. -/
theorem numSpanningTrees_mono {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) :
    numSpanningTrees G ≤ numSpanningTrees H :=
  Finset.card_le_card (spanningTreeEdgeSubsets_mono h)

/-- **Spanning trees are bounded by the complete graph's** (GJ §18.4): every
finite graph has at most as many spanning trees as the complete graph on the same
vertex set.  Reduces the general Penrose/Cayley bound to the complete graph
(`numSpanningTrees (⊤) = |V|^{|V|-2}`, Cayley). -/
theorem numSpanningTrees_le_complete (G : SimpleGraph V) [DecidableRel G.Adj] :
    numSpanningTrees G ≤ numSpanningTrees (⊤ : SimpleGraph V) :=
  numSpanningTrees_mono le_top

end IsingModel
