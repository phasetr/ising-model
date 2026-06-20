import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound
import IsingModel.ClusterExpansion.Incompatibility

/-!
# Rooted-tree orientation for the polymer-sequence incompatibility graph (GJ §18.5)

The Kotecky--Preiss / tree-graph proof of cluster-expansion convergence (FV
Theorem 5.4) sums over spanning trees of the incompatibility graph of a polymer
sequence `ω : α → Finset (Sym2 ι)` and induces along the rooted-tree parent edges.
For that induction the per-polymer Kotecky--Preiss hypothesis
`∑_{Q ∼ P} |w(Q)| e^{a(Q)} ≤ a(P)`
(`incompatibilityActivity_expWeighted_le_card_of_half`) must be applied to each
parent edge, which requires the parent polymer to be genuinely *incompatible* with
its child.

This file provides exactly that orientation fact, stated for any tree subgraph `G`
of the incompatibility graph (a concrete spanning tree `fromEdgeSet ↑T` is such a
subgraph): rooted at `r`, every non-root vertex `v` is incompatible with its parent.
Since `G ≤ polymerSeqIncompatibilityGraph ω`, the rooted-tree parent adjacency in
`G` lifts to an incompatibility-graph adjacency, hence to `PolymersIncompatible`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- **The rooted-tree parent is incompatibility-graph adjacent.**  If `G` is a tree
subgraph of `polymerSeqIncompatibilityGraph ω`, then in the tree rooted at `r` every
non-root vertex `v` is adjacent *in the incompatibility graph* to its parent: the
parent adjacency in `G` is transported along `G ≤ polymerSeqIncompatibilityGraph ω`. -/
theorem polymerSeqTree_parent_adj (ω : α → Finset (Sym2 ι))
    {G : SimpleGraph α} (hsub : G ≤ polymerSeqIncompatibilityGraph ω)
    (hG : G.IsTree) (r v : α) (hv : v ≠ r) :
    (polymerSeqIncompatibilityGraph ω).Adj v (Penrose.treeParent hG r v hv) :=
  hsub (Penrose.treeParent_spec hG r v hv).1

/-- **The rooted-tree parent is distinct from its child.** -/
theorem polymerSeqTree_parent_ne (ω : α → Finset (Sym2 ι))
    {G : SimpleGraph α} (hsub : G ≤ polymerSeqIncompatibilityGraph ω)
    (hG : G.IsTree) (r v : α) (hv : v ≠ r) :
    Penrose.treeParent hG r v hv ≠ v :=
  (polymerSeqTree_parent_adj ω hsub hG r v hv).ne'

/-- **Rooted-tree orientation: a non-root vertex is incompatible with its parent.**
If `G` is a tree subgraph of `polymerSeqIncompatibilityGraph ω` rooted at `r`, then
every non-root vertex `v` satisfies `PolymersIncompatible (ω v) (ω (parent v))`.
This is the structural fact that lets the Kotecky--Preiss per-polymer activity
hypothesis be applied along the parent edges of the rooted-tree induction. -/
theorem polymerSeqTree_parent_incompatible (ω : α → Finset (Sym2 ι))
    {G : SimpleGraph α} (hsub : G ≤ polymerSeqIncompatibilityGraph ω)
    (hG : G.IsTree) (r v : α) (hv : v ≠ r) :
    PolymersIncompatible (ω v) (ω (Penrose.treeParent hG r v hv)) :=
  (polymerSeqIncompatibilityGraph_adj.mp
    (polymerSeqTree_parent_adj ω hsub hG r v hv)).2

/-- **A spanning-tree edge-subset of the incompatibility graph spans a tree
subgraph.**  For `T ∈ spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)`,
`fromEdgeSet ↑T` is a tree contained in the incompatibility graph — the concrete
instance of the abstract tree-subgraph hypothesis above. -/
theorem fromEdgeSet_le_polymerSeqIncompatibilityGraph [Fintype α] [DecidableEq α]
    (ω : α → Finset (Sym2 ι)) {T : Finset (Sym2 α)}
    (hT : T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)) :
    SimpleGraph.fromEdgeSet (↑T : Set (Sym2 α)) ≤ polymerSeqIncompatibilityGraph ω := by
  have hsub : T ⊆ (polymerSeqIncompatibilityGraph ω).edgeFinset :=
    (Penrose.mem_spanningTreeEdgeSubsets.mp hT).1.1
  intro a b hab
  rw [SimpleGraph.fromEdgeSet_adj] at hab
  have hmem := hsub (Finset.mem_coe.mp hab.1)
  rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem

end IsingModel
