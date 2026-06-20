import IsingModel.ClusterExpansion.Penrose.SpanningTree

/-!
# Monotonicity of spanning-tree edge subsets (GJ §18.5)

A spanning tree of a subgraph `G ≤ H` is also a spanning tree of `H`: it has the
same vertex set, its edges lie in `G.edgeFinset ⊆ H.edgeFinset`, it spans a
connected tree, and it has `|V| - 1` edges.  Hence
`spanningTreeEdgeSubsets G ⊆ spanningTreeEdgeSubsets H`.

For the Kotecky--Preiss / tree-graph bound this lets a weighted sum over the
spanning trees of *any* graph (e.g. a polymer incompatibility graph) be dominated
by the same weighted sum over the spanning trees of the complete graph `⊤`, where
the parent-code factorisation of `WeightedTreeSum` applies.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Monotonicity of spanning-tree edge subsets.**  Every spanning tree of a
subgraph `G ≤ H` is a spanning tree of `H`: the tree edges lie in
`G.edgeFinset ⊆ H.edgeFinset`, while the connectivity and edge-count conditions are
unchanged.  Hence `spanningTreeEdgeSubsets G ⊆ spanningTreeEdgeSubsets H`. -/
theorem spanningTreeEdgeSubsets_mono {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G ≤ H) :
    spanningTreeEdgeSubsets G ⊆ spanningTreeEdgeSubsets H := by
  intro S hS
  rw [mem_spanningTreeEdgeSubsets] at hS ⊢
  obtain ⟨⟨hsub, hconn⟩, hcard⟩ := hS
  exact ⟨⟨hsub.trans (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hGH), hconn⟩, hcard⟩

/-- **A weighted spanning-tree sum is monotone in the graph.**  For a non-negative
weight `F` and a subgraph `G ≤ H`, the sum of `F` over the spanning trees of `G` is
at most the sum over the spanning trees of `H` (the former range is a subset of the
latter). -/
theorem sum_spanningTree_le_of_le {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G ≤ H)
    (F : Finset (Sym2 V) → ℝ) (hF : ∀ S, 0 ≤ F S) :
    (∑ S ∈ spanningTreeEdgeSubsets G, F S)
      ≤ ∑ S ∈ spanningTreeEdgeSubsets H, F S :=
  Finset.sum_le_sum_of_subset_of_nonneg (spanningTreeEdgeSubsets_mono hGH)
    fun S _ _ => hF S

/-- **Every spanning tree is a spanning tree of the complete graph.**  Specialising
monotonicity to `H = ⊤`: a weighted spanning-tree sum over any graph is dominated by
the same sum over the spanning trees of `⊤`, where the parent-code factorisation of
`WeightedTreeSum` applies. -/
theorem sum_spanningTree_le_top {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset (Sym2 V) → ℝ) (hF : ∀ S, 0 ≤ F S) :
    (∑ S ∈ spanningTreeEdgeSubsets G, F S)
      ≤ ∑ S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph V), F S :=
  sum_spanningTree_le_of_le le_top F hF

end IsingModel.Penrose
