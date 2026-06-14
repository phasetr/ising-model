import IsingModel.ClusterExpansion.Penrose.KruskalConnected

/-!
# Kruskal forest is acyclic — `treeOf S` is a spanning tree (GJ §18.4-18.5, Issue #3954)

Acyclicity half of the Kruskal correctness of `treeOf` (PR 3b), completing the
headline `treeOf_mem_spanningTreeEdgeSubsets`: when `S` is a connected spanning
edge-subset of `G`, the Kruskal forest `treeOf S` is a spanning tree.

Acyclicity is the **cycle-max argument**: any cycle in `fromEdgeSet ↑(treeOf S)`
has a maximum edge `e` (in the edge order); the rest of the cycle joins `e`'s
endpoints using strictly-smaller edges of `treeOf S ⊆ S`, so `reachableLT S e`
holds — contradicting `e ∈ treeOf S` (a kept edge is one whose endpoints are *not*
joined by strictly-smaller edges).  The reachability via the other cycle edges is
extracted by localising the cycle to `fromEdgeSet ↑c.edges.toFinset` and applying
`adj_and_reachable_delete_edges_iff_exists_cycle`.

With connectivity (from `KruskalConnected`) and acyclicity, `treeOf S` is a tree,
so `|treeOf S| = |V| - 1` and it lands in `spanningTreeEdgeSubsets G`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
- Penrose tree-graph inequality (Brydges' lectures).
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} [LinearOrder V]

/-- **A cycle has at least one edge**: the edge finset of a cycle is nonempty. -/
theorem cycle_edgeFinset_nonempty {S : Finset (Sym2 V)} {u : V}
    {c : (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Walk u u} (hc : c.IsCycle) :
    c.edges.toFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne, List.toFinset_eq_empty_iff]
  intro hnil
  exact hc.not_nil (Walk.nil_iff_length_eq.mpr (by rw [← Walk.length_edges, hnil]; rfl))

/-- **Reachability via the other cycle edges**: for an edge `s(a, b)` of a cycle `c`,
the endpoints `a, b` are reachable using the remaining edges of `c` (i.e. within
`fromEdgeSet ↑(c.edges.toFinset.erase s(a, b))`).  Localise `c` to the graph of its
own edges, then use `adj_and_reachable_delete_edges_iff_exists_cycle`. -/
theorem reachable_from_cycle_edgeFinset_erase {S : Finset (Sym2 V)} {u a b : V}
    {c : (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Walk u u}
    (hc : c.IsCycle) (he : s(a, b) ∈ c.edges) :
    (fromEdgeSet (↑(c.edges.toFinset.erase s(a, b)) : Set (Sym2 V))).Reachable a b := by
  classical
  have htrans : ∀ e ∈ c.edges, e ∈ (fromEdgeSet (↑c.edges.toFinset : Set (Sym2 V))).edgeSet := by
    intro e hemem
    rw [edgeSet_fromEdgeSet, Set.mem_diff]
    refine ⟨Finset.mem_coe.mpr (List.mem_toFinset.mpr hemem), ?_⟩
    intro hdiag
    exact (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).not_isDiag_of_mem_edgeSet
      (c.edges_subset_edgeSet hemem) (Sym2.mem_diagSet.mp hdiag)
  have hc'cycle : (c.transfer _ htrans).IsCycle := hc.transfer htrans
  have he' : s(a, b) ∈ (c.transfer _ htrans).edges := by
    rw [Walk.edges_transfer]; exact he
  have hmain := (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle).mpr
    ⟨u, c.transfer _ htrans, hc'cycle, he'⟩
  have hgraph : (fromEdgeSet (↑c.edges.toFinset : Set (Sym2 V))) \ fromEdgeSet {s(a, b)}
      = fromEdgeSet (↑(c.edges.toFinset.erase s(a, b)) : Set (Sym2 V)) := by
    rw [← fromEdgeSet_sdiff, ← Finset.coe_erase]
  rw [hgraph] at hmain
  exact hmain.2

/-- **The non-maximal cycle edges are strictly-smaller edges of `S`**: every cycle edge
other than a maximum-key edge `M` lies in `edgesLT S M` (it is an edge of
`treeOf S ⊆ S` and has strictly smaller `edgeKey`). -/
theorem cycle_edge_erase_subset_edgesLT {S : Finset (Sym2 V)} {u : V}
    {c : (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).Walk u u} {M : Sym2 V}
    (hMmax : ∀ f ∈ c.edges.toFinset, edgeKey f ≤ edgeKey M) :
    c.edges.toFinset.erase M ⊆ edgesLT S M := by
  intro f hf
  rw [Finset.mem_erase] at hf
  obtain ⟨hne, hmem⟩ := hf
  have hfedge : f ∈ (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).edgeSet :=
    c.edges_subset_edgeSet (List.mem_toFinset.mp hmem)
  rw [edgeSet_fromEdgeSet, Set.mem_diff] at hfedge
  have hfS : f ∈ S := treeOf_subset S (Finset.mem_coe.mp hfedge.1)
  rw [mem_edgesLT]
  exact ⟨hfS, lt_of_le_of_ne (hMmax f hmem) (fun h => hne (edgeKey_injective h))⟩

/-- **The Kruskal forest is acyclic** (cycle-max argument): a cycle's maximum-key edge
`M` is kept (`M ∈ treeOf S`), yet the rest of the cycle joins its endpoints via
strictly-smaller edges of `S`, giving `reachableLT S M` — contradicting the keeping
criterion of `M`. -/
theorem isAcyclic_fromEdgeSet_treeOf (S : Finset (Sym2 V)) :
    (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).IsAcyclic := by
  intro u c hc
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image c.edges.toFinset edgeKey (cycle_edgeFinset_nonempty hc)
  have hMtree : M ∈ treeOf S := by
    have : M ∈ (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).edgeSet :=
      c.edges_subset_edgeSet (List.mem_toFinset.mp hMmem)
    rw [edgeSet_fromEdgeSet, Set.mem_diff] at this
    exact Finset.mem_coe.mp this.1
  obtain ⟨a, b, hMab⟩ : ∃ a b, M = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) M
  have hMedges : s(a, b) ∈ c.edges := by
    rw [← hMab]; exact List.mem_toFinset.mp hMmem
  -- reachability via the other cycle edges, transported into `edgesLT S M`
  have hreach : (fromEdgeSet (↑(edgesLT S M) : Set (Sym2 V))).Reachable a b := by
    have h1 := reachable_from_cycle_edgeFinset_erase hc hMedges
    rw [← hMab] at h1
    exact h1.mono (fromEdgeSet_mono (Finset.coe_subset.mpr
      (cycle_edge_erase_subset_edgesLT hMmax)))
  have hRLT : reachableLT S M := by
    rw [hMab, reachableLT_iff_edgesLT, ← hMab]; exact hreach
  exact (mem_treeOf.mp hMtree).2 hRLT

/-- **The Kruskal forest of a connected spanning edge-subset has `|V| - 1` edges**:
being connected and acyclic it is a tree, so `IsTree.card_edgeFinset` applies. -/
theorem treeOf_card_eq_card_vertices_sub_one [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Finset (Sym2 V)} (hSG : S ⊆ G.edgeFinset)
    (hConn : (fromEdgeSet (↑S : Set (Sym2 V))).Connected) :
    (treeOf S).card = Fintype.card V - 1 := by
  have hTree : (fromEdgeSet (↑(treeOf S) : Set (Sym2 V))).IsTree :=
    ⟨connected_treeOf_of_connected hConn, isAcyclic_fromEdgeSet_treeOf S⟩
  have hcard := hTree.card_edgeFinset
  rw [edgeFinset_fromEdgeSet_treeOf hSG] at hcard
  omega

/-- **Headline: the Kruskal forest of a connected spanning edge-subset is a spanning
tree** (`treeOf S ∈ spanningTreeEdgeSubsets G`).  Combines `treeOf S ⊆ G.edgeFinset`,
the connectivity of `treeOf S`, and the `|V| - 1` edge count. -/
theorem treeOf_mem_spanningTreeEdgeSubsets [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Finset (Sym2 V)}
    (hS : S ∈ connectedSpanningEdgeSubsets G) :
    treeOf S ∈ spanningTreeEdgeSubsets G := by
  rw [mem_connectedSpanningEdgeSubsets] at hS
  rw [mem_spanningTreeEdgeSubsets]
  exact ⟨⟨treeOf_subset_edgeFinset hS.1, connected_treeOf_of_connected hS.2⟩,
    treeOf_card_eq_card_vertices_sub_one hS.1 hS.2⟩

end IsingModel.Penrose
