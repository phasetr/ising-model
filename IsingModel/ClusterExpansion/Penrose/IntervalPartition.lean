import IsingModel.ClusterExpansion.Penrose.KruskalAcyclic
import IsingModel.ClusterExpansion.Penrose.BooleanInterval

/-!
# Penrose interval-partition property (GJ §18.4-18.5, Issue #3954)

The Kruskal retraction `treeOf` partitions the connected spanning edge-subsets of `G`
into Boolean intervals indexed by spanning trees: for a spanning tree `T`, the fiber
`{S | treeOf S = T}` is exactly `[T, T ∪ addable G T]`.  Established here
**unconditionally** (no hypothesis structures).

The new ingredient is a **prefix-level reachability equivalence**
`reachableLT (treeOf S) e ↔ reachableLT S e` (the `< e` edges of `S` and of `treeOf S`
span the same components), proved by strong induction over the `edgeKey` order — a
refinement of the global `reachable_treeOf_iff_reachable`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Penrose tree-graph inequality (Brydges' lectures).
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} [LinearOrder V]

/-- **`edgesLT` is monotone in the edge-set**. -/
theorem edgesLT_mono {X Y : Finset (Sym2 V)} {e : Sym2 V} (hXY : X ⊆ Y) :
    edgesLT X e ⊆ edgesLT Y e := by
  intro f hf
  rw [mem_edgesLT] at hf ⊢
  exact ⟨hXY hf.1, hf.2⟩

/-- **`edgesLT` is monotone in the threshold**: a lower threshold gives a sub-prefix. -/
theorem edgesLT_of_lt_subset {X : Finset (Sym2 V)} {f e : Sym2 V}
    (hfe : edgeKey f < edgeKey e) : edgesLT X f ⊆ edgesLT X e := by
  intro g hg
  rw [mem_edgesLT] at hg ⊢
  exact ⟨hg.1, hg.2.trans hfe⟩

/-- **`reachableLT` is monotone in the edge-set**. -/
theorem reachableLT_mono {X Y : Finset (Sym2 V)} {e : Sym2 V} (hXY : X ⊆ Y)
    (h : reachableLT X e) : reachableLT Y e := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
  rw [reachableLT_iff_edgesLT] at h ⊢
  exact h.mono (fromEdgeSet_mono (Finset.coe_subset.mpr (edgesLT_mono hXY)))

section Prefix
variable [Finite V]

/-- **Prefix reachability into `treeOf`**: if `s(a, b)` is a `< e` edge of `S`, then
`a, b` are reachable within the `< e` edges of `treeOf S`.  Strong induction over the
edge order: a kept `< e` edge gives a direct adjacency; a dropped `< e` edge `f` has
its endpoints joined by `< f`-edges of `S`, each handled by the induction hypothesis
and transported. -/
theorem reachable_edgesLT_treeOf_of_mem_edgesLT {S : Finset (Sym2 V)} :
    ∀ e a b, s(a, b) ∈ edgesLT S e →
      (fromEdgeSet (↑(edgesLT (treeOf S) e) : Set (Sym2 V))).Reachable a b := by
  have key : ∀ d : Sym2 V, ∀ e a b, d = s(a, b) → s(a, b) ∈ edgesLT S e →
      (fromEdgeSet (↑(edgesLT (treeOf S) e) : Set (Sym2 V))).Reachable a b := by
    intro d
    refine WellFounded.induction
      (C := fun d => ∀ e a b, d = s(a, b) → s(a, b) ∈ edgesLT S e →
        (fromEdgeSet (↑(edgesLT (treeOf S) e) : Set (Sym2 V))).Reachable a b)
      wellFounded_edgeKey_lt d ?_
    intro d IH e a b hd hmem
    subst hd
    rw [mem_edgesLT] at hmem
    by_cases hab : a = b
    · subst hab; exact Reachable.refl _
    by_cases hlt : reachableLT S s(a, b)
    · rw [reachableLT_iff_edgesLT] at hlt
      refine reachable_mono_of_edges_reachable (T := edgesLT (treeOf S) e) ?_ hlt
      intro x y hxy
      rw [mem_edgesLT] at hxy
      have hmemE : s(x, y) ∈ edgesLT S e := by
        rw [mem_edgesLT]; exact ⟨hxy.1, hxy.2.trans hmem.2⟩
      exact IH s(x, y) hxy.2 e x y rfl hmemE
    · have hkeep : s(a, b) ∈ treeOf S := mem_treeOf.mpr ⟨hmem.1, hlt⟩
      refine Adj.reachable ?_
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (mem_edgesLT.mpr ⟨hkeep, hmem.2⟩), hab⟩
  intro e a b hmem
  exact key s(a, b) e a b rfl hmem

/-- **Prefix reachability equivalence**: the `< e` edges of `treeOf S` and of `S` have
the same reachability relation. -/
theorem reachable_edgesLT_treeOf_iff {S : Finset (Sym2 V)} {e : Sym2 V} {a b : V} :
    (fromEdgeSet (↑(edgesLT (treeOf S) e) : Set (Sym2 V))).Reachable a b ↔
      (fromEdgeSet (↑(edgesLT S e) : Set (Sym2 V))).Reachable a b := by
  constructor
  · intro h
    exact h.mono (fromEdgeSet_mono (Finset.coe_subset.mpr (edgesLT_mono (treeOf_subset S))))
  · intro h
    exact reachable_mono_of_edges_reachable
      (fun a b hab => reachable_edgesLT_treeOf_of_mem_edgesLT e a b hab) h

/-- **Prefix `reachableLT` equivalence**: `reachableLT (treeOf S) e ↔ reachableLT S e`. -/
theorem reachableLT_treeOf_iff {S : Finset (Sym2 V)} {e : Sym2 V} :
    reachableLT (treeOf S) e ↔ reachableLT S e := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
  rw [reachableLT_iff_edgesLT, reachableLT_iff_edgesLT, reachable_edgesLT_treeOf_iff]

end Prefix

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Edge finset of a diagonal-free edge-subset**: when `S ⊆ G.edgeFinset`,
`(fromEdgeSet ↑S).edgeFinset = S`. -/
theorem edgeFinset_fromEdgeSet_of_subset_edgeFinset {S : Finset (Sym2 V)}
    (hS : S ⊆ G.edgeFinset) :
    (fromEdgeSet (↑S : Set (Sym2 V))).edgeFinset = S := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_diff, Finset.mem_coe]
  refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
  have hmem : e ∈ G.edgeFinset := hS he
  rw [SimpleGraph.mem_edgeFinset] at hmem
  exact fun hdiag => G.not_isDiag_of_mem_edgeSet hmem (Sym2.mem_diagSet.mp hdiag)

/-- **A spanning-tree edge-subset spans a tree**: `fromEdgeSet ↑T` is a tree. -/
theorem isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeEdgeSubsets G) :
    (fromEdgeSet (↑T : Set (Sym2 V))).IsTree := by
  rw [mem_spanningTreeEdgeSubsets] at hT
  rw [isTree_iff_connected_and_card]
  refine ⟨hT.1.2, ?_⟩
  have hef : (fromEdgeSet (↑T : Set (Sym2 V))).edgeFinset = T :=
    edgeFinset_fromEdgeSet_of_subset_edgeFinset hT.1.1
  have hcardV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hT.1.2.nonempty
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, hef, hT.2]
  omega

/-- **A tree edge is not `reachableLT`**: for a spanning tree `T` and `e ∈ T`, the
endpoints of `e` are not joined by the strictly-smaller edges of `T` (else `e` would
close a cycle, contradicting acyclicity). -/
theorem not_reachableLT_of_mem_spanningTreeEdgeSubsets {T : Finset (Sym2 V)} {e : Sym2 V}
    (hT : T ∈ spanningTreeEdgeSubsets G) (heT : e ∈ T) : ¬ reachableLT T e := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
  have htree := isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets hT
  have hsub : T ⊆ G.edgeFinset := (mem_spanningTreeEdgeSubsets.mp hT).1.1
  have heES : s(a, b) ∈ (fromEdgeSet (↑T : Set (Sym2 V))).edgeSet := by
    rw [edgeSet_fromEdgeSet, Set.mem_diff]
    refine ⟨Finset.mem_coe.mpr heT, ?_⟩
    have hmem : s(a, b) ∈ G.edgeFinset := hsub heT
    rw [SimpleGraph.mem_edgeFinset] at hmem
    exact fun hdiag => G.not_isDiag_of_mem_edgeSet hmem (Sym2.mem_diagSet.mp hdiag)
  have hbridge : (fromEdgeSet (↑T : Set (Sym2 V))).IsBridge s(a, b) :=
    (isAcyclic_iff_forall_edge_isBridge.mp htree.isAcyclic) heES
  intro hRLT
  rw [reachableLT_iff_edgesLT] at hRLT
  rw [SimpleGraph.isBridge_iff, ← fromEdgeSet_sdiff] at hbridge
  refine hbridge.2 (hRLT.mono (fromEdgeSet_mono ?_))
  intro f hf
  rw [Finset.mem_coe, mem_edgesLT] at hf
  rw [Set.mem_diff, Set.mem_singleton_iff]
  refine ⟨Finset.mem_coe.mpr hf.1, ?_⟩
  intro hfe
  exact absurd (hfe ▸ hf.2) (lt_irrefl _)

/-- **Addable edges are `reachableLT` for any extension**: if `T ⊆ S` and
`e ∈ addable G T`, then `reachableLT S e`. -/
theorem reachableLT_of_mem_addable_of_subset {T S : Finset (Sym2 V)} {e : Sym2 V}
    (hTS : T ⊆ S) (he : e ∈ addable G T) : reachableLT S e :=
  reachableLT_mono hTS (mem_addable.mp he).2.2

/-- **An interval tree edge stays kept**: for a spanning tree `T` and `S` in its Boolean
interval, a tree edge `e ∈ T` is not `reachableLT S e`.  The `< e` edges of `S` route
through `T` (tree edges directly, addable edges via their own `< e` `T`-reachability),
so `reachableLT S e` would give `reachableLT T e`, contradicting acyclicity of `T`. -/
theorem not_reachableLT_of_interval_tree_edge {T S : Finset (Sym2 V)} {e : Sym2 V}
    (hT : T ∈ spanningTreeEdgeSubsets G) (hSU : S ⊆ T ∪ addable G T) (heT : e ∈ T) :
    ¬ reachableLT S e := by
  intro hRLT
  refine not_reachableLT_of_mem_spanningTreeEdgeSubsets hT heT ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
  rw [reachableLT_iff_edgesLT] at hRLT ⊢
  refine reachable_mono_of_edges_reachable (T := edgesLT T s(a, b)) ?_ hRLT
  intro x y hxy
  rw [mem_edgesLT] at hxy
  rcases Finset.mem_union.mp (hSU hxy.1) with hT' | hadd
  · by_cases hxyeq : x = y
    · subst hxyeq; exact Reachable.refl _
    · refine Adj.reachable ?_
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (mem_edgesLT.mpr ⟨hT', hxy.2⟩), hxyeq⟩
  · have hRLTf : reachableLT T s(x, y) := (mem_addable.mp hadd).2.2
    rw [reachableLT_iff_edgesLT] at hRLTf
    exact hRLTf.mono (fromEdgeSet_mono (Finset.coe_subset.mpr (edgesLT_of_lt_subset hxy.2)))

/-- **Forward interval inclusion**: if `treeOf S = T` then `S ⊆ T ∪ addable G T`. -/
theorem subset_union_addable_of_treeOf_eq {S T : Finset (Sym2 V)}
    (hS : S ∈ connectedSpanningEdgeSubsets G) (h : treeOf S = T) :
    S ⊆ T ∪ addable G T := by
  intro e he
  rw [Finset.mem_union]
  by_cases hmemT : e ∈ T
  · exact Or.inl hmemT
  · refine Or.inr ?_
    have hRLT : reachableLT S e := by
      by_contra hkeep
      exact hmemT (h ▸ mem_treeOf.mpr ⟨he, hkeep⟩)
    have heG : e ∈ G.edgeFinset := (mem_connectedSpanningEdgeSubsets.mp hS).1 he
    rw [mem_addable]
    refine ⟨heG, hmemT, ?_⟩
    rw [← h]
    exact (reachableLT_treeOf_iff (S := S)).mpr hRLT

/-- **Converse interval inclusion**: if `T ⊆ S ⊆ T ∪ addable G T` for a spanning tree
`T`, then `treeOf S = T`.  Addable edges are dropped (`reachableLT S`), tree edges are
kept (interval-tree-edge lemma). -/
theorem treeOf_eq_of_subset_union_addable {S T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeEdgeSubsets G) (hTS : T ⊆ S) (hSU : S ⊆ T ∪ addable G T) :
    treeOf S = T := by
  ext e
  rw [mem_treeOf]
  constructor
  · rintro ⟨heS, hkeep⟩
    rcases Finset.mem_union.mp (hSU heS) with hT' | hadd
    · exact hT'
    · exact absurd (reachableLT_of_mem_addable_of_subset hTS hadd) hkeep
  · intro heT
    exact ⟨hTS heT, not_reachableLT_of_interval_tree_edge hT hSU heT⟩

/-- **Interval-partition property**: `treeOf S = T ↔ T ⊆ S ∧ S ⊆ T ∪ addable G T`. -/
theorem treeOf_eq_iff_subset_union_addable {S T : Finset (Sym2 V)}
    (hS : S ∈ connectedSpanningEdgeSubsets G) (hT : T ∈ spanningTreeEdgeSubsets G) :
    treeOf S = T ↔ T ⊆ S ∧ S ⊆ T ∪ addable G T := by
  constructor
  · intro h
    exact ⟨h ▸ treeOf_subset S, subset_union_addable_of_treeOf_eq hS h⟩
  · rintro ⟨hTS, hSU⟩
    exact treeOf_eq_of_subset_union_addable hT hTS hSU

/-- **An edge-set containing a spanning tree is connected spanning**. -/
theorem connectedSpanning_of_spanningTree_subset {T S : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeEdgeSubsets G) (hTS : T ⊆ S) (hSG : S ⊆ G.edgeFinset) :
    S ∈ connectedSpanningEdgeSubsets G := by
  rw [mem_connectedSpanningEdgeSubsets]
  refine ⟨hSG, ?_⟩
  exact (mem_spanningTreeEdgeSubsets.mp hT).1.2.mono
    (fromEdgeSet_mono (Finset.coe_subset.mpr hTS))

/-- **The `treeOf` fiber over a spanning tree is its Boolean interval**:
`{S ∈ connectedSpanningEdgeSubsets G | treeOf S = T} = [T, T ∪ addable G T]`.  This is
the partition of the connected spanning edge-subsets driving the Penrose collapse. -/
theorem treeOf_fiber_eq_booleanInterval {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeEdgeSubsets G) :
    (connectedSpanningEdgeSubsets G).filter (fun S => treeOf S = T)
      = booleanInterval T (T ∪ addable G T) := by
  ext S
  rw [Finset.mem_filter, mem_booleanInterval]
  constructor
  · rintro ⟨hS, h⟩
    exact (treeOf_eq_iff_subset_union_addable hS hT).mp h
  · rintro ⟨hTS, hSU⟩
    have hSG : S ⊆ G.edgeFinset :=
      hSU.trans (Finset.union_subset (mem_spanningTreeEdgeSubsets.mp hT).1.1
        (addable_subset_edges G T))
    have hS : S ∈ connectedSpanningEdgeSubsets G :=
      connectedSpanning_of_spanningTree_subset hT hTS hSG
    exact ⟨hS, (treeOf_eq_iff_subset_union_addable hS hT).mpr ⟨hTS, hSU⟩⟩

end IsingModel.Penrose
