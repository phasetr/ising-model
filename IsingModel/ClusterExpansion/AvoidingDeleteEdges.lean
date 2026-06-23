import IsingModel.ClusterExpansion.AvoidingPolymerGas
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Avoiding even subgraphs as even subgraphs of a delete-edges graph

This file identifies the high-temperature even-subgraph sum avoiding a fixed edge set `C` with the
ordinary even-subgraph sum of the graph obtained by deleting every edge that touches
`polymerSupport C`.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Edges of `G` that touch the vertex support of `C`. -/
noncomputable def touchEdges (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) : Finset (Sym2 ι) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ v : ι, v ∈ e ∧ v ∈ polymerSupport C)

/-- The graph obtained from `G` by deleting every edge that touches `polymerSupport C`. -/
noncomputable def Gavoid (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) : SimpleGraph ι :=
  G.deleteEdges (touchEdges G C : Set (Sym2 ι))

/-- The deleted graph has decidable adjacency (classically; only used for `degree`/`maxDegree`). -/
noncomputable instance instDecidableRelGavoidAdj (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (C : Finset (Sym2 ι)) :
    DecidableRel (Gavoid G C).Adj := by
  classical
  dsimp [Gavoid]
  infer_instance

/-- The deleted graph has a finite edge set, inherited (by subset) from the finite edge set of
`G` — independent of any `DecidableRel` instance. -/
noncomputable instance instFintypeGavoidEdgeSet (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) : Fintype (Gavoid G C).edgeSet := by
  classical
  dsimp [Gavoid]
  exact ((Set.toFinite G.edgeSet).subset
    (SimpleGraph.edgeSet_subset_edgeSet.mpr
      (G.deleteEdges_le (touchEdges G C : Set (Sym2 ι))))).fintype

/-- Membership in `touchEdges`: an edge is selected exactly when it is an edge of `G` and touches
`polymerSupport C`. -/
theorem mem_touchEdges (G : SimpleGraph ι) [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {e : Sym2 ι} :
    e ∈ touchEdges G C ↔
      e ∈ G.edgeFinset ∧ ∃ v : ι, v ∈ e ∧ v ∈ polymerSupport C := by
  classical
  unfold touchEdges
  rw [Finset.mem_filter]

/-- `touchEdges G C` is a sub-finset of `G.edgeFinset`. -/
theorem touchEdges_subset_edgeFinset (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) :
    touchEdges G C ⊆ G.edgeFinset := by
  intro e he
  exact ((mem_touchEdges G).mp he).1

/-- The edge finset of `Gavoid G C` is the edge finset of `G` with `touchEdges G C` removed.
Proved instance-independently via `mem_edgeFinset` to avoid the `Fintype.edgeSet` diamond. -/
theorem edgeFinset_Gavoid (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) :
    (Gavoid G C).edgeFinset = G.edgeFinset \ touchEdges G C := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  change e ∈ (G.deleteEdges (touchEdges G C : Set (Sym2 ι))).edgeSet ↔ _
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Finset.mem_coe]

/-- Membership in the edge finset of `Gavoid G C`: an edge survives exactly when it is an edge of
`G` and none of its vertices lies in `polymerSupport C`. -/
theorem mem_edgeFinset_Gavoid_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {e : Sym2 ι} :
    e ∈ (Gavoid G C).edgeFinset ↔
      e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∉ polymerSupport C := by
  classical
  rw [edgeFinset_Gavoid, Finset.mem_sdiff, mem_touchEdges]
  constructor
  · rintro ⟨heG, hnot⟩
    refine ⟨heG, ?_⟩
    intro v hve hvC
    exact hnot ⟨heG, v, hve, hvC⟩
  · rintro ⟨heG, havoid⟩
    refine ⟨heG, ?_⟩
    rintro ⟨_, v, hve, hvC⟩
    exact havoid v hve hvC

/-- Vertex-disjointness from `C` is equivalent to every edge avoiding `polymerSupport C`. -/
theorem isPolymerVertexDisjoint_iff_forall_edge_avoids_support
    {C Y : Finset (Sym2 ι)} :
    IsPolymerVertexDisjoint C Y ↔
      ∀ e ∈ Y, ∀ v ∈ e, v ∉ polymerSupport C := by
  classical
  unfold IsPolymerVertexDisjoint
  constructor
  · intro h e heY v hve hvC
    have hvY : v ∈ polymerSupport Y :=
      mem_polymerSupport.mpr ⟨e, heY, hve⟩
    exact (Finset.disjoint_left.mp h) hvC hvY
  · intro h
    rw [Finset.disjoint_left]
    intro v hvC hvY
    obtain ⟨e, heY, hve⟩ := mem_polymerSupport.mp hvY
    exact h e heY v hve hvC

/-- A set of edges is contained in `Gavoid G C` exactly when it is contained in `G` and is
vertex-disjoint from `C`. -/
theorem subset_edgeFinset_Gavoid_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C Y : Finset (Sym2 ι)) :
    Y ⊆ (Gavoid G C).edgeFinset ↔
      Y ⊆ G.edgeFinset ∧ IsPolymerVertexDisjoint C Y := by
  classical
  constructor
  · intro hY
    refine ⟨?_, ?_⟩
    · intro e heY
      exact ((mem_edgeFinset_Gavoid_iff G).mp (hY heY)).1
    · rw [isPolymerVertexDisjoint_iff_forall_edge_avoids_support]
      intro e heY
      exact ((mem_edgeFinset_Gavoid_iff G).mp (hY heY)).2
  · rintro ⟨hYG, hdisj⟩ e heY
    rw [mem_edgeFinset_Gavoid_iff]
    exact ⟨hYG heY,
      (isPolymerVertexDisjoint_iff_forall_edge_avoids_support.mp hdisj) e heY⟩

/-- Avoiding even subgraphs of `G` are exactly even subgraphs of `Gavoid G C`. -/
theorem evenSubgraphsAvoiding_eq_evenSubgraphs_Gavoid
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) :
    evenSubgraphsAvoiding G C = evenSubgraphs (Gavoid G C) := by
  classical
  ext Y
  unfold evenSubgraphsAvoiding
  rw [Finset.mem_filter, mem_evenSubgraphs, mem_evenSubgraphs]
  constructor
  · rintro ⟨hY, hdisj⟩
    exact
      { subset := (subset_edgeFinset_Gavoid_iff G C Y).mpr ⟨hY.subset, hdisj⟩
        even_degree := hY.even_degree }
  · intro hY
    have hsub := (subset_edgeFinset_Gavoid_iff G C Y).mp hY.subset
    exact
      ⟨{ subset := hsub.1
         even_degree := hY.even_degree }, hsub.2⟩

/-- The `A = ∅` high-temperature subgraph sum is the sum over even subgraphs. -/
theorem htSubgraphSum_empty_eq_evenSubgraphs
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℂ) :
    htSubgraphSum G (∅ : Finset ι) t =
      ∑ X ∈ evenSubgraphs G, t ^ X.card := by
  classical
  unfold htSubgraphSum
  congr 1
  ext X
  rw [Finset.mem_filter, Finset.mem_powerset, mem_evenSubgraphs]
  constructor
  · rintro ⟨hsub, hbd⟩
    refine ⟨hsub, ?_⟩
    intro v
    apply Nat.not_odd_iff_even.mp
    intro hodd
    have hv : v ∈ oddBoundary X := by
      rw [oddBoundary, Finset.mem_filter]
      exact ⟨Finset.mem_univ v, hodd⟩
    rw [hbd] at hv
    exact Finset.notMem_empty v hv
  · intro hX
    exact ⟨hX.subset, oddBoundary_eq_empty_of_isEvenSubgraph G hX⟩

/-- The avoiding high-temperature sum is the ordinary empty-boundary high-temperature sum of the
delete-edges graph `Gavoid G C`. -/
theorem htSubgraphSumAvoiding_eq_htSubgraphSum_empty_Gavoid
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (t : ℂ) :
    htSubgraphSumAvoiding G C t =
      htSubgraphSum (Gavoid G C) (∅ : Finset ι) t := by
  classical
  unfold htSubgraphSumAvoiding
  rw [evenSubgraphsAvoiding_eq_evenSubgraphs_Gavoid,
    htSubgraphSum_empty_eq_evenSubgraphs]

/-- A polymer of `Gavoid G C` is exactly a polymer of `G` whose edge set is contained in
`Gavoid G C`. -/
theorem IsPolymer_Gavoid_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C P : Finset (Sym2 ι)) :
    IsPolymer (Gavoid G C) P ↔
      IsPolymer G P ∧ P ⊆ (Gavoid G C).edgeFinset := by
  classical
  constructor
  · intro hP
    have hsub := (subset_edgeFinset_Gavoid_iff G C P).mp hP.isEven.subset
    exact
      ⟨{ isEven :=
          { subset := hsub.1
            even_degree := hP.isEven.even_degree }
         nonempty := hP.nonempty
         connected := hP.connected },
       hP.isEven.subset⟩
  · rintro ⟨hP, hsub⟩
    exact
      { isEven :=
          { subset := hsub
            even_degree := hP.isEven.even_degree }
        nonempty := hP.nonempty
        connected := hP.connected }

/-- The polymers of `Gavoid G C` are the polymers of `G` that are contained in the surviving edge
finset. -/
theorem allPolymers_Gavoid (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) :
    allPolymers (Gavoid G C) =
      (allPolymers G).filter (fun P => P ⊆ (Gavoid G C).edgeFinset) := by
  classical
  ext P
  rw [mem_allPolymers, Finset.mem_filter, mem_allPolymers, IsPolymer_Gavoid_iff]

/-- Deleting the edges that touch `polymerSupport C` cannot increase maximum degree. -/
theorem maxDegree_Gavoid_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (C : Finset (Sym2 ι)) :
    (Gavoid G C).maxDegree ≤ G.maxDegree := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le (G := Gavoid G C) G.maxDegree
  intro v
  have hle : Gavoid G C ≤ G := by
    unfold Gavoid
    exact G.deleteEdges_le (touchEdges G C : Set (Sym2 ι))
  exact ((Gavoid G C).degree_le_of_le hle).trans (G.degree_le_maxDegree v)

end IsingModel
