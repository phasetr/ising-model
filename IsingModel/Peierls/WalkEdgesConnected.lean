import IsingModel.Conditioning.EdgeWalkExistence

/-!
# The edges of a walk are edge-connected (FV §3.7.2)

The edge set of a walk is edge-connected: each new edge shares the walk's current vertex with the
edges already laid down. For the Peierls contour this says the dual edges traversed by a dart
orbit (`d.tail → d.head → …`) form a single edge-connected contour, the input to the
volume-independent count via `card_connected_edge_sets_inducedLatticeGraph_le`.

* `start_mem_some_edge` — the start vertex of a nonempty walk lies in one of its edges.
* `walk_edges_isEdgeConnected` — the edge set of a walk is edge-connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The start vertex lies in a first edge**: a nonempty walk from `v` has an edge containing
`v`. -/
theorem start_mem_some_edge {G : SimpleGraph ι} {v t : ι} (w : G.Walk v t) (h : w.edges ≠ []) :
    ∃ f ∈ w.edges.toFinset, v ∈ f := by
  cases w with
  | nil => simp at h
  | @cons _ v₂ _ hadj w' =>
    refine ⟨s(v, v₂), ?_, ?_⟩
    · rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons]
      exact Finset.mem_insert_self _ _
    · exact Sym2.mem_mk_left v v₂

/-- **A walk's edges are edge-connected**: the finset of edges of any walk is edge-connected (the
empty case is vacuous; each `cons` edge touches the rest of the walk at the shared vertex). -/
theorem walk_edges_isEdgeConnected {G : SimpleGraph ι} {u t : ι} (w : G.Walk u t) :
    IsEdgeConnected w.edges.toFinset := by
  induction w with
  | nil =>
    intro e₁ he₁
    simp only [SimpleGraph.Walk.edges_nil, List.toFinset_nil, Finset.notMem_empty] at he₁
  | @cons u v t hadj w' ih =>
    rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons]
    by_cases hempty : w'.edges = []
    · -- `w'` has no edges: the cut is the singleton `{s(u,v)}`
      rw [hempty, List.toFinset_nil]
      intro e₁ he₁ e₂ he₂
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at he₁ he₂
      subst he₁; subst he₂; exact Relation.ReflTransGen.refl
    · -- `w'` has edges: `s(u,v)` touches `w'` at `v`
      apply isEdgeConnected_insert ih
      obtain ⟨f, hf, hvf⟩ := start_mem_some_edge w' hempty
      exact ⟨f, hf, v, Sym2.mem_mk_right u v, hvf⟩

end IsingModel
