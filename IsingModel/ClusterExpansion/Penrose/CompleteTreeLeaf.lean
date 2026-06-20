import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound

/-!
# A complete-graph spanning tree has a non-root leaf (GJ §18.5)

The rooted-tree Kotecky--Preiss induction peels the tree from its leaves: a vertex
that is nobody's parent (a leaf in the rooted parent code) can be summed out first.
This file provides the existence of such a leaf for the rooted parent code of a
spanning tree of the complete graph `K_{n+1}` (`n > 0`): the vertex farthest from the
root `0` is a non-root vertex that is not the parent of any vertex.

`completeGraphTreeParentCode_exists_nonroot_leaf`: for `n > 0`, there is a non-root
vertex `Fin.succ j` with `completeGraphTreeParentCode n T i ≠ Fin.succ j` for every
`i` — i.e. a leaf of the rooted tree.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel.Penrose

open SimpleGraph

/-- **A complete-graph spanning tree has a non-root leaf.**  For `n > 0`, the vertex
`v` of a spanning tree of `K_{n+1}` farthest from the root `0` is a non-root vertex
that is not the parent of any vertex in the rooted parent code: every `i` satisfies
`completeGraphTreeParentCode n T i ≠ v`.  Indeed if `v` were the parent of some
`Fin.succ i`, then `Fin.succ i` would be one step farther from the root than `v`,
contradicting the maximality of `v`'s distance. -/
theorem completeGraphTreeParentCode_exists_nonroot_leaf {n : ℕ} (hn : 0 < n)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) :
    ∃ j : Fin n, ∀ i : Fin n, completeGraphTreeParentCode n T i ≠ Fin.succ j := by
  obtain ⟨v, -, hvmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
      (fun w => (fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).dist 0 w)
      ⟨0, Finset.mem_univ 0⟩
  have hconn : (fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).Connected :=
    (isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2).connected
  have hv0 : v ≠ 0 := by
    rintro rfl
    have hle := hvmax (Fin.succ ⟨0, hn⟩) (Finset.mem_univ _)
    rw [dist_self] at hle
    exact Fin.succ_ne_zero _ (hconn.dist_eq_zero_iff.mp (Nat.le_zero.mp hle)).symm
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hv0
  refine ⟨j, fun i hcontra => ?_⟩
  have h2 := (treeParent_spec (isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2)
    0 (Fin.succ i) (Fin.succ_ne_zero i)).2
  rw [show treeParent (isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2)
    0 (Fin.succ i) (Fin.succ_ne_zero i) = Fin.succ j from hcontra] at h2
  have hle := hvmax (Fin.succ i) (Finset.mem_univ _)
  omega

end IsingModel.Penrose
