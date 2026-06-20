import IsingModel.ClusterExpansion.RootedParentActive
import IsingModel.ClusterExpansion.Penrose.CompleteTreeLeaf

/-!
# Leaf existence for the rooted-parent active-set induction (GJ §18.5)

The leaf-peel induction needs that a nonempty active set has a leaf.  Abstractly,
this holds whenever the parent function strictly decreases a `rank`: the active
vertex of maximal rank is a leaf, since any vertex it parented would have strictly
larger rank.  For the complete-graph spanning-tree parent code the rank is the tree
distance from the root (`treeParent` moves one step closer to the root), giving a
leaf in every nonempty active set.

* `exists_rootedParentLeaf_of_rank`: a rank-decreasing parent has a leaf in every
  nonempty active set.
* `completeGraphTreeParentCode_rank_lt`: the parent code strictly decreases the tree
  distance from the root.
* `completeGraphTreeParentCode_exists_active_leaf`: hence every nonempty active set
  has a leaf for the complete-graph spanning-tree parent code.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open SimpleGraph

variable {n : ℕ}

/-- **A rank-decreasing parent has a leaf in every nonempty active set.**  If
`rank (par i) < rank (Fin.succ i)` for all `i`, then the active vertex of maximal
`rank ∘ Fin.succ` is a leaf: any active `i` with `par i = Fin.succ j` would satisfy
`rank (Fin.succ j) < rank (Fin.succ i)`, contradicting maximality. -/
theorem exists_rootedParentLeaf_of_rank {par : Fin n → Fin (n + 1)}
    {rank : Fin (n + 1) → ℕ} (hrank : ∀ i : Fin n, rank (par i) < rank (Fin.succ i))
    {A : Finset (Fin n)} (hA : A.Nonempty) :
    ∃ j : Fin n, RootedParentLeaf par A j := by
  obtain ⟨j, hjA, hjmax⟩ := A.exists_max_image (fun j => rank (Fin.succ j)) hA
  refine ⟨j, hjA, fun i hiA hcontra => ?_⟩
  have h1 := hrank i
  rw [hcontra] at h1
  have h2 := hjmax i hiA
  omega

/-- **The complete-graph spanning-tree parent code strictly decreases the root
distance.**  The parent of `Fin.succ i` is one step closer to the root `0` in the
tree, so `dist 0 (parentCode i) < dist 0 (Fin.succ i)`. -/
theorem completeGraphTreeParentCode_rank_lt
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) :
    ∀ i : Fin n,
      (fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).dist 0
          (Penrose.completeGraphTreeParentCode n T i)
        < (fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).dist 0 (Fin.succ i) := by
  intro i
  have h2 := (Penrose.treeParent_spec
    (Penrose.isTree_fromEdgeSet_of_mem_spanningTreeEdgeSubsets T.2)
    0 (Fin.succ i) (Fin.succ_ne_zero i)).2
  simp only [Penrose.completeGraphTreeParentCode]
  omega

/-- **Every nonempty active set has a leaf for the complete-graph spanning-tree
parent code.**  Specialising the rank criterion to the tree distance from the
root. -/
theorem completeGraphTreeParentCode_exists_active_leaf {A : Finset (Fin n)}
    (hA : A.Nonempty)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) :
    ∃ j : Fin n, RootedParentLeaf (Penrose.completeGraphTreeParentCode n T) A j :=
  exists_rootedParentLeaf_of_rank
    (rank := fun v => (fromEdgeSet (↑T.1 : Set (Sym2 (Fin (n + 1))))).dist 0 v)
    (completeGraphTreeParentCode_rank_lt T) hA

end IsingModel
