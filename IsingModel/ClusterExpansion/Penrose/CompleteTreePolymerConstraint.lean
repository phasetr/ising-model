import IsingModel.ClusterExpansion.Penrose.PolymerSeqTreeOrientation

/-!
# Parent-edge incompatibility for complete-graph spanning trees (GJ §18.5)

The rooted-tree Kotecky--Preiss induction reorganises the Mayer tree-sum bound by
fixing a spanning-tree *shape* `T` of the complete graph `K_{n+1}` (so the rooted
parent code `completeGraphTreeParentCode` is available) and summing over the
polymer sequences `ω` for which `T` is a spanning tree of the incompatibility graph
`polymerSeqIncompatibilityGraph ω`.

For such `ω`, every parent edge of the complete-tree parent code is an
incompatibility edge: `PolymersIncompatible (ω (succ i)) (ω (parentCode T i))`.
Hence the constraint "`T` is a spanning tree of `incompat ω`" can be *relaxed* to
the per-edge constraint "every child is incompatible with its parent", which is the
starting point of the leaf-removal KP induction.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Complete-tree parent edges are incompatibility edges.**  If the complete-graph
spanning tree `T` (rooted via `completeGraphTreeParentCode`) is also a spanning tree
of the incompatibility graph of `ω`, then every non-root vertex `succ i` is
incompatible with its parent: `PolymersIncompatible (ω (succ i)) (ω (parentCode T i))`.
The parent edge lies in `T`, which lies in the incompatibility graph's edge set. -/
theorem completeTree_parent_incompatible_of_mem_spanningTreeIncompat (n : ℕ)
    (ω : Fin (n + 1) → Finset (Sym2 ι))
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))})
    (hTω : T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω))
    (i : Fin n) :
    PolymersIncompatible (ω (Fin.succ i)) (ω (Penrose.completeGraphTreeParentCode n T i)) := by
  have hedge : s(Fin.succ i, Penrose.completeGraphTreeParentCode n T i) ∈ T.1 := by
    rw [Penrose.completeGraphTree_edges_eq_parentCode_image n T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsub : T.1 ⊆ (polymerSeqIncompatibilityGraph ω).edgeFinset :=
    (Penrose.mem_spanningTreeEdgeSubsets.mp hTω).1.1
  have hadj := hsub hedge
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hadj
  exact (polymerSeqIncompatibilityGraph_adj.mp hadj).2

/-- **Relaxing the spanning-tree constraint to per-edge incompatibility.**  For a
fixed complete-tree shape `T` and a non-negative weight `W`, the sum of `W` over the
sequences `ω` for which `T` is a spanning tree of `incompat ω` is at most the sum
over the sequences for which every child is incompatible with its parent.  The first
filter is contained in the second by the parent-edge incompatibility above. -/
theorem sum_filter_treeIncompat_le_filter_parentConstraint (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))})
    (A : Finset (Fin (n + 1) → Finset (Sym2 ι)))
    (W : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ) (hW : ∀ ω, 0 ≤ W ω) :
    (∑ ω ∈ A.filter (fun ω =>
        T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)), W ω)
      ≤ ∑ ω ∈ A.filter (fun ω =>
          ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
            (ω (Penrose.completeGraphTreeParentCode n T i))), W ω := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ => hW ω
  intro ω hω
  rw [Finset.mem_filter] at hω ⊢
  exact ⟨hω.1, fun i =>
    completeTree_parent_incompatible_of_mem_spanningTreeIncompat n ω T hω.2 i⟩

end IsingModel
