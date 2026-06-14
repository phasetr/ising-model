import IsingModel.ClusterExpansion.Penrose.IntervalPartition
import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Penrose tree-graph inequality (GJ §18.4-18.5, Issue #3954)

The capstone of the from-scratch Penrose programme (milestone M1):
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`.

The Kruskal retraction `treeOf` maps the connected spanning edge-subsets of `G` onto
its spanning trees, and its fibers are the Boolean intervals
`[T, T ∪ addable G T]` (`treeOf_fiber_eq_booleanInterval`).  Summing fiberwise and
applying the Boolean-interval sign cancellation, each fiber contributes `0` when its
addable part is nonempty and `±1` when it is empty, so the alternating
connected-subgraph sum is bounded in absolute value by the number of spanning trees.

This is the sole hard combinatorial input for general interacting cluster-expansion
convergence; the Kotecký–Preiss tree-sum induction builds on it.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Penrose tree-graph inequality (Brydges' lectures).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.Penrose

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Each Boolean-interval fiber contributes at most `1`**: the alternating sum over
`[T, T ∪ addable G T]` is `0` when `addable G T` is nonempty (the addable part
`(T ∪ addable G T) \ T = addable G T` is nonempty, so the signs cancel) and `±1` when
`addable G T` is empty (the singleton interval `{T}`). -/
theorem abs_sum_booleanInterval_addable_le_one (T : Finset (Sym2 V)) :
    |∑ S ∈ booleanInterval T (T ∪ addable G T), (-1 : ℝ) ^ S.card| ≤ 1 := by
  have hsub : T ⊆ T ∪ addable G T := Finset.subset_union_left
  have hsdiff : (T ∪ addable G T) \ T = addable G T :=
    Finset.union_sdiff_cancel_left (addable_disjoint G T)
  by_cases hne : (addable G T).Nonempty
  · rw [sum_booleanInterval_neg_one_pow_card_real_of_sdiff_nonempty hsub
      (by rw [hsdiff]; exact hne)]
    simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have heq : T ∪ addable G T = T := by rw [hne, Finset.union_empty]
    rw [sum_booleanInterval_neg_one_pow_card_real_of_eq heq]
    simp

/-- **Penrose tree-graph inequality**: for a finite graph `G`,
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`.  The connected spanning
edge-subsets partition into Boolean intervals indexed by spanning trees (the fibers of
`treeOf`), each contributing at most `1` in absolute value to the alternating sum. -/
theorem abs_alternatingConnectedSubgraphSum_le_numSpanningTrees :
    |alternatingConnectedSubgraphSum G| ≤ (numSpanningTrees G : ℝ) := by
  have H : ∀ S ∈ connectedSpanningEdgeSubsets G, treeOf S ∈ spanningTreeEdgeSubsets G :=
    fun S hS => treeOf_mem_spanningTreeEdgeSubsets hS
  unfold alternatingConnectedSubgraphSum
  rw [← Finset.sum_fiberwise_of_maps_to H (fun S => (-1 : ℝ) ^ S.card)]
  calc |∑ T ∈ spanningTreeEdgeSubsets G,
          ∑ S ∈ (connectedSpanningEdgeSubsets G).filter (fun S => treeOf S = T),
            (-1 : ℝ) ^ S.card|
      ≤ ∑ T ∈ spanningTreeEdgeSubsets G,
          |∑ S ∈ (connectedSpanningEdgeSubsets G).filter (fun S => treeOf S = T),
            (-1 : ℝ) ^ S.card| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ spanningTreeEdgeSubsets G, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun T hT => ?_)
        rw [treeOf_fiber_eq_booleanInterval hT]
        exact abs_sum_booleanInterval_addable_le_one T
    _ = (numSpanningTrees G : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, numSpanningTrees]

end IsingModel.Penrose
