import IsingModel.AbstractPolymer.TreeGraphInequality
import IsingModel.AbstractPolymer.ClusterSum

/-!
# Ursell tree bound — from the tree-graph inequality to the cluster sum (GJ §18.4)

The Penrose tree-graph inequality (`AbstractPolymer/TreeGraphInequality.lean`)
bounds the alternating connected-subgraph sum of a single graph by its number of
spanning trees.  This file lifts that bound to the *Ursell coefficient* of a
polymer sequence and, via a family of partition schemes
(`UrsellTreeBound`), to the truncated rooted cluster sum `clusterSumLE`:

`clusterSumLE Incompat z N p ≤ treeSumLE Incompat z N p`,

where `treeSumLE` is `clusterSumLE` with each `|ursellCoeff ω|` replaced by its
Penrose majorant `#{spanning trees of seqGraph ω} / (n+1)!`.  This reduces the
analytic Kotecký–Preiss cluster-sum bound to a bound on `treeSumLE` — a pure
tree-count × activity sum, the object of the labeled-tree generating-function
induction (FV §5.7) that closes the all-order theorem via
`KPAdmissible.weighted_le`.

## References

* O. Penrose, in *Statistical Mechanics* (1967).
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {Incompat : P → P → Prop} [DecidableRel Incompat]

omit [Fintype P] [DecidableEq P] in
/-- **Penrose bound on the Ursell coefficient**: given a partition scheme for the
incompatibility graph of `ω`, the Ursell coefficient is bounded by the number of
spanning trees of that graph, divided by `n!`. -/
theorem ursellCoeff_abs_le_card_spanningTrees_div_factorial {n : ℕ} (ω : Fin n → P)
    (sch : PenrosePartitionScheme (seqGraph Incompat ω)) :
    |ursellCoeff Incompat ω|
      ≤ (spanningTreeEdgeSubsets (seqGraph Incompat ω)).card / (n.factorial : ℝ) := by
  rw [ursellCoeff, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)]
  gcongr
  exact abs_alternatingConnectedSubgraphSum_le_card_spanningTrees sch

omit [Fintype P] [DecidableEq P] in
/-- **Penrose bound on a cluster-sum term**: `|ursellCoeff ω|·|clusterActivity z ω|`
is bounded by `#{spanning trees of seqGraph ω}/n! · |clusterActivity z ω|`. -/
theorem ursellCoeff_mul_clusterActivity_abs_le {n : ℕ} (ω : Fin n → P) (z : P → ℝ)
    (sch : PenrosePartitionScheme (seqGraph Incompat ω)) :
    |ursellCoeff Incompat ω| * |clusterActivity z ω|
      ≤ (spanningTreeEdgeSubsets (seqGraph Incompat ω)).card / (n.factorial : ℝ)
        * |clusterActivity z ω| := by
  gcongr
  exact ursellCoeff_abs_le_card_spanningTrees_div_factorial ω sch

/-- **Ursell tree-bound datum**: a family of Penrose partition schemes, one for
every polymer-sequence incompatibility graph.  This is the combinatorial input
(Penrose's construction) that turns the per-graph tree-graph inequality into a
uniform bound on every Ursell coefficient of the abstract polymer model. -/
structure UrsellTreeBound (Incompat : P → P → Prop) [DecidableRel Incompat] where
  /-- A partition scheme for the incompatibility graph of every polymer sequence. -/
  scheme : ∀ {n : ℕ} (ω : Fin n → P), PenrosePartitionScheme (seqGraph Incompat ω)

/-- **Truncated rooted tree-bound sum**: `clusterSumLE` with each `|ursellCoeff|`
replaced by its Penrose majorant `#{spanning trees of seqGraph ω}/(n+1)!`.  By the
tree-graph inequality this dominates `clusterSumLE` termwise (see
`clusterSumLE_le_treeSumLE`), reducing the analytic cluster-sum bound to a bound
on this pure tree-count × activity sum — the object of the labeled-tree
generating-function induction. -/
noncomputable def treeSumLE (Incompat : P → P → Prop) [DecidableRel Incompat]
    (z : P → ℝ) (N : ℕ) (p : P) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ ω ∈ rootedClusters Incompat n p,
    (spanningTreeEdgeSubsets (seqGraph Incompat ω)).card / ((n + 1).factorial : ℝ)
      * |clusterActivity z ω|

/-- **The tree-bound sum is non-negative**. -/
theorem treeSumLE_nonneg (z : P → ℝ) (N : ℕ) (p : P) : 0 ≤ treeSumLE Incompat z N p :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-- **The tree-bound sum is monotone in the truncation level**. -/
theorem treeSumLE_mono (z : P → ℝ) {N M : ℕ} (h : N ≤ M) (p : P) :
    treeSumLE Incompat z N p ≤ treeSumLE Incompat z M p := by
  unfold treeSumLE
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro n _ _
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- **The cluster sum is dominated by the tree-bound sum**: given a family of
partition schemes, `clusterSumLE Incompat z N p ≤ treeSumLE Incompat z N p`.  This
is the bridge from the (signed, cancellation-heavy) Ursell coefficients to a pure
tree-count majorant, on which the Kotecký–Preiss convergence bound will be proven
by the labeled-tree generating-function induction. -/
theorem clusterSumLE_le_treeSumLE (htb : UrsellTreeBound Incompat)
    (z : P → ℝ) (N : ℕ) (p : P) :
    clusterSumLE Incompat z N p ≤ treeSumLE Incompat z N p := by
  unfold clusterSumLE treeSumLE
  refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun ω _ => ?_))
  exact ursellCoeff_mul_clusterActivity_abs_le ω z (htb.scheme ω)

end IsingModel.AbstractPolymer
