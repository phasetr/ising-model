import IsingModel.AbstractPolymer.UrsellTreeBound

/-!
# Base case of the all-order Kotecký–Preiss bound (GJ §18.4)

The all-order KP convergence theorem will bound the truncated cluster sum
`clusterSumLE Incompat z N p ≤ a p` uniformly in `N` by induction on the
truncation level `N`.  This file establishes the **base case** `N = 1` (the
single-polymer contribution) completely:

`clusterSumLE Incompat z 1 p = |z p| ≤ a p` and
`treeSumLE Incompat z 1 p = |z p| ≤ a p`,

the second inequality holding for any KP-admissible weight `a` and
self-incompatible polymers.  The evaluations rest on the one-vertex facts
`rootedClusters Incompat 0 p = {fun _ ↦ p}` (a single polymer is the only cluster
of size one rooted at `p`) and `spanningTreeEdgeSubsets G = {∅}` for any graph on
`Fin 1` (the empty edge-set is the unique spanning tree), so the single cluster
contributes `|ϕ^T|·|z p| = |z p|` and `(#trees)/1!·|z p| = |z p|`.

The inductive step — the labeled-tree generating-function argument that absorbs
the cluster sum at each neighbour into `a p` via `KPAdmissible.weighted_le` — is
the remaining content of the theorem.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7 (Theorem 5.4).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
/-- **One-vertex connected spanning edge-subsets**: on `Fin 1` every graph is
edgeless, so the empty edge-set is the only connected spanning edge-subset. -/
theorem connectedSpanningEdgeSubsets_fin_one (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] :
    connectedSpanningEdgeSubsets G = {∅} := by
  have h_emptyG : G.edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := he
      exact (G.ne_of_adj hab) (Subsingleton.elim a b)
  apply Finset.ext
  intro S
  rw [mem_connectedSpanningEdgeSubsets, Finset.mem_singleton]
  constructor
  · rintro ⟨hS_sub, _⟩
    rw [h_emptyG, Finset.subset_empty] at hS_sub
    exact hS_sub
  · intro hS_eq
    refine ⟨?_, ?_⟩
    · rw [hS_eq]; exact Finset.empty_subset _
    · rw [hS_eq]
      refine { preconnected := ?_, nonempty := ⟨0⟩ }
      intro u v
      exact (Subsingleton.elim u v) ▸ SimpleGraph.Reachable.refl u

omit [Fintype P] [DecidableEq P] in
/-- **One-vertex spanning trees**: any graph on `Fin 1` has exactly one spanning
tree, the empty edge-set. -/
theorem spanningTreeEdgeSubsets_fin_one (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] :
    spanningTreeEdgeSubsets G = {∅} := by
  rw [spanningTreeEdgeSubsets, connectedSpanningEdgeSubsets_fin_one]
  simp [Finset.filter_singleton]

variable {Incompat : P → P → Prop} [DecidableRel Incompat]

omit [Fintype P] [DecidableEq P] in
/-- **A one-vertex incompatibility graph is connected** (single vertex). -/
theorem seqGraph_fin_one_connected (ω : Fin 1 → P) : (seqGraph Incompat ω).Connected := by
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact (Subsingleton.elim u v) ▸ SimpleGraph.Reachable.refl u

/-- **The clusters of size one rooted at `p`** are exactly the constant sequence
`fun _ ↦ p`: a single polymer is the only connected cluster of length one. -/
theorem rootedClusters_zero (p : P) :
    rootedClusters Incompat 0 p = {fun _ : Fin 1 => p} := by
  apply Finset.ext
  intro ω
  rw [rootedClusters, Finset.mem_filter, Finset.mem_singleton, Fintype.mem_piFinset]
  simp only [Finset.mem_univ, forall_const, true_and]
  constructor
  · rintro ⟨hω0, _⟩
    funext i
    rw [Fin.fin_one_eq_zero i]; exact hω0
  · rintro rfl
    exact ⟨rfl, seqGraph_fin_one_connected _⟩

/-- **The truncated cluster sum at `N = 1`** is `|z p|`: the only contribution is
the single polymer `p`, with `|ϕ^T| = 1` and activity `z p`. -/
theorem clusterSumLE_one (z : P → ℝ) (p : P) :
    clusterSumLE Incompat z 1 p = |z p| := by
  rw [clusterSumLE, Finset.sum_range_one, rootedClusters_zero, Finset.sum_singleton,
    ursellCoeff_singleton, clusterActivity_singleton, abs_one, one_mul]

/-- **The truncated tree-bound sum at `N = 1`** is `|z p|`: the single polymer has
one spanning tree (`∅`) and activity `z p`. -/
theorem treeSumLE_one (z : P → ℝ) (p : P) :
    treeSumLE Incompat z 1 p = |z p| := by
  rw [treeSumLE, Finset.sum_range_one, rootedClusters_zero, Finset.sum_singleton,
    clusterActivity_singleton, spanningTreeEdgeSubsets_fin_one]
  simp [Nat.factorial]

variable {z a : P → ℝ}

/-- **Base case of the all-order KP bound (cluster sum)**: for a KP-admissible
weight `a` with self-incompatible polymers, `clusterSumLE Incompat z 1 p ≤ a p`. -/
theorem clusterSumLE_one_le_weight (h : KPAdmissible Incompat z a)
    (hself : ∀ p, Incompat p p) (p : P) :
    clusterSumLE Incompat z 1 p ≤ a p := by
  rw [clusterSumLE_one]; exact h.activity_le_weight hself p

/-- **Base case of the all-order KP bound (tree-bound sum)**: for a KP-admissible
weight `a` with self-incompatible polymers, `treeSumLE Incompat z 1 p ≤ a p`. -/
theorem treeSumLE_one_le_weight (h : KPAdmissible Incompat z a)
    (hself : ∀ p, Incompat p p) (p : P) :
    treeSumLE Incompat z 1 p ≤ a p := by
  rw [treeSumLE_one]; exact h.activity_le_weight hself p

end IsingModel.AbstractPolymer
