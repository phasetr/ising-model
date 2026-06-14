import IsingModel.AbstractPolymer.UrsellTreeBound

/-!
# Bounded-monotone convergence of the rooted cluster sum (GJ §18.4)

The truncated rooted cluster sum `clusterSumLE Incompat z N p` is non-negative and
monotone non-decreasing in the truncation level `N` (`AbstractPolymer/ClusterSum.lean`).
Hence, *once* the all-order Kotecký–Preiss bound `clusterSumLE Incompat z N p ≤ a p`
is available uniformly in `N`, the sequence converges to its supremum

`rootedClusterSum Incompat z p := ⨆ N, clusterSumLE Incompat z N p`,

and that supremum is `≤ a p`.  This file packages that final convergence step:
monotonicity (`clusterSumLE_monotone`, `treeSumLE_monotone`), the limit
(`tendsto_clusterSumLE_atTop` under `BddAbove`), and the supremum bound
(`rootedClusterSum_le`, hence `rootedClusterSum_le_weight`).  It thereby reduces
the entire remaining convergence theorem to the single analytic input — the
all-order bound — leaving the labeled-tree generating-function induction and the
partition-scheme construction as the only outstanding work.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7 (Theorem 5.4).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {Incompat : P → P → Prop} [DecidableRel Incompat] {z : P → ℝ}

/-- **The truncated cluster sum is monotone in the truncation level** (sequence
form of `clusterSumLE_mono`). -/
theorem clusterSumLE_monotone (p : P) : Monotone (fun N => clusterSumLE Incompat z N p) :=
  fun _ _ h => clusterSumLE_mono h p

/-- **The truncated tree-bound sum is monotone in the truncation level** (sequence
form of `treeSumLE_mono`). -/
theorem treeSumLE_monotone (p : P) : Monotone (fun N => treeSumLE Incompat z N p) :=
  fun _ _ h => treeSumLE_mono z h p

/-- **The rooted cluster sum**: the supremum over all truncation levels of the
truncated rooted cluster sum, `⨆ N, clusterSumLE Incompat z N p`.  When the
truncations are bounded (the all-order KP bound) this is the genuine limit of the
absolutely convergent cluster expansion rooted at `p`. -/
noncomputable def rootedClusterSum (Incompat : P → P → Prop) [DecidableRel Incompat]
    (z : P → ℝ) (p : P) : ℝ :=
  ⨆ N, clusterSumLE Incompat z N p

/-- **Convergence of the truncated cluster sum**: if the truncations are bounded
above, the monotone sequence `N ↦ clusterSumLE Incompat z N p` converges to its
supremum `rootedClusterSum Incompat z p`. -/
theorem tendsto_clusterSumLE_atTop (p : P)
    (hbdd : BddAbove (Set.range (fun N => clusterSumLE Incompat z N p))) :
    Filter.Tendsto (fun N => clusterSumLE Incompat z N p) Filter.atTop
      (nhds (rootedClusterSum Incompat z p)) :=
  tendsto_atTop_ciSup (clusterSumLE_monotone p) hbdd

/-- **The rooted cluster sum inherits any uniform bound on its truncations**: if
`clusterSumLE Incompat z N p ≤ C` for every `N`, then `rootedClusterSum ≤ C`. -/
theorem rootedClusterSum_le (p : P) {C : ℝ}
    (h : ∀ N, clusterSumLE Incompat z N p ≤ C) :
    rootedClusterSum Incompat z p ≤ C :=
  ciSup_le h

/-- **The rooted cluster sum is non-negative** (when bounded): `0 ≤ clusterSumLE 0 p`
is dominated by the supremum. -/
theorem rootedClusterSum_nonneg (p : P)
    (hbdd : BddAbove (Set.range (fun N => clusterSumLE Incompat z N p))) :
    0 ≤ rootedClusterSum Incompat z p :=
  le_trans (clusterSumLE_nonneg 0 p) (le_ciSup hbdd 0)

/-- **Convergence headline (conditional on the all-order bound)**: for a
KP-admissible weight `a`, if every truncation satisfies `clusterSumLE … N p ≤ a p`,
then the rooted cluster sum converges with `rootedClusterSum Incompat z p ≤ a p`.
This is the bounded-monotone reduction: the whole convergence theorem follows from
the all-order bound. -/
theorem rootedClusterSum_le_weight {a : P → ℝ} (p : P)
    (h : ∀ N, clusterSumLE Incompat z N p ≤ a p) :
    rootedClusterSum Incompat z p ≤ a p :=
  rootedClusterSum_le p h

end IsingModel.AbstractPolymer
