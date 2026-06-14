import IsingModel.AbstractPolymer.Cluster

/-!
# Truncated rooted cluster sum (GJ §18.4–18.5)

The per-polymer (rooted) cluster sum of the abstract polymer model
(`AbstractPolymer/`, Issue #3954), truncated to clusters of size at most `N`:

`clusterSumLE Incompat z N p =
  ∑_{n < N} ∑_{ω : Fin (n+1) → P, ω 0 = p, connected} |ϕ^T(ω)| · |∏ z(ω_i)|`,

the sum of `|ursellCoeff|·|clusterActivity|` over connected polymer sequences of
length `≤ N` anchored at `p`.  This finite truncation is the object of the
Kotecký–Preiss induction: the all-order theorem bounds `clusterSumLE … N p ≤ a p`
uniformly in `N` (so the full cluster sum, its supremum, is `≤ a p` and the
expansion converges absolutely).

This file records the basic order structure (non-negativity, monotonicity in the
truncation level `N`) on which the bounded-monotone convergence argument rests;
the all-order bound itself is the subsequent inductive step.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **Connected clusters anchored at `p` of size `n + 1`**: the length-`(n+1)`
polymer sequences `ω` with `ω 0 = p` whose incompatibility graph is connected. -/
def rootedClusters (Incompat : P → P → Prop) [DecidableRel Incompat]
    (n : ℕ) (p : P) : Finset (Fin (n + 1) → P) :=
  (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset P))).filter
    (fun ω => ω 0 = p ∧ (seqGraph Incompat ω).Connected)

/-- **Truncated rooted cluster sum**: `∑_{n < N} ∑_{ω ∈ rootedClusters n p}
|ursellCoeff ω| · |clusterActivity z ω|` — the absolute cluster sum over
connected clusters of size `≤ N` anchored at `p`. -/
noncomputable def clusterSumLE (Incompat : P → P → Prop) [DecidableRel Incompat]
    (z : P → ℝ) (N : ℕ) (p : P) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ ω ∈ rootedClusters Incompat n p,
    |ursellCoeff Incompat ω| * |clusterActivity z ω|

variable {Incompat : P → P → Prop} [DecidableRel Incompat] {z : P → ℝ}

/-- **The truncated rooted cluster sum is non-negative**. -/
theorem clusterSumLE_nonneg (N : ℕ) (p : P) : 0 ≤ clusterSumLE Incompat z N p :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-- **The truncated rooted cluster sum is monotone in the truncation level**:
adding longer clusters (`N ≤ M`) only increases the (non-negative) sum. -/
theorem clusterSumLE_mono {N M : ℕ} (h : N ≤ M) (p : P) :
    clusterSumLE Incompat z N p ≤ clusterSumLE Incompat z M p := by
  unfold clusterSumLE
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro n _ _
  exact Finset.sum_nonneg (fun _ _ => by positivity)

end IsingModel.AbstractPolymer
