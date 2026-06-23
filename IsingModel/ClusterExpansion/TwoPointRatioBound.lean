import IsingModel.ClusterExpansion.TwoPointNumeratorEquality
import IsingModel.ClusterExpansion.TwoPointAnchoredCount
import IsingModel.ClusterExpansion.GeometricFiberSum

/-!
# Two-point ratio bound reduced to a per-component avoiding-ratio estimate (GJ §18.4–18.7)

Capstone reduction toward the volume-uniform two-point bound `hbdd` (Issue #4230, item D of #4214).
Combining the exact complex factorization
`Q_{i,j}(t) = ∑_{C ∈ connectingComponents G i j} t^{|C|} · ZAvoid_C(t)`
(`htSubgraphSum_pair_eq_sum_connectingComponent`) with the volume-uniform anchored count
`|{C : |C| = ℓ}| ≤ Δ^{2ℓ}` (`connectingComponentsOfCard_card_le_maxDegree_pow`) and the geometric
fiber-summation lemma (`sum_le_geometric_closed_of_fiber_card_le`), the norm of the two-point ratio
`‖Q_{i,j}/Q_∅‖` is bounded by a *volume-uniform* geometric value `A/(1 - a·Δ²)` **provided** each
per-component avoiding ratio satisfies `‖t‖^{|C|}·‖ZAvoid_C/Q_∅‖ ≤ A·a^{|C|}`.

This mirrors `correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound` (#4235), which
reduced infinite-volume correlation analyticity to a single Ising hypothesis: here the remaining
hypothesis `hbound` is the **local Kotecký–Preiss avoiding-ratio estimate**
`‖ZAvoid_C(t)/Q_∅(t)‖ ≤ exp(κ·|support C|)` (the genuine cluster-expansion core), discharged in
a following PR.  Once discharged with `A = exp κ`, `a = ‖t‖·exp κ`, the bound is volume-uniform for
`‖t‖·exp(κ)·Δ² < 1` (small `β`).

## Main result
* `twoPointRatio_norm_le_geometric` — `‖Q_{i,j}/Q_∅‖ ≤ A/(1 - a·Δ²)` from the per-component bound.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7; Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Two-point ratio bound from a per-component avoiding-ratio estimate** (GJ §18.4–18.7).  If each
connecting component `C` satisfies `‖t‖^{|C|}·‖ZAvoid_C(t)/Q_∅(t)‖ ≤ A·a^{|C|}` and the geometric
ratio `a·Δ²` is below `1` (with `Δ = G.maxDegree`), then the two-point ratio norm is bounded by the
volume-uniform value `A/(1 - a·Δ²)`.  The hypothesis is the local KP avoiding-ratio estimate; the
count of size-`ℓ` connecting components is `≤ Δ^{2ℓ}`
(`connectingComponentsOfCard_card_le_maxDegree_pow`) and the geometric summation is
`sum_le_geometric_closed_of_fiber_card_le`. -/
theorem twoPointRatio_norm_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {i j : ι} (hij : i ≠ j) (t : ℂ)
    (A a : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hbound : ∀ C ∈ connectingComponents G i j,
      ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ A * a ^ C.card)
    (hq : a * ((G.maxDegree : ℝ) ^ 2) < 1) :
    ‖htSubgraphSum G ({i, j} : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖
      ≤ A / (1 - a * ((G.maxDegree : ℝ) ^ 2)) := by
  classical
  set Q0 : ℂ := htSubgraphSum G (∅ : Finset ι) t with hQ0
  -- the ratio is the sum over connecting components of the per-component ratios
  have hsum : htSubgraphSum G ({i, j} : Finset ι) t / Q0
      = ∑ C ∈ connectingComponents G i j, t ^ C.card * (htSubgraphSumAvoiding G C t / Q0) := by
    rw [htSubgraphSum_pair_eq_sum_connectingComponent G hij t, Finset.sum_div]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [mul_div_assoc]
  -- bound the norm by the sum of per-component norms
  have hnorm : ‖htSubgraphSum G ({i, j} : Finset ι) t / Q0‖
      ≤ ∑ C ∈ connectingComponents G i j,
          ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / Q0‖ := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun C _ => ?_)
    rw [norm_mul, norm_pow]
  refine hnorm.trans ?_
  -- apply the geometric fiber-count bound
  refine sum_le_geometric_closed_of_fiber_card_le
    (connectingComponents G i j) (fun C => C.card)
    (fun C => ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / Q0‖)
    A a ((G.maxDegree : ℝ) ^ 2) G.edgeFinset.card ?_ ?_ ?_ ?_ hA ha ?_ hq
  · -- sizes are at most the number of edges
    intro C hC
    rw [connectingComponents, Finset.mem_filter, Finset.mem_powerset] at hC
    exact Finset.card_le_card hC.1
  · -- nonnegativity of the weights
    intro C _
    exact mul_nonneg (pow_nonneg (norm_nonneg t) _) (norm_nonneg _)
  · -- the per-component bound
    exact hbound
  · -- fiber-count bound: components of size n number at most (Δ²)^n
    intro n
    have hcount := connectingComponentsOfCard_card_le_maxDegree_pow G i j n
    have hcast : (((connectingComponents G i j).filter (fun C => C.card = n)).card : ℝ)
        ≤ ((G.maxDegree ^ (2 * n) : ℕ) : ℝ) := by exact_mod_cast hcount
    refine hcast.trans ?_
    rw [Nat.cast_pow, pow_mul]
  · -- nonnegativity of Δ²
    positivity

end IsingModel
