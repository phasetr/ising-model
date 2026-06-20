import IsingModel.ClusterExpansion.PolymerCounting
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Per-vertex polymer activity bound (GJ §18.5)

Summing the volume-uniform rooted polymer count of `PolymerCounting`
(`rootedPolymersOfCard_card_le_maxDegree_pow`, `≤ Δ^{2ℓ}`) against the activity
`t^ℓ` gives the geometric series bound
`∑_{P ∋ v} t^{|P|} ≤ (1 − Δ²t)⁻¹` under `0 ≤ t` and `Δ²t < 1`, where
`Δ = G.maxDegree`.  This bound depends only on the maximum degree, **not** on the
volume — the per-vertex Kotecky--Preiss activity input that survives the
infinite-volume limit, unlike the per-volume conditions of
`InteractingFreeEnergyMayerHighTemp`.

The result is a finite-graph bound in terms of `G.maxDegree`; assembling the full
volume-uniform Kotecky--Preiss convergence and the infinite-volume pressure from
it is later work.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.3, eq.~(3.49).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polymer activity through a vertex `v`: `∑_{P ∋ v} t^{|P|}`. -/
noncomputable def rootedPolymerActivity (G : SimpleGraph ι) [Fintype G.edgeSet]
    (v : ι) (t : ℝ) : ℝ :=
  ∑ P ∈ rootedPolymers G v, t ^ P.card

/-- **Per-vertex polymer activity bound (volume-uniform).**  For `0 ≤ t` and
`Δ²t < 1` (`Δ = G.maxDegree`), the polymer activity through `v` is bounded by the
geometric series `(1 − Δ²t)⁻¹`, independently of the volume. -/
theorem rootedPolymerActivity_le_geometric (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (v : ι) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (G.maxDegree : ℝ) ^ 2 * t < 1) :
    rootedPolymerActivity G v t ≤ (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
  have hr0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * t := mul_nonneg (by positivity) ht0
  have hmaps : ∀ P ∈ rootedPolymers G v, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    rw [rootedPolymers, Finset.mem_filter] at hP
    have hsub : P ⊆ G.edgeFinset := (mem_allPolymers.mp hP.1).isEven.subset
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hsub))
  rw [rootedPolymerActivity,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun P => t ^ P.card)]
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), t ^ P.card)
        ≤ ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by
    intro ℓ _
    have hconst : (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), t ^ P.card)
        = ((rootedPolymersOfCard G v ℓ).card : ℝ) * t ^ ℓ := by
      rw [rootedPolymersOfCard]
      rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2]]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcount : ((rootedPolymersOfCard G v ℓ).card : ℝ) ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) := by
      exact_mod_cast rootedPolymersOfCard_card_le_maxDegree_pow G v ℓ
    calc ((rootedPolymersOfCard G v ℓ).card : ℝ) * t ^ ℓ
        ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) * t ^ ℓ :=
          mul_le_mul_of_nonneg_right hcount (pow_nonneg ht0 ℓ)
      _ = ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by rw [mul_pow, pow_mul]
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  refine le_trans ((summable_geometric_of_lt_one hr0 ht).sum_le_tsum _
    (fun ℓ _ => pow_nonneg hr0 ℓ)) ?_
  rw [tsum_geometric_of_lt_one hr0 ht]

end IsingModel
