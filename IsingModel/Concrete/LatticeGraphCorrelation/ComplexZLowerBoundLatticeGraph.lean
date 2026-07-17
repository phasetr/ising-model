import IsingModel.AmbientComplexAnalyticity.HighTempExpansion
import IsingModel.Lattice

/-!
# ℤ^d complex Z lower bound per stage

`latticeGraph d`-specialization of the per-stage Λ-layer complex partition
function lower bound
`Ambient.partitionFunctionComplexAlongExhaustion_norm_ge_eps_on_closedBall_at_zero_beta_real_J`
(Issue #3054). For each exhaustion stage `n` and fixed real coupling `J`, there
exist `r > 0` and `ε > 0` such that
`ε ≤ ‖partitionFunctionComplexAlongExhaustion (latticeGraph d) Λ (J:ℂ) 0 β n‖`
on `Metric.closedBall (0 : ℂ) r`. The per-stage hZ provider via the
cluster-expansion route; cross-stage volume-uniformity remains the open hard
core for the Lemma 17.5.2 `hZ` provider (Issue #3044).
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage complex partition function lower bound** (Issue #3054):
specialization of
`Ambient.partitionFunctionComplexAlongExhaustion_norm_ge_eps_on_closedBall_at_zero_beta_real_J`
to `G = IsingModel.latticeGraph d`. For each exhaustion stage `n` and fixed real
coupling `J`, there exist `r > 0` and `ε > 0` such that the closed-ball lower
bound for `partitionFunctionComplexAlongExhaustion (latticeGraph d) Λ (J:ℂ) 0`
holds. -/
theorem partitionFunctionComplexAlongEx_norm_ge_eps_closedBall_zero_beta_realJ_lattice
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    ∃ r > 0, ∃ ε > 0, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) 0 β n‖ :=
  Ambient.partitionFunctionComplexAlongExhaustion_norm_ge_eps_on_closedBall_at_zero_beta_real_J
    (IsingModel.latticeGraph d) Λ J n

end Ambient
end IsingModel
