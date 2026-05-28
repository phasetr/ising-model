import IsingModel.AmbientComplexAnalyticity.Basic.Core
import IsingModel.ComplexAnalyticity.HighTempExpansion

/-!
# Per-stage complex partition function lower bound along an exhaustion

This module lifts the per-fixed-volume complex `Z` lower bound
`partitionFunctionComplex_norm_ge_eps_on_closedBall_at_zero_beta_real_J`
(`IsingModel.ComplexAnalyticity.HighTempExpansion`) to the
along-exhaustion API of
`IsingModel.Ambient.partitionFunctionComplexAlongExhaustion`. The lift is
per-stage: for each exhaustion index `n`, there is a closed disc around
`β = 0` on which `Z_ℂ_{Λ_n}` is bounded below by some `ε_n > 0`. Both `r` and
`ε` depend on `n`; volume-uniformity is the open research-level hard core for
the Lemma 17.5.2 `hZ` provider (Issue #3044) via the cluster-expansion route
(Issue #3054).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Per-stage along-exhaustion complex partition function lower bound**
(Issue #3054): for each fixed real coupling `J` and each exhaustion stage `n`,
there exist `r > 0` and `ε > 0` such that
`ε ≤ ‖partitionFunctionComplexAlongExhaustion G Λ (J:ℂ) 0 β n‖` for all
`β ∈ Metric.closedBall (0 : ℂ) r`. Per-stage lift of
`partitionFunctionComplex_norm_ge_eps_on_closedBall_at_zero_beta_real_J` (PR
#3065) via the `partitionFunctionComplexAlongExhaustion_apply` unfolding.

The radius `r` and lower bound `ε` depend on the exhaustion stage `n` (volume
of `inducedGraph G (Λ.volume n)`); volume-uniformity remains the open hard
core for the Lemma 17.5.2 `hZ` provider (Issue #3044). -/
theorem partitionFunctionComplexAlongExhaustion_norm_ge_eps_on_closedBall_at_zero_beta_real_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    ∃ r > 0, ∃ ε > 0, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) 0 β n‖ := by
  classical
  -- Reduce to the per-fixed-volume bound at `inducedGraph G (Λ.volume n)`.
  obtain ⟨r, hr, ε, hε, hbound⟩ :=
    IsingModel.partitionFunctionComplex_norm_ge_eps_on_closedBall_at_zero_beta_real_J
      (inducedGraph G (Λ.volume n)) J
  refine ⟨r, hr, ε, hε, ?_⟩
  intro β hβ
  rw [partitionFunctionComplexAlongExhaustion_apply]
  exact hbound β hβ

end Ambient
end IsingModel
