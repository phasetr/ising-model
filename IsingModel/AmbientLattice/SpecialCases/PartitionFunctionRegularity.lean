import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularityAnalytic
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularityDifferentiable

/-!
# Ambient partition-function regularity wrappers

This module contains general-graph `Continuous`, `Differentiable`,
`AnalyticAt`, and `AnalyticOnNhd` APIs for per-stage
`partitionFunctionAlongExhaustion` at zero external field. It is split out of
the legacy ambient special-cases module so concrete partition-function
regularity wrappers can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition-function regularity at `h = 0` -/

/-- **Along-ex: partitionFunction Continuous in `β` at `h = 0`,
per stage `n`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n) :=
  partitionFunctionΛ_continuous_J_h_zero G (Λ.volume n) β

/-! ## Moved: 2 partitionFunctionAlongExhaustion h=0 Differentiable wrappers

The two `Differentiable ℝ` wrappers
(`partitionFunctionAlongExhaustion_differentiable_beta_h_zero`,
`partitionFunctionAlongExhaustion_differentiable_J_h_zero`) now live
in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularityDifferentiable`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-! ## Moved: partitionFunctionAlongExhaustion h=0 analyticity wrappers

The four `partitionFunctionAlongExhaustion_analytic*_*_h_zero`
wrappers (AnalyticAt × {beta,J}, AnalyticOnNhd × {beta,J}) now live in
`PartitionFunctionRegularityAnalytic.lean`. They are re-imported here
so downstream consumers continue to see the symbols. -/



end Ambient
end IsingModel
