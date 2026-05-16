import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityHZeroOnNhd

/-!
# Ambient freeEnergyAlongExhaustion h=0 `AnalyticAt` wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_analyticAt_*_h_zero` wrappers extracted
from `FreeEnergyAnalyticity.lean`:

* `freeEnergyAlongExhaustion_analyticAt_beta_h_zero`,
* `freeEnergyAlongExhaustion_analyticAt_J_h_zero`.

The two corresponding `AnalyticOnNhd` wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityHZeroOnNhd`
and are re-imported through this parent module. Each result is a
thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analytic*_*_h_zero` lemma. The theorem names are
unchanged from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  freeEnergyΛ_analyticAt_beta_h_zero G (Λ.volume n) J β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  freeEnergyΛ_analyticAt_J_h_zero G (Λ.volume n) β J

/-! ## Moved: 2 `AnalyticOnNhd` h=0 wrappers

The two `freeEnergyAlongExhaustion_analyticOnNhd_*_h_zero` wrappers
(`_beta_h_zero`, `_J_h_zero`) now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityHZeroOnNhd`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
