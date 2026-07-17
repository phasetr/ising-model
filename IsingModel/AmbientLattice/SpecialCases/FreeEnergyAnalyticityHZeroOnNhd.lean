import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient freeEnergyAlongExhaustion h=0 `AnalyticOnNhd` wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_analyticOnNhd_*_h_zero` wrappers
extracted from `FreeEnergyAnalyticityHZero.lean`:

* `freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero`
* `freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero`

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analyticOnNhd_*_h_zero` lemma. The theorem names are
unchanged from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_h_zero G (Λ.volume n) β

end Ambient
end IsingModel
