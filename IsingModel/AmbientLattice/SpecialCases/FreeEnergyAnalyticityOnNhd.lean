import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityOnNhdH

/-!
# Ambient freeEnergyAlongExhaustion AnalyticOnNhd general-h β/J wrappers

Narrow child module for the two ambient
`freeEnergyAlongExhaustion_analyticOnNhd_*_general_h` wrappers
extracted from `FreeEnergyAnalyticity.lean`:

* `freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h`
* `freeEnergyAlongExhaustion_analyticOnNhd_J_general_h`

The corresponding `h`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityOnNhdH`
and is re-imported through this parent module. Each result is a
thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analyticOnNhd_*` lemma. The theorem names are
unchanged from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_general_h G (Λ.volume n) β h

/-! ## Moved: 1 AnalyticOnNhd `h` wrapper

The `freeEnergyAlongExhaustion_analyticOnNhd_h` wrapper now lives
in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityOnNhdH`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
