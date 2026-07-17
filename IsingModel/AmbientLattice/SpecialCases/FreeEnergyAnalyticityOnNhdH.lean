import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient freeEnergyAlongExhaustion AnalyticOnNhd in `h`

Narrow child module for the ambient
`freeEnergyAlongExhaustion_analyticOnNhd_h` wrapper extracted from
`FreeEnergyAnalyticityOnNhd.lean`.

The result is a thin pass-through of the Λ-level
`freeEnergyΛ_analyticOnNhd_h` lemma. The theorem name is unchanged
from the former `FreeEnergyAnalyticity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_h G (Λ.volume n) J β

end Ambient
end IsingModel
