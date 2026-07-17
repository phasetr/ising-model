import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient freeEnergyAlongExhaustion AnalyticAt in `h`

Narrow child module for the ambient
`freeEnergyAlongExhaustion_analyticAt_h` wrapper extracted from
`FreeEnergyAnalyticity.lean`.

The result is a thin pass-through of the Λ-level
`freeEnergyΛ_analyticAt_h` lemma. The theorem name is unchanged
from the former `FreeEnergyAnalyticity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  freeEnergyΛ_analyticAt_h G (Λ.volume n) J β h

end Ambient
end IsingModel
