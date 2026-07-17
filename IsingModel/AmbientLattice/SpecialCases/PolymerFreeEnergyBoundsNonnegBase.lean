import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Ambient polymerFreeEnergyAlongExhaustion `≥ 0` base wrapper

Narrow child module for the ambient
`polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg` base lower
bound wrapper extracted from `PolymerFreeEnergyBoundsNonneg.lean`.
The wrapper is a thin pass-through to
`polymerFreeEnergy_Λ_nonneg_of_nonneg`. The theorem name is
unchanged from the former `PolymerFreeEnergyBounds` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy ≥ 0` under `t ≥ 0`** (§18.5
along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  polymerFreeEnergy_Λ_nonneg_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
