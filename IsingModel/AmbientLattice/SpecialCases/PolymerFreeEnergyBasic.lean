import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasicSandwich

/-!
# Basic polymer free-energy at-zero / at-one wrappers along an exhaustion

Narrow child module for the two along-exhaustion `polymerFreeEnergy`
trivial-slice wrappers (`_at_zero`, `_at_one`). The corresponding
nonnegative sandwich wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasicSandwich`
and is re-imported through this parent module. Theorem names are
unchanged from the former monolithic special-cases declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + sandwich along-ex -/

/-- **Along-ex: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergyAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) 0 = 0 :=
  polymerFreeEnergy_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergyAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  polymerFreeEnergy_Λ_at_one G (Λ.volume n)

/-! ## Moved: 1 polymerFreeEnergy sandwich wrapper

The `polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasicSandwich`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
