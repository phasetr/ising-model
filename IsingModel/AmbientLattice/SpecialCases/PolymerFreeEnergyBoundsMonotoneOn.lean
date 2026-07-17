import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Ambient polymerFreeEnergyAlongExhaustion `MonotoneOn (Set.Ici 0)` wrapper

Narrow child module for the along-exhaustion
`polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero` wrapper
extracted from `PolymerFreeEnergyBounds.lean`. The wrapper is a
thin pass-through to `polymerFreeEnergy_Λ_monotoneOn_Ici_zero`. The
theorem name is unchanged from the former `PolymerFreeEnergyBounds`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) t) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_monotoneOn_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
