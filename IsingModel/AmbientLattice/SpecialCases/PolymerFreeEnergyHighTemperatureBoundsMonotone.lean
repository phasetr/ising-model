import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# `vdPolymerFamilies_sum` `MonotoneOn (Set.Ici 0)` wrapper along an exhaustion

Narrow child module for the §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero` wrapper
extracted from `PolymerFreeEnergyHighTemperatureBounds.lean`. The
wrapper is a thin pass-through to
`vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero`. The theorem name is
unchanged from the former
`PolymerFreeEnergyHighTemperatureBounds` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
