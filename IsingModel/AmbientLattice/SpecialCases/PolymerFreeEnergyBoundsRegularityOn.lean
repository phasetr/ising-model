import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# Ambient polymerFreeEnergyAlongExhaustion `_On` (Set.Ici 0) regularity wrappers

Narrow child module for the two ambient
`polymerFreeEnergyAlongExhaustion_*On_Ici_zero` regularity wrappers
extracted from `PolymerFreeEnergyBoundsRegularity.lean`:

* `polymerFreeEnergyAlongExhaustion_continuousOn_Ici_zero`
* `polymerFreeEnergyAlongExhaustion_differentiableOn_Ici_zero`

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_{continuousOn_Ici_zero,differentiableOn_Ici_zero}`
lemma. Theorem names are unchanged from the former
`PolymerFreeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: `polymerFreeEnergy` is
`ContinuousOn (Set.Ici 0)`** (§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_continuousOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ContinuousOn (fun s : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) s) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_continuousOn_Ici_zero G (Λ.volume n)

/-- **Along-exhaustion: `polymerFreeEnergy` is
`DifferentiableOn (Set.Ici 0)`** (§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_differentiableOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    DifferentiableOn ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) s) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_differentiableOn_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
