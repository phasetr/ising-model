import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# Regularity of the polymer free energy on the nonnegative activity ray

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

As a function of the activity, the polymer free energy of the stage subgraph is continuous on
`Set.Ici 0` and differentiable over `ℝ` on `Set.Ici 0`.
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
