import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Polymer free-energy ferromagnetic tanh sandwich wrapper along an exhaustion

Narrow child module for the §18.5 ambient alongExhaustion
ferromagnetic `polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro`
wrapper extracted from `PolymerFreeEnergyTanhBoundsFerro.lean`. The
wrapper is a thin pass-through to
`polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic`. The theorem
name is unchanged from the former `PolymerFreeEnergyTanhBounds`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
