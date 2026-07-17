import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# `polymerFreeEnergyAlongExhaustion = mayerPartialSum` trivial-slice wrappers

Narrow child module for the two ambient
`polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_*_zero`
trivial-slice wrappers extracted from
`MayerEdgeCasesPolymerFreeEnergy.lean`:

* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_beta_zero`
* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_J_zero`

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_eq_mayerPartialSum_at_*_zero` lemma. Theorem
names are unchanged from the former `MayerEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    G (Λ.volume n) J N

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    G (Λ.volume n) β N

end Ambient
end IsingModel
