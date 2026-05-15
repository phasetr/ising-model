import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient polymerFreeEnergyAlongExhaustion = mayerPartialSum edge-case wrappers

Narrow child module for 4 ambient
`polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_*` wrappers
extracted from `MayerEdgeCases.lean`:

* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_zero`,
* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_betaJ_zero`,
* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_beta_zero`,
* `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_J_zero`.

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_eq_mayerPartialSum_at_*` lemma. The theorem
names are unchanged from the former `MayerEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case along-ex wraps -/

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at t = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) 0 =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero G (Λ.volume n) N

/-- **Along-ex: polymerFreeEnergy = mayerPartialSum at β·J = 0**. -/
theorem polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    G (Λ.volume n) hβJ N

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
