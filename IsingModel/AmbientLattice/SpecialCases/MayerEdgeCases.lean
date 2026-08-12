import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# The Mayer identity at the zero-activity parameter slices, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At an activity forced to `0` -- written as the literal `0`, or as `Real.tanh (β * J)` under
`β * J = 0`, at `β = 0`, at `J = 0`, or at `β` and `J` both zero -- the logarithm of the
vertex-disjoint compatible polymer-family sum of the stage subgraph agrees with the Mayer
partial sum truncated at any order `N`. The same identity is also written with its left-hand
side as `IsingModel.polymerFreeEnergy`, which is that logarithm by definition.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: Mayer identity at `t = 0`**. -/
theorem mayer_identity_at_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 :=
  mayer_identity_at_zero_Λ G (Λ.volume n) N

/-- **Along-ex: Mayer identity at `β·J = 0`**. -/
theorem mayer_identity_at_betaJ_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_at_betaJ_zero_Λ G (Λ.volume n) hβJ N

/-- **Along-ex: Mayer identity at `β = 0`**. -/
theorem mayer_identity_at_beta_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_beta_zero_Λ G (Λ.volume n) J N

/-- **Along-ex: Mayer identity at `J = 0`**. -/
theorem mayer_identity_at_J_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_J_zero_Λ G (Λ.volume n) β N

/-- **Along-ex: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  mayer_identity_at_either_zero_polymer_free_energy_Λ G (Λ.volume n) N

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
