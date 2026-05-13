import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones

/-!
# Concrete high-temperature capstone wrappers

Narrow child module for the §18.4-§18.6 high-temperature
partition-function/free-energy capstone wrappers on the concrete lattice
graph. The theorem names are the same as the former legacy declarations, but
callers can now avoid importing the monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-! ### §18.4-§18.6 capstones ℤ^d wraps -/

/-- **ℤ^d Λ: §18.4 partitionFunction polymer-family form**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_polymer_family
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: §18.4 partitionFunction even-subgraph form**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_evenSubgraphs
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs
                (inducedGraph (IsingModel.latticeGraph d) Λ),
          Real.tanh (β * J) ^ X.card :=
  Ambient.partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: §18.6 freeEnergy decomposition**. -/
theorem freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyΛ_eq_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ: freeEnergy = log 2 at `β·J = 0`**. -/
theorem freeEnergyΛ_latticeGraph_eq_log_two_at_betaJ_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 :=
  Ambient.freeEnergyΛ_eq_log_two_at_betaJ_zero
    (IsingModel.latticeGraph d) Λ hβJ hne

/-- **ℤ^d Λ: mayerPartialSum at N=1, t=1**. -/
theorem mayerPartialSum_Λ_latticeGraph_one_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 1 =
      (IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.mayerPartialSum_Λ_one_at_one (IsingModel.latticeGraph d) Λ

/-! ## Moved: AlongExhaustion high-temperature capstone wrappers

The six AlongExhaustion `partitionFunctionAlongExhaustion_latticeGraph_*`,
`freeEnergyAlongExhaustion_latticeGraph_*`, and
`mayerPartialSumAlongExhaustion_latticeGraph_one_at_one` wrappers now
live in `HighTemperatureCapstonesAlongEx.lean`. -/



end Ambient
end IsingModel
