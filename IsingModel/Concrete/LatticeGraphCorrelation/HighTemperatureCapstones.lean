import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Concrete high-temperature capstone wrappers

Narrow child module for the §18.4-§18.6 high-temperature
partition-function/free-energy capstone wrappers on the concrete lattice
graph. The theorem names are the same as the former declarations, but
callers can now avoid importing the monolithic concrete module.
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

/-! ## Moved: Λ-direct freeEnergyΛ HT capstone wrappers

The three Λ-direct `freeEnergyΛ_latticeGraph_*` capstone wrappers
(`_eq_polymerFreeEnergy`, `_eq_polymerFreeEnergy_ferromagnetic`,
`_eq_log_two_at_betaJ_zero`) now live in
`HighTemperatureCapstonesFreeEnergy.lean`. -/



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
