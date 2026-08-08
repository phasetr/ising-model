import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT Λ-layer strict-deviation wrappers

Instantiates the Λ-level strict-deviation statements of GJ §18.3–§18.4 at
`IsingModel.latticeGraph d` for the free energy, the partition function and its logarithm,
so ℤ^d arguments can separate the high-temperature expansion from its trivial slice.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ f strict deviation**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (hne : 0 < Λ.card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    0 < freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_deviation_pos
    (IsingModel.latticeGraph d) Λ J β hβJ hne hEpos

/-- **ℤ^d Λ ferromagnetic f strict deviation**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_pos_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    0 < freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_deviation_pos_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne hEpos

/-- **ℤ^d Λ Z strict deviation**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    (IsingModel.latticeGraph d) Λ J β hβJ hEpos

/-- **ℤ^d Λ log Z strict deviation**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    (IsingModel.latticeGraph d) Λ J β hβJ hEpos

end Ambient

end IsingModel
