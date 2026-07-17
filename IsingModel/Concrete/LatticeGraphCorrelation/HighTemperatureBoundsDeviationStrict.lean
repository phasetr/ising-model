import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT Λ-layer strict-deviation wrappers

Narrow child module for the 8 ℤ^d Λ-layer strict-deviation HT
wrappers (`freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_pos`,
`_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt`,
`_ferromagnetic`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos`,
`_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle`,
`_ferromagnetic`) extracted from
`HighTemperatureBoundsDeviation.lean` in PR #2078. Each is a thin
pass-through to the corresponding ambient
`freeEnergyΛ_*` / `partitionFunctionΛ_*` / `log_partitionFunctionΛ_*`
strict-deviation lemma at `IsingModel.latticeGraph d`. The theorem
names are unchanged from the former `HighTemperatureBoundsDeviation`
declarations.
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

/-- **ℤ^d Λ Z + log Z + f strict deviation bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (hne : 0 < Λ.card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
        < partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    0 < Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 ∧
    0 < freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  partitionFunctionΛ_high_temp_expansion_h_zero_strict_deviation_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ hne hEpos

/-! ## Moved: HT Λ-layer ferromagnetic strict-deviation bundle/Z/logZ wrappers

The three ferromagnetic Λ-layer strict-deviation wrappers
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos_ferromagnetic`
now live in `HighTemperatureBoundsDeviationStrictFerro.lean`. -/


end Ambient

end IsingModel
