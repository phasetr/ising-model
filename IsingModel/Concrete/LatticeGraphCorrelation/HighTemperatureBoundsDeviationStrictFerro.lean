import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviationStrict

/-!
# ℤ^d HT Λ-layer strict-deviation ferromagnetic bundle/Z/logZ wrappers

Narrow child module for three ℤ^d Λ-layer strict-deviation HT
ferromagnetic wrappers extracted from
`HighTemperatureBoundsDeviationStrict.lean`:

* the Z + log Z + f bundle wrapper (`*_strict_deviation_bundle_ferromagnetic`),
* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic`,
* `log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`*_ferromagnetic` strict-deviation lemma at `IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`HighTemperatureBoundsDeviationStrict` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ ferromagnetic Z + log Z + f strict deviation bundle**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
        < partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    0 < Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 ∧
    0 < freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle
    d Λ J β (mul_pos hβ hJ) hne hEpos

/-- **ℤ^d Λ ferromagnetic Z strict deviation**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hEpos

/-- **ℤ^d Λ ferromagnetic log Z strict deviation**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hEpos

end Ambient

end IsingModel
