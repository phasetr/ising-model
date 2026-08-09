import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviationStrict

/-!
# ℤ^d fixed-volume ferromagnetic strict deviation for `Z_Λ` and `log Z_Λ`

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the strict inequalities `2 ^ |Λ| < Z_Λ` and `|Λ| * log 2 < log Z_Λ` in
their ferromagnetic form. Each assumes `0 < J` together with `0 < β`, strict in the coupling
as well as in the inverse temperature, and each requires the induced subgraph on `Λ` to carry
at least one edge; nonemptiness of `Λ` is not assumed.
-/

namespace IsingModel
namespace Ambient

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
