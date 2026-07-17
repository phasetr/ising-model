import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete §18.3-§18.4 Λ-direct sharper-exp ferromagnetic complete-summary wrappers

Narrow child module for 3 ℤ^d Λ-direct ferromagnetic sharper-exp
`complete_summary_exp` wrappers extracted from
`HighTemperatureBoundsExpSharperCompleteSummary.lean`:

* `partitionFunctionΛ_*_complete_summary_exp_ferromagnetic`,
* `log_partitionFunctionΛ_*_complete_summary_exp_ferromagnetic`,
* `freeEnergyΛ_*_complete_summary_exp_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`*Λ_high_temp_*_complete_summary_exp_ferromagnetic` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsExpSharperCompleteSummary`
declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ ferromagnetic Z/logZ/f complete-summary exp bundles**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic log Z complete-summary exp bundle**. -/
theorem
log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)) = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ)) = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic f complete-summary exp bundle**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
