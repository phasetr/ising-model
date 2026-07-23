import IsingModel.AmbientLattice.Defs.HighTempPartition.Ratios

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level triple (Z + log Z + f) ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).1,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).1⟩

/-- **Λ-level triple ratio sandwich bundle at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).2,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).2⟩

/-- **Λ-level ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
