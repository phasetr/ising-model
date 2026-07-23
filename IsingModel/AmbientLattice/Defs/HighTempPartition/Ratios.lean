import IsingModel.AmbientLattice.Defs.HighTempPartition.Deviation

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level Z ratio sandwich at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level Z ratio sandwich at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G Λ J β hβJ⟩

/-- **Λ-level ferromagnetic Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level Z ratio bound at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  (partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ).2

/-- **Λ-level Z ratio bound at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  (partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G Λ J β hβJ).2

/-- **Λ-level ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic Z ratio upper bound at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level log Z ratio sandwich bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply,
      partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic log Z ratio sandwich bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level log Z ratio bound at J=0**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level log Z ratio bound at β=0**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, partitionFunctionΛ_apply]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level f ratio sandwich bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, freeEnergyΛ_apply,
      ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level ferromagnetic f ratio sandwich bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level f ratio bound at J=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_bound
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f ratio bound at β=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    (inducedGraph G Λ) J β hβJ hcard

end Ambient

end IsingModel
