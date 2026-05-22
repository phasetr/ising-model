import IsingModel.AmbientLattice.Defs.HighTempPartition.ExpBounds

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level sharper f complete-summary exp bundle**: under `0 < |Λ|`,
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values at the Λ-layer. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  obtain ⟨h1, h2⟩ := freeEnergyΛ_high_temp_h_zero_sandwich_exp
    G Λ J β hβJ hne
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [freeEnergyΛ_apply]
    have := IsingModel.freeEnergy_J_zero (inducedGraph G Λ) (0 : ℝ) β hcard
    simpa [mul_zero, Real.cosh_zero] using this
  · rw [freeEnergyΛ_apply]
    exact IsingModel.freeEnergy_beta_zero (inducedGraph G Λ) J 0 hcard

/-- **Λ-level sharper Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card := by
  obtain ⟨h1, h2⟩ := partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  exact ⟨h1, h2,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero G Λ β,
    partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero G Λ J⟩

/-- **Λ-level sharper log Z complete-summary exp bundle**: under
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 := by
  obtain ⟨h1, h2⟩ := log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G Λ J β hβJ
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero,
        Real.log_pow]
  · rw [partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero,
        Real.log_pow]

/-- **Λ-level ferromagnetic Z complete-summary exp bundle**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic log Z complete-summary exp bundle**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J * (inducedGraph G Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level ferromagnetic f complete-summary exp bundle**. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card ∧
    freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
