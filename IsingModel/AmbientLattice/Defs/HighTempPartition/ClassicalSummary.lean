import IsingModel.AmbientLattice.Defs.HighTempPartition.TripleRatios

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level Z high-temp sandwich (FV (3.45))**: under `0 ≤ β·J`,
`2^|Λ| · cosh^|E_Λ| ≤ Z_Λ ≤ 2^(|Λ|+|E_Λ|) · cosh^|E_Λ|`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
          Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound G Λ J β hβJ⟩

/-- **Λ-level Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
single statement bundling Λ-level Z lower bound, upper bound, and
trivial-slice values at `J = 0` / `β = 0`. Λ-layer wrapper of
`partitionFunction_high_temp_expansion_h_zero_complete_summary`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ (2 : ℝ) ^ (Λ.card + (inducedGraph G Λ).edgeFinset.card) *
            Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card ∧
      partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Λ.card ∧
      partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Λ.card :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound G Λ J β hβJ,
   partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero G Λ β,
   partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero G Λ J⟩

/-- **Λ-level freeEnergy complete-summary bundle at h = 0**: under
`0 < |Λ|` and `0 ≤ β·J`, single statement bundling Λ-level lower /
upper bounds and trivial-slice values at `J = 0` / `β = 0` (both =
`log 2`). Λ-layer wrapper of
`freeEnergy_high_temp_h_zero_complete_summary`. -/
theorem freeEnergyΛ_high_temp_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 +
            ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
              Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  ⟨freeEnergyΛ_high_temp_h_zero_lower_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_upper_bound G Λ J β hβJ hne,
   by
     have := IsingModel.freeEnergy_J_zero (inducedGraph G Λ) (0 : ℝ) β hcard
     simpa [freeEnergyΛ, mul_zero, Real.cosh_zero] using this,
   by
     have := IsingModel.freeEnergy_beta_zero (inducedGraph G Λ) J 0 hcard
     simpa [freeEnergyΛ] using this⟩

/-- **Λ-level freeEnergy high-temp sandwich (FV (3.45))**: under
`0 < |Λ|` and `0 ≤ β·J`,
`log 2 + (|E_Λ|/|Λ|) log cosh(βJ) ≤ f_Λ ≤ log 2 + (|E_Λ|/|Λ|) log(2·cosh βJ)`. -/
theorem freeEnergyΛ_high_temp_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
            Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergyΛ_high_temp_h_zero_lower_bound G Λ J β hβJ hne,
   freeEnergyΛ_high_temp_h_zero_upper_bound G Λ J β hβJ hne⟩

end Ambient

end IsingModel
