import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosed
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Ambient alongExhaustion sandwich / complete-summary wrappers at h = 0

Packages the GJ §18.3–§18.4 high-temperature expansion into two-sided sandwich and
complete-summary statements for the zero-field partition function and free energy along an
exhaustion, which is the form the §18.7 decay argument consumes.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion Z high-temp sandwich (FV (3.45))**: under
`0 ≤ β·J`, at every stage `n`,
`2^|Λ_n| · cosh^|E_n| ≤ Z_n ≤ 2^(|Λ_n|+|E_n|) · cosh^|E_n|`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph G (Λ.volume n)).edgeFinset.card) *
          Real.cosh (β * J) ^
              (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound
      G Λ J β hβJ n⟩

/-- **Along-ex Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
at every stage `n` packages along-exhaustion Z lower bound, upper bound,
and trivial-slice values at `J = 0` / `β = 0`. Along-exhaustion wrapper
of `partitionFunction_high_temp_expansion_h_zero_complete_summary`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ (2 : ℝ) ^ ((Λ.volume n).card +
              (inducedGraph G (Λ.volume n)).edgeFinset.card) *
            Real.cosh (β * J) ^
              (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
      partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        = (2 : ℝ) ^ (Λ.volume n).card ∧
      partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        = (2 : ℝ) ^ (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
      G Λ β n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
      G Λ J n⟩

/-- **Along-ex freeEnergy complete-summary bundle at h = 0**: under
`0 ≤ β·J` and `(Λ.volume n).Nonempty`, at every stage `n` packages
along-exhaustion freeEnergy lower bound, upper bound, and trivial-slice
values at `J = 0` / `β = 0` (both = `log 2`). Along-exhaustion wrapper
of `freeEnergy_high_temp_h_zero_complete_summary`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.log 2 +
            ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
              (Λ.volume n).card *
                Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  have hcard : 0 < (Λ.volume n).card := hne.card_pos
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound G Λ J β hβJ n hcard,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound G Λ J β hβJ n hcard,
   freeEnergyAlongExhaustion_zero_params G Λ β n hne,
   freeEnergyAlongExhaustion_beta_zero G Λ J 0 n hne⟩


end Ambient

end IsingModel
