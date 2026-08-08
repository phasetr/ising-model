import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictZ

/-!
# Ambient alongExhaustion strict-deviation wrappers at h = 0

Turns the GJ §18.3–§18.4 high-temperature expansion into strict deviation statements for the
zero-field partition function and free energy along an exhaustion, which is what separates
the expansion from its trivial slice.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
          (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) / _ ∧ partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) / _ ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    G (Λ.volume n) J β hβJ

/-- **Along-ex f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 := by
  change 0 < freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
  exact freeEnergyΛ_high_temp_h_zero_deviation_pos
    G (Λ.volume n) J β hβJ hne hEpos

end Ambient

end IsingModel
