import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictZ

/-!
# Ambient alongExhaustion strict-deviation wrappers at h = 0

Narrow child module for 10 §18.3-§18.4 ambient alongExhaustion strict-
deviation wrappers covering `partitionFunctionAlongExhaustion_*_relative_sandwich`
+ ferromagnetic variant, `freeEnergyAlongExhaustion_*_deviation_pos` +
ferromagnetic, `partitionFunctionAlongExhaustion_*_pow_two_lt` +
ferromagnetic, `log_partitionFunctionAlongExhaustion_*_deviation_pos` +
ferromagnetic, and `_strict_deviation_bundle`. Theorem names are
unchanged from the former `HighTemperatureBoundsDeviation`
declarations.
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

/-! ## Moved: 2 Z / log Z strict-deviation wrappers

The two Z and log Z strict-deviation wrappers
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt`,
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictZ`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-! ## Moved: ferromagnetic + strict-deviation bundle wrappers

The four ferromagnetic strict-deviation wrappers
(`_relative_sandwich_ferromagnetic`, `_deviation_pos_ferromagnetic`,
`_pow_two_lt_ferromagnetic`, `log_*_deviation_pos_ferromagnetic`)
and the two strict-deviation bundles (`_strict_deviation_bundle`,
`_strict_deviation_bundle_ferromagnetic`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

end Ambient

end IsingModel
