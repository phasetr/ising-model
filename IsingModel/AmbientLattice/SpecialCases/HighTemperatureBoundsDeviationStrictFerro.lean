import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict

/-!
# Ambient alongExhaustion ferromagnetic strict-deviation wrappers at h = 0

Narrow child module for the four §18.3-§18.4 ambient alongExhaustion
ferromagnetic strict-deviation wrappers
(`_relative_sandwich_ferromagnetic`, `_deviation_pos_ferromagnetic`,
`_pow_two_lt_ferromagnetic`, `log_*_deviation_pos_ferromagnetic`).
Theorem names are unchanged from the former
`HighTemperatureBoundsDeviationStrict` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
          (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) n hne hEpos

/-! ## Moved: strict-deviation bundle wrapper

The `Z + log Z + f` strict-deviation bundle wrapper
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle`)
now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerroBundle`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: 2 ferromagnetic Z / log Z strict-deviation wrappers

The two ferromagnetic Z / log Z strict-deviation wrappers
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic`,
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerroZ`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient

end IsingModel
