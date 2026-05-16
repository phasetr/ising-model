import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Ambient alongExhaustion sharper-exp Z/f/log Z wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
sharper-exp upper-bound / sandwich / complete-summary wrappers. 16
theorems for `partitionFunctionAlongExhaustion`,
`freeEnergyAlongExhaustion`, and `log_partitionFunctionAlongExhaustion`
high-temperature wrappers with `_exp` suffix at `h = 0` plus
ferromagnetic variants. The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-- **Along-ex sharper Z upper bound at stage `n`**: under `0 ≤ β·J`,
`Z_n(⟨J, 0, β⟩) ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. Stage-`n` Λ-level
specialization of
`partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) ≤ _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

/-- **Along-ex sharper log Z upper bound at stage `n`**: under
`0 ≤ β·J`, `log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. Stage-`n` Λ-level
specialization of
`log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    G (Λ.volume n) J β hβJ

/-! ## Moved: sharper-exp sandwich wrappers

The 5 ambient alongExhaustion sharper-exp `_sandwich_exp` wrappers
(`log_partitionFunctionAlongExhaustion_*_sandwich_exp`,
`partitionFunctionAlongExhaustion_*_sandwich_exp`,
`freeEnergyAlongExhaustion_*_sandwich_exp`, plus ferromagnetic
variants for Z and f) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/


/-! ## Moved: ferromagnetic upper-bound exp wrappers

The three `*AlongExhaustion_high_temp_*_h_zero_upper_bound_exp_ferromagnetic`
wrappers (for `partitionFunction`, `log_partitionFunction`,
`freeEnergy`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperFerro`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

/-! ## Moved: complete_summary_exp wrappers

The 6 ambient alongExhaustion `complete_summary_exp` wrappers
(`freeEnergyAlongExhaustion`, `partitionFunctionAlongExhaustion`,
`log_partitionFunctionAlongExhaustion` with ferromagnetic variants)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperComplete`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel
