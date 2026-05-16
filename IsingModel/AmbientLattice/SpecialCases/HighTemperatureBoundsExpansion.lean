import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity

/-!
# Ambient alongExhaustion partition/free-energy expansion wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
partition function / free energy expansion / closed-form / lower-bound /
upper-bound / sandwich / complete-summary wrappers. 20 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, `correlationAlongExhaustion`
closed forms, plus `one_le_sum_pow_tanh_even_subgraph_alongExhaustion`
helper. The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: alongExhaustion expansion lower/upper-bound wrappers

The 8 ambient alongExhaustion partition function / free energy /
log partition function high-temperature expansion lower-bound,
upper-bound, closed-form, and lower_le_upper consistency wrappers
(`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`,
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound`,
`partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper`,
`freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper`,
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound`,
`freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed`,
`freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound`,
`freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/

/-! ## Moved: expansion variant + one_le_sum helper

The 4 ambient alongExhaustion `_high_temp_expansion_h_zero` /
`_high_temp_expansion` / `_high_temp_expansion_subset_form` and
`one_le_sum_pow_tanh_even_subgraph_alongExhaustion` wrappers now
live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/


/-! ## Moved: closed-form / sandwich / complete-summary wrappers

The 8 ambient alongExhaustion closed-form / sandwich /
complete-summary wrappers (`*_closed_at_J_zero`,
`*_closed_at_beta_zero`, redundant `*_closed`,
`correlationAlongExhaustion_*_nonneg`, `_closed`,
`*_sandwich`, `*_complete_summary`, freeEnergy
complete_summary) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedForms`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/

end Ambient

end IsingModel
