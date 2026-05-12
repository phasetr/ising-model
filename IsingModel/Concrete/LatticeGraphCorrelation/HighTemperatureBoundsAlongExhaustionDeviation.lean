import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExDeviationContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExDeviationSandwich
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRelativeSandwich
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExDeviationPos
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExStrictDeviation

/-!
# Concrete alongExhaustion f/Z/log Z deviation / continuity wrappers at h = 0

Backwards-compatibility shim for the §18.3-§18.4 concrete
alongExhaustion deviation / continuity family on `latticeGraph d` at
`h = 0`. All eighteen wrappers that used to live here have been carved
out into narrower children
(`HighTemperatureBoundsAlongExDeviationContinuity`,
`HighTemperatureBoundsAlongExDeviationSandwich`,
`HighTemperatureBoundsAlongExRelativeSandwich`,
`HighTemperatureBoundsAlongExDeviationPos`, and
`HighTemperatureBoundsAlongExStrictDeviation`). This file now contains
only Moved doc blocks pointing at those children. The theorem names
are unchanged from the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-! ## Moved: alongExhaustion `deviation_bound_exp` + `continuity_bundle` wrappers

The four wrappers
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp_ferromagnetic`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_continuity_bundle`, and
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_continuity_bundle_ferromagnetic`
now live in `HighTemperatureBoundsAlongExDeviationContinuity.lean`. -/


/-! ## Moved: alongExhaustion `deviation_sandwich` wrappers

The four wrappers `freeEnergyAlongExhaustion_latticeGraph_*_deviation_sandwich`
and `log_partitionFunctionAlongExhaustion_latticeGraph_*_deviation_sandwich`
(each with a ferromagnetic variant) now live in
`HighTemperatureBoundsAlongExDeviationSandwich.lean`. -/


/-! ## Moved: alongExhaustion Z `relative_sandwich` wrappers

The two wrappers
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_relative_sandwich`
and `partitionFunctionAlongExhaustion_latticeGraph_h_zero_relative_sandwich_ferromagnetic`
now live in `HighTemperatureBoundsAlongExRelativeSandwich.lean`. -/

/-! ## Moved: alongExhaustion `deviation_pos` / `pow_two_lt` wrappers

The four wrappers
`freeEnergyAlongExhaustion_latticeGraph_*_deviation_pos`,
`partitionFunctionAlongExhaustion_latticeGraph_*_pow_two_lt`, and
`log_partitionFunctionAlongExhaustion_latticeGraph_*_deviation_pos`
now live in `HighTemperatureBoundsAlongExDeviationPos.lean`. -/

/-! ## Moved: alongExhaustion `strict_deviation_bundle` + residual ferromagnetic wrappers

The two `strict_deviation_bundle` wrappers (general and ferromagnetic),
`partitionFunctionAlongExhaustion_*_pow_two_lt_ferromagnetic`, and
`log_partitionFunctionAlongExhaustion_*_deviation_pos_ferromagnetic`
now live in `HighTemperatureBoundsAlongExStrictDeviation.lean`. -/



end Ambient

end IsingModel
