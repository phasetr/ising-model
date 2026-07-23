import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioSandwichBundle
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundSlices
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundBundle

/-!
# Concrete alongExhaustion Z ratio sandwich and ratio bound wrappers at h = 0

Backwards-compatibility shim. All eight ℤ^d alongExhaustion
`partitionFunctionAlongExhaustion_latticeGraph_*` Z ratio wrappers
that used to live here have been carved out into three narrower
children:
`HighTemperatureBoundsAlongExRatioSandwichBundle.lean` (PR #2089) for
the two `ratio_sandwich_bundle` wrappers;
`HighTemperatureBoundsAlongExRatioBoundSlices.lean` (PR #2090) for the
four J = 0 / β = 0 `ratio_bound` slice wrappers; and
`HighTemperatureBoundsAlongExRatioBoundBundle.lean` (PR #2091) for the
two `ratio_bound_bundle` wrappers. The 7 `triple_ratio_*` wrappers
live in `HighTemperatureBoundsAlongExhaustionTripleRatio.lean` (PR
#1996) and the 14 `log_partitionFunction` / `freeEnergy` ratio
wrappers live in `HighTemperatureBoundsAlongExhaustionRatioLogFe.lean`
(PR #1997). The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-! ## Moved: alongExhaustion Z `ratio_sandwich_bundle` wrappers

The two wrappers
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle`
and `partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_sandwich_bundle_ferromagnetic`
now live in `HighTemperatureBoundsAlongExRatioSandwichBundle.lean`. -/


/-! ## Moved: alongExhaustion Z `ratio_bound` J = 0 / β = 0 slice wrappers

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_*_ratio_bound`,
`*_ratio_bound_beta_zero`, `*_ratio_bound_ferromagnetic`, and
`*_ratio_bound_beta_zero_ferromagnetic` now live in
`HighTemperatureBoundsAlongExRatioBoundSlices.lean`. -/


/-! ## Moved: alongExhaustion Z `ratio_bound_bundle` wrappers

The two wrappers
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle`
and `partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_bound_bundle_ferromagnetic`
now live in `HighTemperatureBoundsAlongExRatioBoundBundle.lean`. -/

/-! ## Moved: ℤ^d log Z + freeEnergy ratio wrappers

The 14 ℤ^d alongExhaustion `log_partitionFunction` and `freeEnergy`
ratio_sandwich / ratio_bound (+ deviation_pos / pow_two_lt) wrappers
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioLogFe`.
The umbrella `HighTemperatureBounds.lean` re-imports
the new child so the import paths and theorem names remain
unchanged.
-/

/-! ## Moved: ℤ^d alongExhaustion triple-ratio wrappers

The 4 ℤ^d alongExhaustion `triple_ratio_sandwich_bundle` wrappers
(J = 0 / β = 0 trivial slices, ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionTripleRatio`.
The earlier import path is preserved by re-exporting the new child
from the umbrella module that aggregates it.
-/


end Ambient

end IsingModel
