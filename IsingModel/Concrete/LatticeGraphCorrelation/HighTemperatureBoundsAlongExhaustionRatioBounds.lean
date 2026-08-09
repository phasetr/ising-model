import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioSandwichBundle
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundSlices
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundBundle

/-!
# ℤ^d along-exhaustion partition-function ratio family, assembled

Aggregates, for callers that want the family behind a single import, the ℤ^d along-exhaustion
zero-field partition-function ratio results proved in the modules it imports: the sandwich
bundle placing the ratios against the `J = 0` and `β = 0` parameter records between
`cosh (β * J) ^ |E_n|` and `exp (β * J * |E_n|)`, those ratios' separate upper bounds, and the
bundle collecting the upper bounds.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

end Ambient

end IsingModel
