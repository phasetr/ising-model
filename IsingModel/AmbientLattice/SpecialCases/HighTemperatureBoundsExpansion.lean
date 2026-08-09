import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity

/-!
# An import node of the zero-field high-temperature expansion layer

This module states nothing of its own. What it makes available is what
`IsingModel.AmbientLattice.SpecialCases.FreeEnergy` and
`IsingModel.AmbientLattice.Analyticity` make available, and modules of the along-exhaustion
zero-field high-temperature expansion layer reach that surface through this name.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

end Ambient

end IsingModel
