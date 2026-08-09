import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases

/-!
# ℤ^d Mayer identity edge cases, assembled

Carries no declaration of its own. It makes available, behind a single import, the
`IsingModel.latticeGraph` definition together with the graph-generic along-exhaustion results
proved in the modules it imports: the Mayer identity at the trivial parameter slices, and the
agreement of `polymerFreeEnergy` with `mayerPartialSum` at those slices.
-/

namespace IsingModel
namespace Ambient

open Finset Real

end Ambient
end IsingModel
