import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases

/-!
# Concrete Mayer edge-case wrappers

Narrow child module for concrete `ℤ^d` Mayer identity edge cases and
`polymerFreeEnergy = mayerPartialSum` forwarders. This keeps callers that only
need these wrappers out of the monolithic lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ## Moved: Λ-direct Mayer identity edge-case wrappers

The four wrappers
`mayer_identity_at_zero_Λ_latticeGraph`,
`mayer_identity_at_betaJ_zero_Λ_latticeGraph`,
`mayer_identity_at_beta_zero_Λ_latticeGraph`,
`mayer_identity_at_J_zero_Λ_latticeGraph` now live in
`MayerEdgeCasesLambda.lean`. -/


/-! ## Moved: along-ex Mayer identity edge-case wrappers

The four wrappers
`mayer_identity_at_{zero,betaJ_zero,beta_zero,J_zero}_AlongExhaustion_latticeGraph`
now live in `MayerEdgeCasesAlongExIdentity.lean`. -/


/-! ## Moved: Λ polymerFreeEnergy = mayerPartialSum edge cases

The four wrappers
`polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_{zero,betaJ_zero,beta_zero,J_zero}`
now live in `MayerEdgeCasesLambdaPolymer.lean`. -/

/-! ## Moved: along-ex polymerFreeEnergy = mayerPartialSum edge cases

The four
`polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at`
wrappers (`{_zero, _betaJ_zero, _beta_zero, _J_zero}`) now live in
`MayerEdgeCasesAlongExPolymer.lean`. -/


/-! ## Moved: `mayer_identity_*_polymer_free_energy_*` edge cases

The six wrappers
`mayer_identity_at_{J,beta,either}_zero_polymer_free_energy_{Λ,AlongExhaustion}_latticeGraph`
now live in `MayerEdgeCasesPolymerFreeEnergy.lean`. -/

end Ambient
end IsingModel
