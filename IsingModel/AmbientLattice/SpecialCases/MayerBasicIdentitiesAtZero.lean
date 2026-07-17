import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Mayer `mayerPartialSum` at `t = 0` wrapper along an exhaustion

Narrow child module for the along-exhaustion
`mayerPartialSumAlongExhaustion_at_zero` wrapper (`t = 0`)
extracted from `MayerBasicIdentities.lean`. The wrapper is a thin
pass-through to `mayerPartialSum_Λ_at_zero`. The theorem name is
unchanged from the former `MayerBasicIdentities` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 = 0 :=
  mayerPartialSum_Λ_at_zero G (Λ.volume n) N

end Ambient
end IsingModel
