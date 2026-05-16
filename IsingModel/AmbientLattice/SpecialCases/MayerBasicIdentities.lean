import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesExpansionTerm
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesVdSum

/-!
# Mayer basic identity wrappers along an exhaustion

Narrow child module for along-exhaustion at-zero and at-one identities for
`vdPolymerFamilies_sum`, `mayerPartialSum`, and `mayerExpansionTerm`. This
keeps callers that only need these basic forwarders out of the monolithic
original special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 basic identities at_zero / at_one along-ex wraps -/

/-! ## Moved: 2 vdPolymerFamilies_sumAlongExhaustion at-zero / at-one identities

The two along-ex `vdPolymerFamilies_sumAlongExhaustion` evaluation
identities (`_at_zero`, `_at_one`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesVdSum`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerPartialSum_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSumAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerPartialSum_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 = 0 :=
  mayerPartialSum_Λ_at_zero G (Λ.volume n) N

/-! ## Moved: mayerExpansionTermAlongExhaustion basic identity wrappers

The three `mayerExpansionTermAlongExhaustion_*` basic identity wrappers
(`zero`, `one`, `at_zero`) now live in
`MayerBasicIdentitiesExpansionTerm.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



end Ambient
end IsingModel
