import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwo
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesAbsLe

/-!
# Mayer expansion edge-case wrappers along an exhaustion

Narrow child module for along-exhaustion Mayer expansion `n = 2`, no-polymer,
edgeless, and absolute-bound wrappers. This keeps callers that only need these
forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer expansion edge-cases + abs_le along-ex -/

/-! ## Moved: mayer expansion `_two` wrappers

The three `mayer*AlongExhaustion_two*` wrappers (`_two`,
`_two_filter`, `mayerPartialSumAlongExhaustion_two`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwo`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t N

/-- **Along-ex: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t N

/-! ## Moved: 1 mayerExpansionTerm abs_le wrapper

The `mayerExpansionTermAlongExhaustion_abs_le` wrapper now lives
in
`IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesAbsLe`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
