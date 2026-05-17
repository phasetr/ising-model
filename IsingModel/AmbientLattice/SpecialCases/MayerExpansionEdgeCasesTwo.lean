import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwoPartialSum

/-!
# Mayer expansion-term `n = 2` wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion Mayer
expansion-term `n = 2` wrappers extracted from
`MayerExpansionEdgeCases.lean`:

* `mayerExpansionTermAlongExhaustion_two`
* `mayerExpansionTermAlongExhaustion_two_filter`

The corresponding partial-sum wrapper (`mayerPartialSumAlongExhaustion_two`)
now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwoPartialSum`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding `mayer*_Λ_two*` ambient
lemma. Theorem names are unchanged from the former
`MayerExpansionEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTermAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph G (Λ.volume n))) ×ˢ
              (IsingModel.allPolymers (inducedGraph G (Λ.volume n))),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTermAlongExhaustion_two_filter
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n))) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n)))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two_filter G (Λ.volume n) t

/-! ## Moved: 1 mayerPartialSum_two wrapper

The `mayerPartialSumAlongExhaustion_two` wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwoPartialSum`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
