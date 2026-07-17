import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Mayer partial-sum at `N = 2` wrapper along an exhaustion

Narrow child module for the §18.5 along-exhaustion
`mayerPartialSumAlongExhaustion_two` wrapper extracted from
`MayerExpansionEdgeCasesTwo.lean`. The wrapper is a thin
pass-through to the corresponding `mayerPartialSum_Λ_two` ambient
lemma. The theorem name is unchanged from the former
`MayerExpansionEdgeCases` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSumAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G (Λ.volume n)),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n))) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n)))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerPartialSum_Λ_two G (Λ.volume n) t

end Ambient
end IsingModel
