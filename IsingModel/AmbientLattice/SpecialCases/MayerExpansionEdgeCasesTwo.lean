import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwoPartialSum

/-!
# The order-2 Mayer expansion term, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At every real activity `t`, the order-`2` Mayer expansion term of the stage subgraph is
written over the product of that subgraph's polymer universe with itself: once with the
summand carrying the coefficient `-1/2` on incompatible pairs and `0` elsewhere, and once as
`-1/2` times the sum restricted by `Finset.filter` to the incompatible pairs.
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

end Ambient
end IsingModel
