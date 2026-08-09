import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# The Mayer partial sum at truncation order 2, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At every real activity `t`, the Mayer partial sum of the stage subgraph truncated at order
`2` is the total polymer activity `∑ P, t ^ P.card` plus `-1/2` times the sum of
`t ^ p.card * t ^ q.card` over the ordered pairs `(p, q)` of that subgraph's polymers that
are incompatible.
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
