import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Triangle-inequality bound on a Mayer expansion term, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

By definition the order-`k` Mayer expansion term of the stage subgraph is the sum, over
length-`k` sequences `ω` of that subgraph's polymers, of
`ursellCoefficient ω * clusterSeqActivity t ω`. Its absolute value is bounded by the same
sum with both factors replaced by their absolute values, at every order `k` and every real
activity `t`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_abs_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph G (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  mayerExpansionTerm_Λ_abs_le G (Λ.volume n) k t

end Ambient
end IsingModel
