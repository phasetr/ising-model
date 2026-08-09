import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwo
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesAbsLe

/-!
# Vanishing of the Mayer partial sum on trivial stage subgraphs

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

When the stage subgraph has no polymer, and when its edge finset is empty, its Mayer partial
sum is `0`, at every truncation order `N` and every real activity `t`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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

end Ambient
end IsingModel
