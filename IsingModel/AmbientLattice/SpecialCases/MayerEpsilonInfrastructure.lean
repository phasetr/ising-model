import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSum
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureAllPolymers

/-!
# Sign of the order-1 and order-2 Mayer expansion terms, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

For an activity `t` with `0 ≤ t`, the Mayer expansion term of the stage subgraph is
non-negative at order `1` and non-positive at order `2`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t :=
  mayerExpansionTerm_Λ_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) 2 t
      ≤ 0 :=
  mayerExpansionTerm_Λ_two_nonpos_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
