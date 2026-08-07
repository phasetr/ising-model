import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure

/-!
# ℤ^d AlongExhaustion mayer-epsilon infrastructure wrappers

Instantiates the along-exhaustion sign and degeneracy facts about the low-order Mayer
expansion terms and the polymer set at `IsingModel.latticeGraph d`, the bookkeeping the
ℤ^d cluster-expansion estimates rest on.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: 0 ≤ mayerExpansionTerm at n = 1** under
`0 ≤ t`. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t :=
  Ambient.mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 2 ≤ 0** under
`0 ≤ t`. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_two_nonpos_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t
      ≤ 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem
allPolymersAlongExhaustion_latticeGraph_eq_empty_of_edgeFinset_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅ :=
  Ambient.allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ n h_empty

end Ambient
end IsingModel
