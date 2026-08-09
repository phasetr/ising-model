import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# ℤ^d signs of the leading Mayer terms and the edgeless polymer set

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the signs of the
leading Mayer expansion terms of the induced subgraph — the order-`1` term is nonnegative and
the order-`2` term is nonpositive — together with the vanishing of the polymer set of that
subgraph when its edge set is empty. The sign statements assume `0 ≤ t` on the activity and
nothing else; the polymer statement assumes only that empty edge set.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_latticeGraph_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t :=
  Ambient.mayerExpansionTerm_Λ_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two_nonpos_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t ≤ 0 :=
  Ambient.mayerExpansionTerm_Λ_two_nonpos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymers_Λ_latticeGraph_eq_empty_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset
      = ∅) :
    IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.allPolymers_Λ_eq_empty_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty

end Ambient
end IsingModel
