import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.Lattice

/-!
# ℤ^d Λ polymerFreeEnergy degenerate volumes and order (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the degenerate behaviour of
the polymer free energy — it vanishes identically when the induced graph carries no polymer,
and likewise when it has no edge — and its preservation of the order `t ≤ s`, once with both
activities assumed nonnegative and once with only the lower one. These fix the boundary
cases of the GJ §18.5 cluster expansion on ℤ^d.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: polymerFreeEnergy = 0 for empty-polymer induced graphs**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t = 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ h_no t

/-- **ℤ^d Λ: polymerFreeEnergy = 0 for edgeless induced graphs**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph
      (IsingModel.latticeGraph d) Λ).edgeFinset = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t = 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty t

/-- At the `ℤ^d` Λ layer, polymer free energy preserves order when the smaller activity is
nonnegative. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_of_le_of_nonneg_left
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s :=
  Ambient.polymerFreeEnergy_Λ_le_of_le_of_nonneg_left
    (IsingModel.latticeGraph d) Λ ht hts

end Ambient
end IsingModel
