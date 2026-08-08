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

/-- **ℤ^d Λ: polymerFreeEnergy preserves order on `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_of_le_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s :=
  Ambient.polymerFreeEnergy_Λ_le_of_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht hs hts

/-- **ℤ^d Λ: polymerFreeEnergy strict-form order preservation**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_of_le_strict_form
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s :=
  Ambient.polymerFreeEnergy_Λ_le_of_le_strict_form
    (IsingModel.latticeGraph d) Λ ht hts

end Ambient
end IsingModel
