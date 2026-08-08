import IsingModel.AmbientLattice.AnalyticityLambdaRegularity
import IsingModel.Lattice

/-!
# Concrete ℤ^d polymerFreeEnergy regularity wrappers (§18.5)

Instantiates the Λ-level regularity of the polymer free energy at
`IsingModel.latticeGraph d`, pointwise and on `Ici 0`, the ℤ^d input for differentiating the
GJ §18.5 cluster expansion.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy regularity ℤ^d wraps -/

/-- **ℤ^d Λ: `polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_continuousAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s) t :=
  Ambient.polymerFreeEnergy_Λ_continuousAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: `polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_differentiableAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s) t :=
  Ambient.polymerFreeEnergy_Λ_differentiableAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: `polymerFreeEnergy` is `ContinuousOn (Set.Ici 0)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_continuousOn_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    ContinuousOn (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_continuousOn_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: `polymerFreeEnergy` is `DifferentiableOn (Set.Ici 0)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_differentiableOn_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_differentiableOn_Ici_zero
    (IsingModel.latticeGraph d) Λ

end Ambient

end IsingModel
