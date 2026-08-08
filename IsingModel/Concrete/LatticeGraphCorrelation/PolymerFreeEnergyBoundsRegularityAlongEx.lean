import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularity

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy regularity wrappers (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the regularity of the polymer
free energy in the activity variable: continuity and differentiability at each nonnegative
activity, and their `Set.Ici 0` counterparts. This is the ℤ^d input for differentiating the
GJ §18.5 cluster expansion stage by stage.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `polymerFreeEnergy` is `ContinuousAt` for
`t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_continuousAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ContinuousAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_continuousAt
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: `polymerFreeEnergy` is `DifferentiableAt` for
`t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_differentiableAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    DifferentiableAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_differentiableAt
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: `polymerFreeEnergy` is
`ContinuousOn (Set.Ici 0)`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_continuousOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    ContinuousOn (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_continuousOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: `polymerFreeEnergy` is
`DifferentiableOn (Set.Ici 0)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_differentiableOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    DifferentiableOn ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_differentiableOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n


end Ambient

end IsingModel
