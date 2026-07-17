import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularity

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy regularity wrappers (§18.5)

Narrow child module for the four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` regularity wrappers
extracted from `PolymerFreeEnergyBoundsRegularity.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_continuousAt`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_differentiableAt`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_continuousOn_Ici_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_differentiableOn_Ici_zero`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*` regularity lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyBoundsRegularity` declarations.
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
