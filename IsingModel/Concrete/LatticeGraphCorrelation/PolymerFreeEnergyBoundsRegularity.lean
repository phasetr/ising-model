import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds

/-!
# Concrete ℤ^d polymerFreeEnergy regularity wrappers (§18.5)

Narrow child module for the 8 ℤ^d `polymerFreeEnergy_Λ_latticeGraph_*`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_*` regularity
wrappers (`continuousAt`, `differentiableAt`, `continuousOn_Ici_zero`,
`differentiableOn_Ici_zero` in both Λ and AlongExhaustion forms)
extracted from `PolymerFreeEnergyBounds.lean` in PR #2059. Each is a
thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_*` / `polymerFreeEnergyAlongExhaustion_*`
regularity lemma at `IsingModel.latticeGraph d`. The theorem names
are unchanged from the former `PolymerFreeEnergyBounds`
declarations.
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
