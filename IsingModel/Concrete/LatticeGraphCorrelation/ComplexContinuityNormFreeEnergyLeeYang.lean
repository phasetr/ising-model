import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d regularity of the complex free energy on the Lee-Yang subdomain

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the analyticity, the continuity and the complex differentiability
of the complex free-energy density, as a function of the external field, on
`leeYangSubdomain β (Fintype.card ↑Λ)`. Each statement assumes `0 < β` and imposes no
condition on the real coupling.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyComplex` `AnalyticOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `ContinuousOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_continuousOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_continuousOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `DifferentiableOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`): Vitali-compatible input. -/
theorem freeEnergyComplex_differentiableOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    DifferentiableOn ℂ (fun h' => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h' (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_differentiableOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

end Ambient
end IsingModel
