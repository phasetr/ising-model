import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# ℤ^d freeEnergyComplex leeYangSubdomain wrappers

Narrow child module for three ℤ^d Λ-induced
`freeEnergyComplex_*_leeYangSubdomain_latticeGraph` wrappers extracted
from `ComplexContinuityNorm.lean`:

* `freeEnergyComplex_analyticOn_leeYangSubdomain_latticeGraph`,
* `freeEnergyComplex_continuousOn_leeYangSubdomain_latticeGraph`,
* `freeEnergyComplex_differentiableOn_leeYangSubdomain_latticeGraph`.
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
