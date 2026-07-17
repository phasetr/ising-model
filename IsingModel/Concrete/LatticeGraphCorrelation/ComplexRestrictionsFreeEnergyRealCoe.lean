import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d `freeEnergyComplex` real-coe regularity wrappers

Narrow child module for three ℤ^d Λ-induced
`freeEnergyComplex_*_h_real_coe_latticeGraph` wrappers
(`analyticAt`, `differentiableAt`, `continuousAt`) extracted from
`ComplexRestrictions.lean`. Each wrapper is a thin pass-through to the
corresponding ambient `IsingModel.freeEnergyComplex_*_h_real_coe` lemma.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `f_ℂ` `AnalyticAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_analyticAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_analyticAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `DifferentiableAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_differentiableAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    DifferentiableAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_differentiableAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `ContinuousAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_continuousAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_continuousAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

end Ambient
end IsingModel
