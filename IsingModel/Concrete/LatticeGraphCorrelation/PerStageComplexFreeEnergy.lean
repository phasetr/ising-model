import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d per-stage `freeEnergyComplexAlongExhaustion` wrappers

Narrow child module for four ℤ^d per-stage Lee-Yang regularity wrappers for
the complex free energy along an exhaustion extracted from
`PerStageComplex.lean`:

* `freeEnergyComplexAlongExhaustion_analyticAt_h_stage_latticeGraph`,
* `freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage_latticeGraph`,
* `freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage_latticeGraph`,
* `freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-stage `AnalyticAt h₀` for `freeEnergyComplexAlongExhaustion`
under `Z_{stage} ∈ slitPlane`**. -/
theorem freeEnergyComplexAlongExhaustion_analyticAt_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ)
    (hZ : Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h₀ β n ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) h₀ :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticAt_h_stage
    (IsingModel.latticeGraph d) Λ J β n h₀ hZ

/-- **ℤ^d per-stage `AnalyticOnNhd` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion` (ferromagnetic). -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

/-- **ℤ^d per-stage `DifferentiableOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

/-- **ℤ^d per-stage `ContinuousOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    ContinuousOn
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

end Ambient
end IsingModel
