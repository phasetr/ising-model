import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d per-stage regularity of the complex free energy along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a fixed stage `n` of an `Ambient.Exhaustion`
of `Fin d → ℤ`, the regularity in the external field of the complex free-energy density of
that stage's volume. Analyticity at a complex base point is given for arbitrary complex `J`
and `β` and assumes exactly that the stage partition function lies in `Complex.slitPlane`
there. Analyticity on a neighbourhood, complex differentiability and continuity on
`leeYangSubdomain β (Fintype.card ↑(Λ.volume n))` are given for real `J` and `β`, and each
assumes `0 < β` and nothing else.
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
