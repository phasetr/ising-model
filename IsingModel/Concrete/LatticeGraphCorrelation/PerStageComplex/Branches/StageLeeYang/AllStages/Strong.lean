import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.StageLeeYang.AllStages.Ball

/-!
# Strong all-stage Lee-Yang branch wrappers

This module contains the strong all-stage wrapper split from
`PerStageComplex.Branches.StageLeeYang.AllStages`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d strong all-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: the same local branch witness carries
`AnalyticOnNhd`, the ball-wide exponential identity, and basepoint agreement
with the stage principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n)
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong
    (IsingModel.latticeGraph d) Λ hβ hJ

end Ambient
end IsingModel
