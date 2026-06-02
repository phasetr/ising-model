import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.StageLeeYang.AllStages.Pointwise

/-!
# Ball all-stage Lee-Yang branch wrappers

This module contains the ball all-stage wrapper split from
`PerStageComplex.Branches.StageLeeYang.AllStages`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d all-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: if all stages are nonempty, every stage
admits a local analytic branch on each ball contained in `leeYangDomain`,
with the exponential identity holding throughout the ball. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ ∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages
    (IsingModel.latticeGraph d) Λ hβ hJ

end Ambient
end IsingModel
