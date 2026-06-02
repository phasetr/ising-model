import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds

/-!
# Per-stage Lee-Yang branch wrappers

Stage-local wrappers split from `PerStageComplex.Branches.StageLeeYang`.
-/

namespace IsingModel
namespace Ambient

/-! #### Per-stage Lee-Yang branch wrappers -/

/-- **ℤ^d per-stage Lee-Yang local branch** for
`freeEnergyComplexAlongExhaustion`: at a nonempty stage and any
`h₀ ∈ leeYangDomain`, an analytic local branch recovers the stage
partition function at the basepoint and agrees there with the stage
principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
          = Ambient.partitionFunctionComplexAlongExhaustion
              (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
      ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hmem

/-- **ℤ^d per-stage Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`, in pointwise `∀ h₀ ∈ leeYangDomain`
form at a fixed nonempty stage. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)] :
    ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **ℤ^d per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: the local analytic branch is analytic on
the ball and its exponential recovers the stage partition function throughout
that ball. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hr hsub

/-- **ℤ^d strong per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: the same branch carries
`AnalyticOnNhd`, the ball-wide exponential identity, and basepoint agreement
with the stage principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ (∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) z (β : ℂ) n)
      ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong
    (IsingModel.latticeGraph d) Λ hβ hJ n hr hsub

end Ambient
end IsingModel
