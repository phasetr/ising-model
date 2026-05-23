import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Bounds

/-!
# Per-stage Lee-Yang branch wrappers

This module contains wrappers split from `PerStageComplex.Branches`.
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

/-- **ℤ^d all-stages Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`: if all exhaustion stages are
nonempty, every stage admits the finite-volume local branch form on the
full Lee-Yang domain in pointwise basepoint form. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_all_stages_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = Ambient.partitionFunctionComplexAlongExhaustion
                (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (J : ℂ) h₀ (β : ℂ) n :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_all_stages
    (IsingModel.latticeGraph d) Λ hβ hJ

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

/-- **ℤ^d pointwise-normalised all-stage Lee-Yang branch data from positive
real parameters**: pass-through of the ambient pre-Montel branch-choice
package constructor at `latticeGraph d`. -/
theorem exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d closed-ball pointwise-normalised all-stage Lee-Yang branch data from
positive real parameters**: pass-through of the ambient closed-ball
pre-Montel branch-choice package constructor at `latticeGraph d`. -/
theorem
    exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (J : ℂ) (β : ℂ)) :=
  Ambient.exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **ℤ^d real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`): at real
parameters, the complex along-exhaustion sequence converges (in `ℂ`) to
`↑(freeEnergyInfinite G Λ p)`. Pass-through of the abstract lemma. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (fun n => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((Ambient.freeEnergyInfinite
        (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ)) :=
  Ambient.freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED hd

end Ambient

end IsingModel
