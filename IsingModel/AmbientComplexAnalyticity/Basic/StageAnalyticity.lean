import IsingModel.AmbientComplexAnalyticity.Basic.Core

/-!
# Per-stage analyticity wrappers

This module contains wrappers split from `AmbientComplexAnalyticity.Basic`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Per-stage analyticity / continuity / norm bounds

Per-stage analytic / continuous / norm-bound properties for the
along-exhaustion complex objects. Each is a thin pass-through of the
finite-volume result (from `ComplexAnalyticity.lean`) applied at the
stage-`n` induced subgraph `inducedGraph G (Λ.volume n)`. -/

/-- **Per-stage entire in `h`** for `partitionFunctionComplexAlongExhaustion`.
Pass-through of `IsingModel.partitionFunctionComplex_analyticAt_h` at
stage `n`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_h_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ) :
    AnalyticAt ℂ
      (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n) h₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_h
    (inducedGraph G (Λ.volume n)) J β h₀

/-- **Per-stage entire in `J`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_J_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℂ) (n : ℕ) (J₀ : ℂ) :
    AnalyticAt ℂ
      (fun J => partitionFunctionComplexAlongExhaustion G Λ J h β n) J₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_J
    (inducedGraph G (Λ.volume n)) h β J₀

/-- **Per-stage entire in `β`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℂ) (n : ℕ) (β₀ : ℂ) :
    AnalyticAt ℂ
      (fun β => partitionFunctionComplexAlongExhaustion G Λ J h β n) β₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_beta
    (inducedGraph G (Λ.volume n)) J h β₀

/-- **Per-stage joint entire** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      partitionFunctionComplexAlongExhaustion G Λ z.1 z.2.1 z.2.2 n) z₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_joint
    (inducedGraph G (Λ.volume n)) z₀

/-- **Per-stage `Continuous` in `h`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_continuous_h_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) :
    Continuous
      (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n) :=
  IsingModel.continuous_partitionFunctionComplex_h
    (inducedGraph G (Λ.volume n)) J β

/-- **Per-stage `AnalyticAt h₀` for `freeEnergyComplexAlongExhaustion`
under `Z_{stage} ∈ slitPlane`**. -/
theorem freeEnergyComplexAlongExhaustion_analyticAt_h_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ)
    (hZ : partitionFunctionComplexAlongExhaustion G Λ J h₀ β n
            ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ J h β n) h₀ :=
  IsingModel.freeEnergyComplex_analyticAt_h
    (inducedGraph G (Λ.volume n)) J β h₀ hZ

/-- **Per-stage `AnalyticOnNhd` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion` (ferromagnetic real `β > 0`, `J ∈ ℝ`):
the finite-volume analytic branch on the stage-`n` Lee-Yang subdomain. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β (Fintype.card (↑(Λ.volume n) : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_leeYangSubdomain
    (inducedGraph G (Λ.volume n)) hβ J

/-- **Per-stage `DifferentiableOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β (Fintype.card (↑(Λ.volume n) : Type _))) :=
  IsingModel.freeEnergyComplex_differentiableOn_leeYangSubdomain
    (inducedGraph G (Λ.volume n)) hβ J

/-- **Per-stage `ContinuousOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    ContinuousOn
      (fun h => freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β (Fintype.card (↑(Λ.volume n) : Type _))) :=
  IsingModel.freeEnergyComplex_continuousOn_leeYangSubdomain
    (inducedGraph G (Λ.volume n)) hβ J

/-- **Per-stage Lee-Yang local branch** for
`freeEnergyComplexAlongExhaustion`: at any stage with nonempty volume
and any `h₀ ∈ leeYangDomain`, there is an analytic local branch whose
basepoint value agrees with the principal `freeEnergyComplexAlongExhaustion`
value and whose exponential recovers the stage partition function at
that basepoint. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
          = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n
      ∧ f h₀ = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n :=
  IsingModel.exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (inducedGraph G (Λ.volume n)) hβ hJ hmem

/-- **Per-stage Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`: a pointwise `∀ h₀ ∈ leeYangDomain`
form of the local branch construction at a fixed stage. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)] :
    ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n :=
  fun _ hmem =>
    freeEnergyComplexAlongExhaustion_exists_analyticAt_branch_leeYangDomain_stage
      G Λ hβ hJ n hmem

/-- **Per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: at any nonempty stage and any ball
contained in `leeYangDomain`, there is an analytic branch on that ball whose
exponential recovers the stage partition function throughout the ball. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n :=
  IsingModel.exists_freeEnergyComplex_analyticOnNhd_ball
    (inducedGraph G (Λ.volume n)) hβ hJ hr hsub

/-- **Strong per-stage Lee-Yang local branch on a ball** for
`freeEnergyComplexAlongExhaustion`: the branch is analytic on the ball,
its exponential recovers the stage partition function throughout the ball,
and its basepoint value agrees with the stage principal free energy. -/
theorem freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    [Nonempty (↑(Λ.volume n) : Type _)]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ (∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
            = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n)
      ∧ f h₀ = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n :=
  IsingModel.exists_freeEnergyComplex_analyticOnNhd_branch_ball_strong
    (inducedGraph G (Λ.volume n)) hβ hJ hr hsub

/-- **All-stages Lee-Yang branch family** for
`freeEnergyComplexAlongExhaustion`: if every stage of the exhaustion is
nonempty, then every stage admits the finite-volume local branch form on
the full Lee-Yang domain in pointwise basepoint form. -/
theorem freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_all_stages
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f h₀)
            = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n
        ∧ f h₀ = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n :=
  fun n =>
    freeEnergyComplexAlongExhaustion_analyticBranch_leeYangDomain_stage
      G Λ hβ hJ n

/-- **All-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: if every stage is nonempty, then every
stage admits a local analytic branch on each ball contained in `leeYangDomain`,
with the exponential identity holding throughout the ball. This is the
branch-family input shape for the later normal-family/Vitali convergence step. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ ∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n :=
by
  intro n h₀ r hr hsub
  exact freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage
    G Λ hβ hJ n hr hsub

/-- **Strong all-stages Lee-Yang local branches on balls** for
`freeEnergyComplexAlongExhaustion`: every nonempty stage admits a local
analytic branch on each Lee-Yang ball, with the ball-wide exponential
identity and basepoint principal-value agreement in the same witness. -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ n, ∀ {h₀ : ℂ} {r : ℝ}, 0 < r →
      Metric.ball h₀ r ⊆ IsingModel.leeYangDomain →
      ∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
              = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n)
        ∧ f h₀ = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h₀ (β : ℂ) n :=
by
  intro n h₀ r hr hsub
  exact freeEnergyComplexAlongExhaustion_exists_analyticOnNhd_branch_ball_stage_strong
    G Λ hβ hJ n hr hsub

end Ambient

end IsingModel
