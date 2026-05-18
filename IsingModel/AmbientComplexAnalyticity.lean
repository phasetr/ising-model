import IsingModel.AmbientLatticeSum
import IsingModel.ComplexAnalyticity

/-!
# Complex partition function / free energy along an exhaustion

The complex analogues of `Ambient.partitionFunctionAlongExhaustion` and
`Ambient.freeEnergyAlongExhaustion`:

* `Ambient.partitionFunctionComplexAlongExhaustion G Λ J h β n`
  := `partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β`
* `Ambient.freeEnergyComplexAlongExhaustion G Λ J h β n`
  := `freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β`

These are the foundational objects for the infinite-volume Vitali
completion argument for GJ §4.6 Thm 4.6.2: the per-site
`freeEnergyComplexAlongExhaustion` at stage `n` equals the finite-volume
`freeEnergyComplex` on the induced subgraph of the `Λ.volume n` block,
and the sequence is expected to converge (in the Montel/Vitali sense)
as `n → ∞` on the Lee-Yang (sub)domain.

This file supplies the definitions, their `_apply` unfoldings, and the
real-complex compatibility identities that identify the complex
along-exhaustion sequence with the cast of the real `…AlongExhaustion`
on real-parameter slices.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6 Thm 4.6.2, pp. 67–70.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Complex partition function along an exhaustion**: per-stage
`Z_ℂ_{Λ_n}(J, h, β)`. Complex analogue of
`partitionFunctionAlongExhaustion`. -/
noncomputable def partitionFunctionComplexAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) : ℕ → ℂ :=
  fun n => partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β

/-- **Unfolding of `partitionFunctionComplexAlongExhaustion`**:
equal to `partitionFunctionComplex` on the `n`-th volume by
construction. -/
@[simp]
theorem partitionFunctionComplexAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    partitionFunctionComplexAlongExhaustion G Λ J h β n
      = partitionFunctionComplex (inducedGraph G (Λ.volume n)) J h β :=
  rfl

/-- **Complex free energy along an exhaustion**: per-stage
`f_ℂ_{Λ_n}(J, h, β) = |Λ_n|⁻¹ · log Z_ℂ_{Λ_n}(J, h, β)`. Complex
analogue of `freeEnergyAlongExhaustion`. -/
noncomputable def freeEnergyComplexAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) : ℕ → ℂ :=
  fun n => freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β

/-- **Unfolding of `freeEnergyComplexAlongExhaustion`**:
equal to `freeEnergyComplex` on the `n`-th volume by construction. -/
@[simp]
theorem freeEnergyComplexAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    freeEnergyComplexAlongExhaustion G Λ J h β n
      = freeEnergyComplex (inducedGraph G (Λ.volume n)) J h β :=
  rfl

/-- **Real-complex compatibility** for the along-exhaustion Z at real
parameters: the cast of the real `partitionFunctionAlongExhaustion`
agrees with `partitionFunctionComplexAlongExhaustion` at the cast
parameters. Direct pointwise consequence of
`partitionFunction_ofReal_eq_partitionFunctionComplex`. -/
theorem partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((partitionFunctionAlongExhaustion G Λ p n : ℝ) : ℂ) := by
  unfold partitionFunctionComplexAlongExhaustion
  unfold partitionFunctionAlongExhaustion partitionFunctionΛ
  exact (IsingModel.partitionFunction_ofReal_eq_partitionFunctionComplex
    (inducedGraph G (Λ.volume n)) p).symm

/-- **Real-complex compatibility** for the along-exhaustion free energy
at real parameters. Direct pointwise consequence of
`freeEnergy_ofReal_eq_freeEnergyComplex`. -/
theorem freeEnergyComplexAlongExhaustion_at_real_eq_ofReal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((freeEnergyAlongExhaustion G Λ p n : ℝ) : ℂ) := by
  unfold freeEnergyComplexAlongExhaustion
  unfold freeEnergyAlongExhaustion freeEnergyΛ
  exact (IsingModel.freeEnergy_ofReal_eq_freeEnergyComplex
    (inducedGraph G (Λ.volume n)) p).symm

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

/-- **Per-stage locally-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion` under `|Re h| ≤ R`. Montel input. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
      ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
          Real.exp (|β| *
            (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
              + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_of_re_bound
    (inducedGraph G (Λ.volume n)) β J hh

/-- **Compact real-part bound** for complex fields: every compact set of
fields has a uniform bound on `|Re h|`. This is the topological input that
turns the pointwise `|Re h| ≤ R` partition-function estimate into a
compact-uniform estimate. -/
theorem exists_abs_re_le_on_isCompact {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ h ∈ K, |h.re| ≤ R := by
  rcases hK.bddAbove_image (by fun_prop : ContinuousOn (fun h : ℂ => |h.re|) K) with
    ⟨R₀, hR₀⟩
  refine ⟨max R₀ 0, le_max_right _ _, ?_⟩
  intro h hh
  exact (hR₀ ⟨h, hh, rfl⟩).trans (le_max_left _ _)

/-- **Per-stage compact-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: on any compact field set `K`,
there is a single real-part bound `R` that works for every `h ∈ K` and every
stage estimate. The right-hand side still depends on the stage size; this
packages the compact-field envelope needed by later normalised logarithmic
estimates rather than a stage-uniform Montel bound by itself. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ∀ h ∈ K,
      ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
            Real.exp (|β| *
              (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
                + R * Fintype.card (↑(Λ.volume n) : Type _))) := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, hR_nonneg, hR⟩
  refine ⟨R, hR_nonneg, ?_⟩
  intro n h hh
  exact norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    G Λ β J n (hR h hh)

/-- **Per-stage upper bound on the normalised real logarithm of `‖Z_ℂ‖`**:
under `|Re h| ≤ R` and nonvanishing of the complex partition function, the
compact-envelope estimate gives an upper bound for
`log ‖Z_{Λ_n}(h)‖ / |Λ_n|`. This is only the upper half of the later
normalised absolute-log control; it does not provide lower control on
`‖Z_{Λ_n}(h)‖`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {R : ℝ} {h : ℂ}
    (hZ : partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0)
    (hh : |h.re| ≤ R) :
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
      ≤ Real.log 2 +
        |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  set A : ℝ :=
    |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
      + R * Fintype.card (↑(Λ.volume n) : Type _))
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hconfig_pos :
      (0 : ℝ) < (Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ) := by
    rw [card_config_eq_two_pow]
    positivity
  have hexp_pos : (0 : ℝ) < Real.exp A := Real.exp_pos _
  have hnorm_pos :
      0 < ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    norm_pos_iff.mpr hZ
  have hlog :
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A := by
    calc
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          ≤ Real.log
              ((Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ)
                * Real.exp A) := by
            refine (Real.log_le_log_iff hnorm_pos
              (mul_pos hconfig_pos hexp_pos)).mpr ?_
            simpa [A] using
              norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
                G Λ β J n hh
      _ = Real.log
              (Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) : ℝ)
            + A := by
            rw [Real.log_mul hconfig_pos.ne' hexp_pos.ne', Real.log_exp]
      _ = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A := by
            rw [card_config_eq_two_pow]
            push_cast
            rw [Real.log_pow]
  calc
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹ *
          Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ := by
            field_simp
    _ ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹ *
        ((Fintype.card (↑(Λ.volume n) : Type _) : ℝ) * Real.log 2 + A) :=
          mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hcard_pos.le)
    _ = Real.log 2 + A / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          field_simp
    _ = Real.log 2 +
        |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          simp [A]

/-- **Compact-field upper normalised-log handoff under bounded edge density**:
if `K` is compact, the exhaustion has bounded edge density, every stage is
nonempty, and `Z_{Λ_n}(h)` is nonzero on `K`, then
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on
`K`. This packages the upper half of the normalised-log input for the later
normal-family argument; the lower control needed for `|log ‖Z‖|` remains
separate. -/
theorem exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) (β J : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hZ : ∀ n, ∀ h ∈ K,
      partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  rcases hBED with ⟨c, hc⟩
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  refine ⟨Real.log 2 + |β| * (|J| * c + R), ?_⟩
  intro n h hh
  have hstage :=
    real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
      G Λ β J n (hZ n h hh) (hR h hh)
  have hcard_pos_nat : 0 < Fintype.card (↑(Λ.volume n) : Type _) :=
    Fintype.card_pos
  have hvol_nonempty : (Λ.volume n).Nonempty := by
    exact Finset.card_pos.mp (by
      simpa [Fintype.card_coe] using hcard_pos_nat)
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hvol_nonempty)
  calc
    Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ Real.log 2 +
          |β| * (|J| * (inducedGraph G (Λ.volume n)).edgeFinset.card
            + R * Fintype.card (↑(Λ.volume n) : Type _))
            / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := hstage
    _ = Real.log 2 +
          |β| * (|J| *
              (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
                (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) + R) := by
          field_simp
    _ ≤ Real.log 2 + |β| * (|J| * c + R) := by
          gcongr

/-- **Stage free-energy bound from a normalised absolute-log bound**:
if the normalised quantity
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` is bounded by `C` at a nonempty stage, then the
principal complex free energy is bounded by `C + π / |Λ_n|`. This is the
precise handoff from normalised logarithmic control to the free-energy bound
needed by the later normal-family step; it does not assert that the
partition-function upper envelope alone supplies the hypothesis. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {h : ℂ} {C : ℝ}
    (hC :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
      ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  have hbase :=
    IsingModel.norm_freeEnergyComplex_le_trivial_bound
      (inducedGraph G (Λ.volume n)) β J h
  have hC' :
      |Real.log ‖partitionFunctionComplex
          (inducedGraph G (Λ.volume n)) (J : ℂ) h (β : ℂ)‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
    simpa [partitionFunctionComplexAlongExhaustion] using hC
  have hstep :
      |Real.log ‖partitionFunctionComplex
          (inducedGraph G (Λ.volume n)) (J : ℂ) h (β : ℂ)‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
          + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    linarith
  simpa [freeEnergyComplexAlongExhaustion,
    partitionFunctionComplexAlongExhaustion] using hbase.trans hstep

/-- **Setwise free-energy bound from normalised absolute-log control**:
if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every stage and every `h` in a set `K`, then
the along-exhaustion principal free energies satisfy the corresponding
stagewise bound on `K`. This packages the exact remaining analytic input for
the Montel/Vitali normal-family step. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  intro n h hh
  exact norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_stage
    G Λ β J n (hC n h hh)

/-- **Stage-independent setwise free-energy bound from normalised
absolute-log control**: if one constant `C` bounds
`|log ‖Z_{Λ_n}(h)‖| / |Λ_n|` for every nonempty stage and every `h ∈ K`, then
the along-exhaustion principal free energies are bounded on `K` by the single
stage-independent constant `C + π`. This is the locally bounded family shape
needed by a later Montel/normal-family argument. -/
theorem norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hC : ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        ≤ C + Real.pi := by
  intro n h hh
  have hstage :=
    norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set
      G Λ β J hC n h hh
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast
      (Nat.succ_le_iff.mp (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _)))
  have hpi :
      Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hcard_pos]
    nlinarith [Real.pi_nonneg, hcard_ge_one]
  have hpi_step :
      C + Real.pi / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        ≤ C + Real.pi := by
    linarith
  exact hstage.trans hpi_step

/-- **Absolute normalised-log control from two-sided control**:
if `Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` is bounded above by `C` and below by
`-C` on a set `K`, then
`|Real.log ‖Z_{Λ_n}(h)‖| / |Λ_n| ≤ C` there. This is the elementary bridge
from separate upper/lower logarithmic estimates to the normalised absolute-log
hypothesis consumed by the free-energy bounds. -/
theorem abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_two_sided_on_set
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (β J : ℝ) {K : Set ℂ} {C : ℝ}
    (hlo : ∀ n, ∀ h ∈ K,
      -C ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ))
    (hhi : ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C) :
    ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  intro n h hh
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have habs :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)| ≤ C :=
    abs_le.mpr ⟨hlo n h hh, hhi n h hh⟩
  have hrewrite :
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)|
        =
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    rw [abs_div, abs_of_pos hcard_pos]
  calc
    |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
        =
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)| := hrewrite.symm
    _ ≤ C := habs

/-- **Stage lower normalised-log bridge from a Lee-Yang polynomial lower
witness**: if the Lee-Yang polynomial factor at stage `n` has a positive lower
witness `ε` and `|Re h| ≤ R`, then the finite-volume `Z_ℂ` lower bound gives
the corresponding lower bound for
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|`.

This theorem is still stagewise: the witness `ε` may depend on `n` and `h`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_ge_of_poly_lower_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R ε : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) {h : ℂ}
    (hR : |h.re| ≤ R) (hε : 0 < ε)
    (hpoly :
      ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖) :
    Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) - β * R
      ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hZlower :
      Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε
        ≤ ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ := by
    simpa [partitionFunctionComplexAlongExhaustion] using
      IsingModel.norm_partitionFunctionComplex_ge_exp_mul_isingEdgePoly_lower
        (inducedGraph G (Λ.volume n)) hβ hJ hR hε.le hpoly
  have hprod_pos :
      0 < Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε :=
    mul_pos (Real.exp_pos _) hε
  have hZ_pos :
      0 < ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    hprod_pos.trans_le hZlower
  have hlog_le :
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    (Real.log_le_log_iff hprod_pos hZ_pos).mpr hZlower
  have hlog_prod :
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        =
      -β * R * Fintype.card (↑(Λ.volume n) : Type _) + Real.log ε := by
    rw [Real.log_mul (Real.exp_pos _).ne' hε.ne', Real.log_exp]
  calc
    Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) - β * R
        =
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          rw [hlog_prod]
          field_simp [hcard_pos.ne']
          ring
    _ ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
          div_le_div_of_nonneg_right hlog_le hcard_pos.le

/-- **Lower normalised-log handoff from polynomial-factor witnesses**:
if every stage and field in `K` has a positive polynomial-factor lower witness
`ε`, and the normalised logarithms of these witnesses are uniformly bounded
below, then the complex partition functions satisfy the lower normalised-log
hypothesis consumed by the Lee-Yang locally bounded family handoff.

This isolates the remaining hard input on the polynomial witnesses; it does not
prove a stage-uniform lower bound for them. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) {K : Set ℂ}
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  rcases hPolyLower with ⟨Lε, hLε⟩
  refine ⟨Lε + β * R, ?_⟩
  intro n h hh
  rcases hLε n h hh with ⟨ε, hε_pos, hpoly, hlogε⟩
  have hstage :=
    real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_ge_of_poly_lower_stage
      G Λ hβ hJ n (hR h hh) hε_pos hpoly
  linarith

/-- **Compact Lee-Yang polynomial lower witnesses**: compact containment in
`leeYangDomain` gives a stage-uniform lower normalised-log bound for the
positive Lee-Yang polynomial witnesses. The witness is
`ε_n = (1-r)^{|Λ_n|}`, where `r < 1` is the compact fugacity gap. -/
theorem exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  rcases IsingModel.exists_leeYangFugacity_norm_le_lt_one_on_isCompact hβ hK hKsub
    with ⟨r, hr_lt, hrbound⟩
  let s : ℝ := max r 0
  have hs0 : 0 ≤ s := le_max_right r 0
  have hs1 : s < 1 := max_lt hr_lt zero_lt_one
  have hspos : 0 < 1 - s := by linarith
  refine ⟨-Real.log (1 - s), ?_⟩
  intro n h hh
  let ε : ℝ := (1 - s) ^ Fintype.card (↑(Λ.volume n) : Type _)
  have hε_pos : 0 < ε := by
    exact pow_pos hspos _
  have ht₀ : 0 ≤ Real.exp (-2 * β * J) := (Real.exp_pos _).le
  have ht₁ : Real.exp (-2 * β * J) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < 2 * β * J := by positivity
    linarith
  have hz : ‖IsingModel.leeYangFugacity (β : ℂ) h‖ ≤ s :=
    (hrbound h hh).trans (le_max_left r 0)
  have hpoly :
      ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ := by
    simpa [ε] using
      IsingModel.one_sub_radius_pow_card_le_norm_isingEdgePoly_eval_leeYangFugacityVec
        (G := inducedGraph G (Λ.volume n)) ht₀ ht₁ hs0 hs1 hz
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hlogε :
      Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) =
        Real.log (1 - s) := by
    unfold ε
    rw [Real.log_pow]
    field_simp [hcard_pos.ne']
  exact ⟨ε, hε_pos, hpoly, by rw [hlogε]; simp⟩

/-- **Compact Lee-Yang lower normalised-log bound**: the quantitative
root-product lower bound for the Lee-Yang polynomial supplies the lower-log
hypothesis for the complex partition functions on any compact
`K ⊆ leeYangDomain`. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    G Λ hβ.le hJ.le hR
    (exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
      G Λ hβ hJ hK hKsub)

/-- **Per-stage `Z_ℂ ≠ 0 on leeYangDomain`** for
`partitionFunctionComplexAlongExhaustion` (ferromagnetic). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain
    (inducedGraph G (Λ.volume n)) hβ hJ hh

/-- **Compact-field upper normalised-log bound on Lee-Yang compact sets**:
on compact subsets of `leeYangDomain`, the Lee-Yang nonvanishing theorem
discharges the nonzero hypothesis in
`exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact`.
Thus, under bounded edge density and nonempty stages,
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on
`K ⊆ leeYangDomain`. This is still only the upper half of the absolute
normalised-log input. -/
theorem exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    G Λ hBED β J hK (by
      intro n h hh
      exact partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
        G Λ hβ hJ n (hKsub hh))

/-- **Lee-Yang compact absolute normalised-log handoff from lower control**:
on compact `K ⊆ leeYangDomain`, the automatic Lee-Yang upper bound and a
remaining lower normalised-log hypothesis combine into the absolute
normalised-log hypothesis consumed by the free-energy bounds. -/
theorem exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  rcases hLower with ⟨L, hL⟩
  rcases exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
      G Λ hBED hβ hJ hK hKsub with ⟨U, hU⟩
  refine ⟨max L U, ?_⟩
  exact abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_two_sided_on_set
    G Λ β J
    (by
      intro n h hh
      exact (neg_le_neg (le_max_left L U)).trans (hL n h hh))
    (by
      intro n h hh
      exact (hU n h hh).trans (le_max_right L U))

/-- **Lee-Yang compact locally bounded free-energy family from lower control**:
on compact `K ⊆ leeYangDomain`, once a stage-uniform lower normalised-log
bound is available, the Lee-Yang compact upper bound supplies the absolute-log
control and hence a stage-independent free-energy bound `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
      G Λ hBED hβ hJ hK hKsub hLower with ⟨C, hC⟩
  exact ⟨C, norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    G Λ β J hC⟩

/-- **Lee-Yang locally bounded family from polynomial-factor lower witnesses**:
on compact `K ⊆ leeYangDomain`, a stage-uniform lower normalised-log bound for
positive Lee-Yang polynomial-factor witnesses supplies the lower-log hypothesis
for `Z_ℂ`; combining this with the Lee-Yang upper bound gives a single
stage-independent free-energy bound `‖f_n(h)‖ ≤ C + π`.

This remains conditional on the polynomial-witness lower normalised-log input;
it only packages the route from that input to the locally bounded family. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  have hLower :
      ∃ L : ℝ, ∀ n, ∀ h ∈ K,
        -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion
            G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
    exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
      G Λ hβ.le hJ.le hR hPolyLower
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    G Λ hBED hβ hJ hK hKsub hLower

/-- **Compact Lee-Yang locally bounded family from polynomial lower witnesses**:
compactness supplies the real-part bound consumed by
`exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang`. The
polynomial-witness lower normalised-log input remains an explicit hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    G Λ hBED hβ hJ hK hKsub hR hPolyLower

/-- **Ball-local Lee-Yang locally bounded family from polynomial lower
witnesses**: if the polynomial-witness lower normalised-log input is available
on a closed ball contained in `leeYangDomain`, then the free-energy family is
bounded on the corresponding open ball. This is the local-cover shape used by
later normal-family/Vitali inputs. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
      G Λ hBED hβ hJ (isCompact_closedBall h₀ ρ) hsub hPolyLower with ⟨C, hC⟩
  exact ⟨C, fun n h hh => hC n h (Metric.ball_subset_closedBall hh)⟩

/-- **Point-local Lee-Yang locally bounded family from polynomial lower
witnesses**: around any Lee-Yang point, choose a positive closed ball inside
`leeYangDomain`; a radius-dependent polynomial-witness lower normalised-log
input on that closed ball gives a bound on the corresponding open ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_around
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain)
    (hPolyLower : ∀ ρ : ℝ, 0 < ρ →
      Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain →
      ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
        ∃ ε : ℝ, 0 < ε ∧
          ε ≤ ‖(IsingModel.isingEdgePoly
            (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
              (Real.exp (-2 * β * J)))).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
          -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases IsingModel.leeYangDomain_closedBall_subset hmem with ⟨ρ, hρ, hsub⟩
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
      G Λ hBED hβ hJ hsub (hPolyLower ρ hρ hsub) with ⟨C, hC⟩
  exact ⟨ρ, hρ, C, hC⟩

/-- **Compact Lee-Yang locally bounded family**: on compact
`K ⊆ leeYangDomain`, the root-product polynomial lower bound removes the
previous explicit polynomial-witness hypothesis and yields the uniform
free-energy bound `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    G Λ hBED hβ hJ hK hKsub
    (exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
      G Λ hβ hJ hK hKsub hR)

/-- **Ball-local Lee-Yang locally bounded family**: a closed ball contained in
`leeYangDomain` gives a uniform free-energy bound on the corresponding open
ball, with no remaining polynomial-witness hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
      G Λ hBED hβ hJ (isCompact_closedBall h₀ ρ) hsub with ⟨C, hC⟩
  exact ⟨C, fun n h hh => hC n h (Metric.ball_subset_closedBall hh)⟩

/-- **Point-local Lee-Yang locally bounded family**: every point of
`leeYangDomain` has a ball on which the free-energy family is uniformly
bounded, with the polynomial lower normalised-log input discharged by the
root-product estimate. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_around
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases IsingModel.leeYangDomain_closedBall_subset hmem with ⟨ρ, hρ, hsub⟩
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
      G Λ hBED hβ hJ hsub with ⟨C, hC⟩
  exact ⟨ρ, hρ, C, hC⟩

/-! ## Real-axis convergence to `freeEnergyInfinite`

The real-axis half of the Vitali identification: at real parameters,
`freeEnergyComplexAlongExhaustion G Λ ↑p.J ↑p.h ↑p.β n` converges to
`↑(freeEnergyInfinite G Λ p)` as `n → ∞`. Combined with the Montel
extraction (Step 3) and holomorphic-uniqueness (Step 5-6), this pins
down the Vitali limit on the Lee-Yang (sub)domain. -/

/-- **Real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`). Pointwise
limit for the Vitali identification at real parameters. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p) :
    Filter.Tendsto
      (fun n => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((freeEnergyInfinite G Λ p : ℝ) : ℂ)) := by
  have h_real := freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    G Λ p hBED hd
  have h_eq : (fun n => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      = fun n => ((freeEnergyAlongExhaustion G Λ p n : ℝ) : ℂ) := by
    funext n
    exact freeEnergyComplexAlongExhaustion_at_real_eq_ofReal G Λ p n
  rw [h_eq]
  exact (Complex.continuous_ofReal.tendsto _).comp h_real

/-! ## Conditional Vitali assembly

The next statements package the final Vitali handoff for the
along-exhaustion complex free energy. The hard analytic input remains
the locally uniform convergence of the finite-volume branch family; once
that input is supplied, these lemmas turn it into holomorphicity of the
infinite-volume candidate and identify the real-positive slice with the
Fekete `freeEnergyInfinite` limit. -/

/-- **Conditional Vitali assembly on an open set** for
`freeEnergyComplexAlongExhaustion`: a locally uniform limit of
per-stage holomorphic complex free energies is holomorphic on the same
open set. This is the along-exhaustion specialization of
`IsingModel.vitali_bridge`. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {U : Set ℂ} (hU : IsOpen U) (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ J h β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  IsingModel.vitali_bridge hU hF hconv

/-- **Conditional Vitali assembly on `leeYangDomain`** for
`freeEnergyComplexAlongExhaustion`. This is the named Step 5 handoff in
the infinite-volume proof of GJ §4.6 Thm 4.6.2: after the branch-family
locally-uniform convergence is available on the Lee-Yang domain, the
limit is holomorphic there. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  IsingModel.vitali_bridge_leeYangDomain hF hconv

/-- **Real-axis identification of a locally uniform Vitali limit**:
if the complex along-exhaustion free energies converge locally uniformly
on `leeYangDomain` to `f`, then at any real parameter `p.h` belonging to
`leeYangDomain`, the value of `f` is the cast of the real
`freeEnergyInfinite` limit. -/
theorem freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hp
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  exact tendsto_nhds_unique hpoint hreal

/-- **Conditional Vitali assembly with real-axis identification**:
combines holomorphicity of the locally uniform Lee-Yang limit with its
identification on the real-positive slice via the real
`freeEnergyInfinite` limit. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      IsingModel.leeYangDomain)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  ⟨freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
      G Λ (p.J : ℂ) (p.β : ℂ) hF hconv,
    freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real
      G Λ p hBED hd hp hconv⟩

/-! ## Local branch-family Vitali assembly

The preceding Lee-Yang-domain bridge is phrased for the principal
`freeEnergyComplexAlongExhaustion` sequence. The full Lee-Yang proof uses
locally chosen logarithm branches instead. The next wrappers package the
local handoff: once a coherent branch family on a Lee-Yang ball is known to
converge locally uniformly, Vitali gives holomorphicity of the local limit,
and the PR #2675 basepoint normalisation identifies the centre value with the
real-axis Fekete limit. -/

/-- **Local branch-family Vitali bridge on a ball**: if a chosen per-stage
branch family is analytic on a ball and converges locally uniformly there,
then its limit is holomorphic on that ball. The exponential and basepoint
clauses are retained in `hbranch` so the hypothesis matches the strong
Lee-Yang branch witnesses used in the later normal-family step. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  IsingModel.vitali_bridge Metric.isOpen_ball
    (fun n => (hbranch n).1.differentiableOn) hconv

/-- **Local branch-family Vitali bridge with centre identification**:
for a ball centred at the real parameter `p.h`, a locally-uniform limit of
normalised branch witnesses is holomorphic on the ball and agrees at the
centre with the real infinite-volume free energy. The remaining external
input is the coherent locally-uniform convergence of the chosen branches. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
      G Λ (p.J : ℂ) (p.β : ℂ) hbranch hconv
  have hcenter : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) r := Metric.mem_ball_self hr
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hcenter
  have hbranch_eq :
      (fun n => F n (p.h : ℂ))
        = fun n => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n := by
    funext n
    exact (hbranch n).2.2
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  exact ⟨hdiff, tendsto_nhds_unique hpoint hreal⟩

/-- **Local-cover branch-family Vitali bridge on `leeYangDomain`**:
if every Lee-Yang point has a ball on which a chosen branch family converges
locally uniformly to the same function `f`, then `f` is holomorphic on the
whole Lee-Yang domain. This globalises the PR #2676 ball handoff while leaving
the coherent local branch construction as an explicit hypothesis. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = partitionFunctionComplexAlongExhaustion G Λ J z β n)
              ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain := by
  intro h₀ hmem
  rcases hlocal h₀ hmem with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hdiff_ball :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
      G Λ J β hbranch hconv
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- **Local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local cover of Lee-Yang balls whose branch
families converge locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`; at a real Lee-Yang centre it agrees with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = partitionFunctionComplexAlongExhaustion G Λ
                        (p.J : ℂ) z (p.β : ℂ) n)
              ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover
      G Λ (p.J : ℂ) (p.β : ℂ) hlocal
  rcases hlocal (p.h : ℂ) hp with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hcenter :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr hbranch hconv
  exact ⟨hdiff, hcenter.2⟩

/-! ## Subsequence local branch-family Vitali assembly

The actual Montel step is expected to produce a locally uniformly convergent
subsequence of local Lee-Yang logarithm branches. The next wrappers are the
subsequence-indexed variants of the preceding local branch-family handoffs:
the stage at branch-family index `m` is `σ m`, where `σ` is strictly
increasing. -/

/-- **Subsequence local branch-family Vitali bridge on a ball**: if a
Montel-extracted subsequence of per-stage branch witnesses is analytic on a
Lee-Yang ball and converges locally uniformly there, then its limit is
holomorphic on that ball. The branch identities are written at stage `σ m`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {σ : ℕ → ℕ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  IsingModel.vitali_bridge Metric.isOpen_ball
    (fun m => (hbranch m).1.differentiableOn) hconv

/-- **Subsequence local branch-family Vitali bridge with centre
identification**: for a ball centred at the real parameter `p.h`, a locally
uniform limit of subsequence branch witnesses is holomorphic on the ball and
agrees at the centre with the real infinite-volume free energy. The real-axis
convergence is composed with the strictly increasing index map `σ`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ F m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ (p.J : ℂ) (p.β : ℂ) hbranch hconv
  have hcenter : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) r := Metric.mem_ball_self hr
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hcenter
  have hbranch_eq :
      (fun m => F m (p.h : ℂ))
        = fun m => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    funext m
    exact (hbranch m).2.2
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  have hreal_subseq :
      Filter.Tendsto
        (fun m => freeEnergyComplexAlongExhaustion G Λ
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
        Filter.atTop
        (nhds ((freeEnergyInfinite G Λ p : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using hreal.comp hσ.tendsto_atTop
  exact ⟨hdiff, tendsto_nhds_unique hpoint hreal_subseq⟩

/-- **Subsequence local-cover branch-family Vitali bridge on
`leeYangDomain`**: if every Lee-Yang point has a ball on which a
subsequence-indexed branch family converges locally uniformly to the same
function `f`, then `f` is holomorphic on the whole Lee-Yang domain. This is
the handoff shape expected after a Montel diagonal extraction. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain := by
  intro h₀ hmem
  rcases hlocal h₀ hmem with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hdiff_ball :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β hbranch hconv
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- **Subsequence local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang cover of subsequence branch
families converging locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`, and at a real Lee-Yang centre it agrees with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ
                        (p.J : ℂ) z (p.β : ℂ) (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
      G Λ (p.J : ℂ) (p.β : ℂ) hlocal
  rcases hlocal (p.h : ℂ) hp with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hcenter :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr hσ hbranch hconv
  exact ⟨hdiff, hcenter.2⟩

end Ambient

end IsingModel
