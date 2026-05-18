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

end Ambient

end IsingModel
