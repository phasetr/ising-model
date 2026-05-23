import IsingModel.ClusterExpansion.HighTempGeneralRegularity.MagnetizationSusceptibility

/-!
# High-temperature Gibbs expectation regularity

Mechanical child split from `ClusterExpansion.HighTempGeneralRegularity`.
-/

namespace IsingModel

open Finset
/-- **Numerator of gibbsExpectation jointly `AnalyticAt ℝ` in `(β, J, h)`**
for any observable `F : Config ι → ℝ`: the unnormalised expectation
`∑_σ F(σ) · boltzmannWeight G p σ` is real-analytic jointly. Each
summand is `(constant in (β, J, h)) · exp(polynomial in (β, J, h))`. -/
theorem gibbsExpectation_numerator_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ =>
        ∑ σ : Config ι, F σ *
          boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ)
      (β, J, h) := by
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      ∑ σ : Config ι, F σ *
        boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι, F σ *
        Real.exp (p.1 * p.2.1 * (∑ e ∈ G.edgeFinset, edgeSpin σ e) +
          p.1 * p.2.2 * (∑ i : ι, Spin.sign ℝ (σ i))) := by
    funext p
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.mul ?_
  refine analyticAt_rexp.comp ?_
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **gibbsExpectation jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
generalisation): for any observable `F : Config ι → ℝ` and any
`(β, J, h)`,
  `⟨F⟩ = (1/Z) · ∑_σ F(σ) · exp(-β·H(σ))`
is real-analytic jointly in all three Ising parameters.

Generalises `correlation_analyticAt_joint` (PR #1536, the special case
`F = spinProduct A`) to arbitrary observables. -/
theorem gibbsExpectation_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F)
      (β, J, h) := by
  unfold gibbsExpectation
  have h_pos : 0 < partitionFunction G ⟨J, h, β⟩ := partitionFunction_pos G _
  set f : ℝ × ℝ × ℝ → ℝ :=
    fun p => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩ with hf_def
  have h_f_val : f (β, J, h) = partitionFunction G ⟨J, h, β⟩ := rfl
  have h_inv : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      (partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)⁻¹) (β, J, h) := by
    have h_Z : AnalyticAt ℝ f (β, J, h) :=
      partitionFunction_analyticAt_joint G β J h
    have h_ne : f (β, J, h) ≠ 0 := by rw [h_f_val]; exact h_pos.ne'
    exact h_Z.inv h_ne
  exact h_inv.mul (gibbsExpectation_numerator_analyticAt_joint G F β J h)

/-- **gibbsExpectation jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 generalisation): global form. -/
theorem gibbsExpectation_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => gibbsExpectation_analyticAt_joint G F β J h

/-- **gibbsExpectation jointly `Continuous` in `(β, J, h)`** (§18.6
generalisation, direct corollary). -/
theorem gibbsExpectation_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (gibbsExpectation_analyticAt_joint G F β J h).continuousAt

/-- **gibbsExpectation jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6 generalisation, direct corollary). -/
theorem gibbsExpectation_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F) :=
  fun ⟨β, J, h⟩ => (gibbsExpectation_analyticAt_joint G F β J h).differentiableAt

/-- **partitionFunction Continuous in `β` at general `h`** (§18.6,
direct corollary of `partitionFunction_analyticAt_beta_general_h`). -/
theorem partitionFunction_continuous_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℝ) :
    Continuous (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) :=
  continuous_iff_continuousAt.mpr fun β =>
    (partitionFunction_analyticAt_beta_general_h G J h β).continuousAt

/-- **partitionFunction Differentiable in `β` at general `h`** (§18.6). -/
theorem partitionFunction_differentiable_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) :=
  fun β => (partitionFunction_analyticAt_beta_general_h G J h β).differentiableAt

/-- **partitionFunction Continuous in `J` at general `h`** (§18.6,
direct corollary of `partitionFunction_analyticAt_J_general_h`). -/
theorem partitionFunction_continuous_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β h : ℝ) :
    Continuous (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) :=
  continuous_iff_continuousAt.mpr fun J =>
    (partitionFunction_analyticAt_J_general_h G β h J).continuousAt

/-- **partitionFunction Differentiable in `J` at general `h`** (§18.6). -/
theorem partitionFunction_differentiable_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) :=
  fun J => (partitionFunction_analyticAt_J_general_h G β h J).differentiableAt

/-- **partitionFunction Continuous in `h`** (§18.6, direct corollary of
`partitionFunction_analyticAt_h`). -/
theorem partitionFunction_continuous_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    Continuous (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) :=
  continuous_iff_continuousAt.mpr fun h =>
    (partitionFunction_analyticAt_h G J β h).continuousAt

/-- **partitionFunction Differentiable in `h`** (§18.6). -/
theorem partitionFunction_differentiable_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) :=
  fun h => (partitionFunction_analyticAt_h G J β h).differentiableAt
end IsingModel
