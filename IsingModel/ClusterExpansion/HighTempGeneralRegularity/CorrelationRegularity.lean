import IsingModel.ClusterExpansion.HighTempGeneralRegularity.FreeEnergyAnalyticity

/-!
# High-temperature correlation regularity

Mechanical child split from `ClusterExpansion.HighTempGeneralRegularity`.
-/

namespace IsingModel

open Finset
/-- **Numerator of correlation function jointly `AnalyticAt ℝ` in
`(β, J, h)`**: the unnormalised expectation
`∑_σ spinProduct A σ · boltzmannWeight G p σ`, viewed as a function
of `(β, J, h)`, is real-analytic jointly. Each summand is
`(constant in (β, J, h)) · exp(polynomial in (β, J, h))`. -/
theorem correlation_numerator_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ =>
        ∑ σ : Config ι, spinProduct A σ *
          boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ)
      (β, J, h) := by
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      ∑ σ : Config ι, spinProduct A σ *
        boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι, spinProduct A σ *
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
  -- Linear combination of polynomials in (β, J, h).
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **Correlation function jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
extension): for any spin subset `A` and any `(β, J, h)`,
`⟨σ_A⟩ = (∑_σ σ_A · exp(-β·H)) / Z` is real-analytic jointly in all
three Ising parameters.

Proof: `correlation = (1/Z) · numerator`, both `Z` and `numerator` are
jointly analytic (PR #1531 + helper above), and `Z > 0` lets us apply
`AnalyticAt.inv` for the reciprocal. -/
theorem correlation_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A)
      (β, J, h) := by
  unfold correlation gibbsExpectation
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
  exact h_inv.mul (correlation_numerator_analyticAt_joint G A β J h)

/-- **Correlation function jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 extension): global form of `correlation_analyticAt_joint`. -/
theorem correlation_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => correlation_analyticAt_joint G A β J h

/-- **Correlation function jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary). -/
theorem correlation_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    Continuous (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (correlation_analyticAt_joint G A β J h).continuousAt

/-- **Correlation function jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6, direct corollary). -/
theorem correlation_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A) :=
  fun ⟨β, J, h⟩ => (correlation_analyticAt_joint G A β J h).differentiableAt

end IsingModel
