import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsLocalEq

/-!
# Regularity of concrete pseudo-mass beta profiles

This module packages the continuity and differentiability inputs for the
concrete `pseudoMassFromParamsAtPair` beta profile.  These wrappers let callers
feed the localized Lemma 17.5.2 MVT/Lipschitz APIs using regularity of the
underlying infinite correlation profile plus active-range membership.
-/

namespace IsingModel

open Set

namespace Ambient

/-- **Concrete pseudo-mass beta profile is continuous at a point**:
continuity of the infinite correlation profile and active-range membership
transport through `pseudoMassExt`. -/
theorem pseudoMassFromParamsAtPair_beta_continuousAt_of_corr_continuousAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β : ℝ}
    (hc_cont :
      ContinuousAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    ContinuousAt
      (fun β' =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
      β := by
  have hpm_cont :
      ContinuousAt (pseudoMassExt hα hr)
        (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :=
    pseudoMassExt_continuousAt hα hr hcorr
  change ContinuousAt
    ((pseudoMassExt hα hr) ∘
      (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})) β
  exact ContinuousAt.comp
    (f := fun β' =>
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (g := pseudoMassExt hα hr) hpm_cont hc_cont

/-- **Concrete pseudo-mass beta profile is differentiable at a point**:
differentiability of the infinite correlation profile and active-range
membership transport through `pseudoMassExt`. -/
theorem pseudoMassFromParamsAtPair_beta_differentiableAt_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β : ℝ}
    (hc_diff :
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    DifferentiableAt ℝ
      (fun β' =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
      β := by
  have hpm_diff :
      DifferentiableAt ℝ (pseudoMassExt hα hr)
        (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :=
    pseudoMassExt_differentiableAt hα hr hcorr
  change DifferentiableAt ℝ
    ((pseudoMassExt hα hr) ∘
      (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})) β
  exact DifferentiableAt.comp
    (f := fun β' =>
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (g := pseudoMassExt hα hr) β hpm_diff hc_diff

/-- **MVT-ready derivative statement for the concrete pseudo-mass beta
profile**: the differentiability wrapper gives the exact `HasDerivAt ... (deriv
...)` shape required by the localized pseudo-mass Lipschitz theorem. -/
theorem pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β : ℝ}
    (hc_diff :
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt
      (fun β' =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
      (deriv (fun β' =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z) β)
      β :=
  (pseudoMassFromParamsAtPair_beta_differentiableAt_of_corr_differentiableAt
    hα hr Λ J x z hc_diff hcorr).hasDerivAt

/-- **Concrete pseudo-mass beta profile is continuous on a closed interval**:
pointwise `ContinuousAt` of the infinite correlation profile and active-range
membership give the `ContinuousOn` denominator input used by the compact
ratio-bounds package. -/
theorem pseudoMassFromParamsAtPair_beta_continuousOn_Icc_of_corr_continuousAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hc_cont : ∀ β ∈ Set.Icc β₁ β₂,
      ContinuousAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    ContinuousOn
      (fun β =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      (Set.Icc β₁ β₂) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_beta_continuousAt_of_corr_continuousAt
    hα hr Λ J x z (hc_cont β hβ) (hcorr β hβ)).continuousWithinAt

/-- **Closed-interval MVT-ready derivative package for the concrete pseudo-mass
beta profile**: pointwise differentiability of the infinite correlation profile
and active-range membership give the derivative input required by
`pseudoMass_pow_succ_lipschitz`. -/
theorem pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_on_Icc_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    ∀ β ∈ Set.Icc β₁ β₂,
      HasDerivAt
        (fun β' =>
          pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
        (deriv (fun β' =>
          pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z) β)
        β := by
  intro β hβ
  exact pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt
    hα hr Λ J x z (hc_diff β hβ) (hcorr β hβ)

end Ambient

end IsingModel
