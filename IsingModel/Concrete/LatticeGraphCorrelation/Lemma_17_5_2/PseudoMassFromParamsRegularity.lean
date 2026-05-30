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

/-- **Concrete pseudo-mass beta derivative formula**: once the infinite
correlation beta profile is differentiable and lies in the active range, the
concrete pseudo-mass profile satisfies the implicit derivative formula coming
from `pseudoMassG(m⁻) = correlationInfinite`. -/
theorem pseudoMassFromParamsAtPair_beta_deriv_formula_of_corr_hasDerivAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β c' : ℝ}
    (hc_deriv :
      HasDerivAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        c' β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    deriv
        (fun β' =>
          pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
        β =
      c' /
        ((-2 * r *
              Real.exp
                (-(pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) *
              (1 +
                (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) -
            2 *
              Real.exp
                (-(pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) *
              (↑α *
                (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ (α - 1) *
                  r)) /
          (1 +
              (pseudoMassFromParamsAtPair hα hr d Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) ^
            2) := by
  let h : ℝ → ℝ := fun β' =>
    pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) x z
  let c : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hh_deriv : HasDerivAt h (deriv h β) β := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt
        hα hr Λ J x z hc_deriv.differentiableAt hcorr
  have hh_nonneg : 0 ≤ h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_nonneg hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_continuousAt
        hα hr Λ J x z hc_deriv.continuousAt hcorr
  have hh_pos : 0 < h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr
  have hformula := pseudoMass_deriv_formula α hr hh_deriv
    (by simpa [c] using hc_deriv) hh_nonneg hg_eq hh_pos
  simpa [h] using hformula

/-- **Concrete pseudo-mass beta power-derivative bound**: an HLS-style
absolute derivative bound for the infinite correlation profile transfers to
the concrete pseudo-mass beta profile as
`(m⁻ β)^(2α) * |deriv m⁻ β| ≤ K / r`. -/
theorem pseudoMassFromParamsAtPair_beta_power_deriv_le_of_corr_hasDerivAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β c' K : ℝ}
    (hc_deriv :
      HasDerivAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        c' β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp :
      |c'| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) *
      |deriv
        (fun β' =>
          pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
        β| ≤ K / r := by
  let h : ℝ → ℝ := fun β' =>
    pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) x z
  let c : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hh_deriv : HasDerivAt h (deriv h β) β := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt
        hα hr Λ J x z hc_deriv.differentiableAt hcorr
  have hh_nonneg : 0 ≤ h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_nonneg hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_continuousAt
        hα hr Λ J x z hc_deriv.continuousAt hcorr
  have hh_pos : 0 < h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr
  have hc_pos : 0 < c β := by
    simpa [c] using hcorr.1
  have hpower := pseudoMass_power_deriv_le α hr hh_deriv
    (by simpa [c] using hc_deriv) hh_nonneg hg_eq hh_pos hc_pos
    (by simpa [h, c] using hcomp)
  simpa [h] using hpower

/-- **Concrete pseudo-mass beta power-chain derivative bound**: the concrete
profile `β ↦ (m⁻ β)^(2α+1)` has a derivative at `β` whose absolute value is
bounded by `(2α+1) * K / r` whenever the infinite correlation derivative
satisfies the HLS denominator comparison. -/
theorem pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_of_corr_hasDerivAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β c' K : ℝ}
    (hc_deriv :
      HasDerivAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        c' β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp :
      |c'| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' =>
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1))
        dval β ∧
      |dval| ≤ ↑(2 * α + 1) * K / r := by
  let h : ℝ → ℝ := fun β' =>
    pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) x z
  let c : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hh_deriv : HasDerivAt h (deriv h β) β := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt
        hα hr Λ J x z hc_deriv.differentiableAt hcorr
  have hh_nonneg : 0 ≤ h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_nonneg hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : (fun β' => pseudoMassG α r (h β')) =ᶠ[nhds β] c := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_continuousAt
        hα hr Λ J x z hc_deriv.continuousAt hcorr
  have hh_pos : 0 < h β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr
  have hc_pos : 0 < c β := by
    simpa [c] using hcorr.1
  simpa [h] using
    pseudoMass_pow_succ_deriv_bound α hr hh_deriv
      (by simpa [c] using hc_deriv) hh_nonneg hg_eq hh_pos hc_pos
      (by simpa [h, c] using hcomp)

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

/-- **Closed-interval concrete pseudo-mass beta derivative formula**: pointwise
differentiability of the infinite correlation profile and active-range
membership on a compact beta interval give the implicit derivative formula for
the concrete pseudo-mass profile at every point of the interval. -/
theorem pseudoMassFromParamsAtPair_beta_deriv_formula_on_Icc_of_corr_differentiableAt
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
      deriv
          (fun β' =>
            pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) x z)
          β =
        deriv
            (fun β' =>
              Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
            β /
          ((-2 * r *
                Real.exp
                  (-(pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) *
                (1 +
                  (pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) -
              2 *
                Real.exp
                  (-(pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) *
                (↑α *
                  (pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ (α - 1) *
                    r)) /
            (1 +
                (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) ^
              2) := by
  intro β hβ
  exact
    pseudoMassFromParamsAtPair_beta_deriv_formula_of_corr_hasDerivAt
      hα hr Λ J x z (hc_diff β hβ).hasDerivAt (hcorr β hβ)

/-- **Closed-interval concrete pseudo-mass power-chain derivative bound**:
pointwise differentiability of the infinite correlation profile, active-range
membership, and the HLS denominator comparison give the derivative bound for
`β ↦ (m⁻ β)^(2α+1)` at every point of the interval. -/
theorem
    pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_on_Icc_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ K : ℝ}
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    ∀ β ∈ Set.Icc β₁ β₂,
      ∃ dval : ℝ,
        HasDerivAt
          (fun β' =>
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1))
          dval β ∧
        |dval| ≤ ↑(2 * α + 1) * K / r := by
  intro β hβ
  exact
    pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_of_corr_hasDerivAt
      hα hr Λ J x z (hc_diff β hβ).hasDerivAt (hcorr β hβ) (hcomp β hβ)

/-- **Closed-interval concrete pseudo-mass power-chain Lipschitz bound**:
pointwise differentiability of the infinite correlation profile, active-range
membership, and the HLS denominator comparison imply the interval Lipschitz
estimate for `β ↦ (m⁻ β)^(2α+1)`. -/
theorem
    pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ K : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    |(pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁) := by
  let h : ℝ → ℝ := fun β =>
    pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  let c : ℝ → ℝ := fun β =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
  have hh_diff : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β) β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_on_Icc_of_corr_differentiableAt
        hα hr Λ J x z hc_diff hcorr
  have hc_deriv : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt c (deriv c β) β := by
    intro β hβ
    exact (hc_diff β hβ).hasDerivAt
  have hh_nonneg : ∀ β ∈ Set.Icc β₁ β₂, 0 ≤ h β := by
    intro β _hβ
    exact pseudoMassFromParamsAtPair_nonneg hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : ∀ β ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α r (h γ)) =ᶠ[nhds β] c := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_on_Icc_of_corr_continuousAt
        hα hr Λ J x z
        (fun β hβ => (hc_diff β hβ).continuousAt) hcorr
  have hh_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < h β := by
    intro β hβ
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z (hcorr β hβ)
  have hc_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < c β := by
    intro β hβ
    exact (hcorr β hβ).1
  have hcomp' : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv c β| ≤ K * c β / (h β) ^ (2 * α) := by
    intro β hβ
    simpa [h, c] using hcomp β hβ
  simpa [h, c] using
    pseudoMass_pow_succ_lipschitz α hr hβ₁₂
      hh_diff hc_deriv hh_nonneg hg_eq hh_pos hc_pos hcomp'

/-- **GJ §17.5 Theorem 17.5.1 proof骨子: `m⁻(σ, A)^(2α+1)` is Lipschitz continuous in σ
A-uniformly** (GJ §17.5 pp. 311–312).

Glimm–Jaffe proves Theorem 17.5.1 ("The mass `m(σ)` in (17.5.1) is continuous as a function
of σ.") via the intermediate Lipschitz claim: `m⁻(σ, A)^(2α+1)` is Lipschitz continuous in
σ with a constant *uniform in both σ and A*. This is then combined with Lemma 17.5.2's
sandwich `0 ≤ m⁻ ≤ m ≤ const · m⁻` to conclude continuity of `m`.

This wrapper provides the Lipschitz claim under the GJ-aligned name and is a thin alias
of `pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt`
(which gives the same claim using the concrete profile name).

The Lipschitz constant is `(2α + 1) · K / r`, where `K` is the HLS denominator comparison
coefficient (the Lebowitz IIIb factor) and `r` is the radius parameter of `pseudoMass`. The
constant is A-uniform because both `K` and `r` are.

Direct correspondence to GJ p.312:

* `dm⁻/dσ`-formula step →
  `pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt`.
* Lebowitz IIIb (Cor 4.3.3) bounding the 4-point function → hypothesis `hcomp`
  `|c'| ≤ K · c / m⁻^(2α)` (caller-supplied; concrete Lebowitz application).
* Algebraic chain `m⁻^(2α) · dm⁻/dσ ≤ const` → built into the `_pow_succ_deriv_bound_*`
  helper.
* MVT integration over `[β₁, β₂]` → done inside the existing Lipschitz wrapper.

This is the **m⁻-derivative analysis section** of GJ's Theorem 17.5.1 proof in the Lean
formalization. It does NOT yet deliver Theorem 17.5.1 itself (continuity of `m`); that
requires combining with Lemma 17.5.2's sandwich and `pseudoMass` extension to `σ < σ_c`. -/
theorem gj_theorem_17_5_1_pseudoMass_pow_succ_lipschitz_on_Icc
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ K : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    |(pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁) :=
  pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    hα hr Λ J x z hβ₁₂ hc_diff hcorr hcomp

end Ambient

end IsingModel
