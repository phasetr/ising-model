import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.PseudoMass.Basic
import IsingModel.PseudoMass.Profile
import IsingModel.PseudoMass.Lipschitz
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsLocalEq
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.PointwiseRegularity

/-!
# Regularity of concrete pseudo-mass beta profiles (2/5): pointwise derivative bounds

Structural split (2/5) of
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`.
This child holds the implicit derivative formula coming from
`pseudoMassG (m⁻ β) = correlationInfinite β`, the HLS power-derivative bound
`(m⁻)^(2α) · |deriv m⁻| ≤ K / r`, and the power-chain derivative bound for
`β ↦ (m⁻ β) ^ (2α + 1)`.  See the
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`
facade module for the full contents overview.
-/

namespace IsingModel

open Set

namespace Ambient

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

end Ambient

end IsingModel
