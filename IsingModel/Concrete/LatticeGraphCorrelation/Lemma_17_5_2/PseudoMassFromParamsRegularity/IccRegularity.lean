import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.PointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.PointwiseDerivBounds

/-!
# Regularity of concrete pseudo-mass beta profiles (3/5): closed-interval versions

Structural split (3/5) of
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`.
This child holds the closed-interval (`Set.Icc β₁ β₂`) versions of the pointwise regularity
package: `ContinuousOn`, the pointwise `HasDerivAt` statement on the interval, the derivative
formula on the interval, and the power-chain derivative bound on the interval.  See the
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`
facade module for the full contents overview.
-/

namespace IsingModel

open Set

namespace Ambient

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

end Ambient

end IsingModel
