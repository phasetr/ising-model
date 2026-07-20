import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.PseudoMass.Ext
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# Regularity of concrete pseudo-mass beta profiles (1/5): pointwise regularity

Structural split (1/5) of
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`.
This child holds the pointwise `ContinuousAt` and `DifferentiableAt` statements for the
concrete `pseudoMassFromParamsAtPair` beta profile, transported through `pseudoMassExt` from
regularity of the underlying infinite correlation profile plus active-range membership,
together with the MVT-ready `HasDerivAt … (deriv …)` shape.  See the
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`
facade module for the full contents overview.
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

end Ambient

end IsingModel
