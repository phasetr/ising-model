import IsingModel.TransferMatrix.LayerOpenInfiniteTemperatureNormWindow

/-!
# High-temperature open physical norm-window bridges

This file turns the strict infinite-temperature physical open norm-window
inequality into a finite high-temperature bridge under explicit scalar
continuity hypotheses.  If the chosen spectral-data family's canonical
max-index ratio and physical norm-window cap both tend to their beta-zero
values, then the strict inequality proved at `β = 0` persists in a small
one-sided interval `0 ≤ β ≤ βmax`.

The results are finite and conditional.  They do not prove continuity of a
Hermitian spectral-theorem eigenbasis, stability of `maxEigenIndex`, a concrete
interacting cubic-layer spectral window, parity adaptation, a thermodynamic
limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Filter
open scoped Topology

/-! ## Topological strict-inequality helpers -/

/-- A strict inequality at `0` persists eventually if both sides tend to their
values at `0`. -/
private theorem eventually_lt_of_tendsto_at_zero
    {f g : ℝ → ℝ} (hf : Tendsto f (𝓝 0) (𝓝 (f 0)))
    (hg : Tendsto g (𝓝 0) (𝓝 (g 0))) (h0 : f 0 < g 0) :
    ∀ᶠ β in 𝓝 0, f β < g β :=
  hf.eventually_lt hg h0

/-- An eventual property near `0` contains an absolute-value neighborhood. -/
private theorem exists_pos_abs_lt_of_eventually_nhds_zero
    {P : ℝ → Prop} (hP : ∀ᶠ β in 𝓝 0, P β) :
    ∃ ε > 0, ∀ β : ℝ, |β| < ε → P β := by
  rw [Metric.eventually_nhds_iff] at hP
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun β hβ => hball (y := β) ?_⟩
  simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using hβ

/-- An absolute-value neighborhood of `0` contains a one-sided interval
`0 ≤ β ≤ βmax` for some positive `βmax`. -/
private theorem exists_pos_Icc_of_abs_neighborhood
    {P : ℝ → Prop} (hP : ∃ ε > 0, ∀ β : ℝ, |β| < ε → P β) :
    ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → P β := by
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, by positivity, fun β hβ => hball β ?_⟩
  rcases hβ with ⟨hβ_nonneg, hβ_le⟩
  rw [abs_of_nonneg hβ_nonneg]
  linarith

/-! ## Generic finite physical high-temperature bridge -/

/-- Under explicit scalar continuity hypotheses for a chosen finite spectral
data family, the beta-zero physical norm-window inequality persists eventually
near `β = 0`. -/
theorem eventually_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ)))) :
    let ratio : ℝ → ℝ := fun β =>
      (spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
    let cap : ℝ → ℝ := fun β =>
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    Tendsto ratio (𝓝 0) (𝓝 (ratio 0)) →
      Tendsto cap (𝓝 0) (𝓝 (cap 0)) →
        ∀ᶠ β in 𝓝 0, ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    eventually_lt_of_tendsto_at_zero hratio hcap
      (subdominantRatioMax_lt_layerOpenPhysicalNormCap_beta_zero
        H transitionPairs ({ p with β := 0 } : IsingParams ℝ) rfl (spec 0))

/-- Under explicit scalar continuity hypotheses for a chosen finite spectral
data family, the physical norm-window inequality holds on an absolute-value
neighborhood of `β = 0`. -/
theorem
    exists_pos_abs_lt_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ)))) :
    let ratio : ℝ → ℝ := fun β =>
      (spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
    let cap : ℝ → ℝ := fun β =>
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    Tendsto ratio (𝓝 0) (𝓝 (ratio 0)) →
      Tendsto cap (𝓝 0) (𝓝 (cap 0)) →
        ∃ ε > 0, ∀ β : ℝ, |β| < ε → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_abs_lt_of_eventually_nhds_zero
      (eventually_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
        H transitionPairs p spec hratio hcap)

/-- Under explicit scalar continuity hypotheses for a chosen finite spectral
data family, the physical norm-window inequality holds on a one-sided
high-temperature interval `0 ≤ β ≤ βmax`. -/
theorem
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ)))) :
    let ratio : ℝ → ℝ := fun β =>
      (spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
    let cap : ℝ → ℝ := fun β =>
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    Tendsto ratio (𝓝 0) (𝓝 (ratio 0)) →
      Tendsto cap (𝓝 0) (𝓝 (cap 0)) →
        ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_Icc_of_abs_neighborhood
      (exists_pos_abs_lt_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
        H transitionPairs p spec hratio hcap)

/-! ## Cubic specializations -/

/-- Cubic specialization of the eventual finite high-temperature physical
norm-window bridge. -/
theorem
    eventually_cubic_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
    (d R : ℕ) (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ)))) :
    let ratio : ℝ → ℝ := fun β =>
      (spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
    let cap : ℝ → ℝ := fun β =>
      cubicLayerOpenPhysicalBoundaryNormWindowCap
        d R ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    Tendsto ratio (𝓝 0) (𝓝 (ratio 0)) →
      Tendsto cap (𝓝 0) (𝓝 (cap 0)) →
        ∀ᶠ β in 𝓝 0, ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    eventually_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p spec hratio hcap

/-- Cubic specialization of the one-sided finite high-temperature physical
norm-window bridge. -/
theorem
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
    (d R : ℕ) (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ)))) :
    let ratio : ℝ → ℝ := fun β =>
      (spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
    let cap : ℝ → ℝ := fun β =>
      cubicLayerOpenPhysicalBoundaryNormWindowCap
        d R ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    Tendsto ratio (𝓝 0) (𝓝 (ratio 0)) →
      Tendsto cap (𝓝 0) (𝓝 (cap 0)) →
        ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p spec hratio hcap

end TransferMatrix

end IsingModel
