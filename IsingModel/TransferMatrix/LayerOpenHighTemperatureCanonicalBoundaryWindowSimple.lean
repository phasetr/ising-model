import IsingModel.TransferMatrix.LayerOpenHighTemperatureBoundaryWindowSimple

/-!
# Canonical high-temperature boundary-window simple-parity consumers

This file specializes the local high-temperature boundary-window route to the
canonical max-index decay parameter
`RealOrthogonalSpectralData.subdominantRatio_maxEigenIndex`.  The strict
infinite-temperature seed is proved from the existing physical norm-window seed
and the physical-to-boundary cap bridge, so downstream users only provide
scalar continuity for the canonical ratio and boundary cap and local
`ColumnSimpleEigenspaces` input on the punctured high-temperature side.

The results remain finite and conditional.  They do not prove spectral-data
continuity, perturbative stability of the selected spectral data, local
simple-eigenspace hypotheses for a concrete interacting family, a concrete
interacting cubic-layer spectral window, a thermodynamic limit, or final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Filter
open scoped Topology

/-! ## Local interval helpers -/

/-- An eventual punctured property near `0` contains a punctured
absolute-value neighborhood. -/
private theorem exists_pos_punctured_abs_lt_of_eventually_nhds_zero_canonical
    {P : ℝ → Prop} (hP : ∀ᶠ β in 𝓝 0, β ≠ 0 → P β) :
    ∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε → P β := by
  rw [Metric.eventually_nhds_iff] at hP
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun β hβ_ne hβ => hball (y := β) ?_ ?_⟩
  · simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using hβ
  · exact abs_pos.mp hβ_ne

/-- A positive closed one-sided interval and a positive punctured one-sided
interval contain a common positive punctured one-sided subinterval. -/
private theorem exists_pos_Ioc_subset_Icc_Ioc
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c > 0, ∀ β : ℝ, β ∈ Set.Ioc 0 c →
      β ∈ Set.Icc 0 a ∧ β ∈ Set.Ioc 0 b := by
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro β hβ
  exact
    ⟨⟨le_of_lt hβ.1, le_trans hβ.2 (min_le_left a b)⟩,
      ⟨hβ.1, le_trans hβ.2 (min_le_right a b)⟩⟩

/-- A positive closed one-sided interval and a positive punctured
absolute-value neighborhood contain a common positive punctured one-sided
subinterval. -/
private theorem exists_pos_Ioc_subset_Icc_punctured_abs
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ c > 0, ∀ β : ℝ, β ∈ Set.Ioc 0 c →
      β ∈ Set.Icc 0 a ∧ 0 < |β| ∧ |β| < ε := by
  refine ⟨min a (ε / 2), lt_min ha (by positivity), ?_⟩
  intro β hβ
  have hβ_le_a : β ≤ a := le_trans hβ.2 (min_le_left a (ε / 2))
  have hβ_le_ε : β ≤ ε / 2 := le_trans hβ.2 (min_le_right a (ε / 2))
  have hβ_abs : |β| = β := abs_of_nonneg (le_of_lt hβ.1)
  exact
    ⟨⟨le_of_lt hβ.1, hβ_le_a⟩, by simpa [hβ_abs] using hβ.1,
      by rw [hβ_abs]; linarith⟩

/-! ## Canonical boundary-window scalar bridges -/

/-- At `β = 0`, the canonical max-index ratio is strictly below the open
boundary spectral-window cap. -/
theorem subdominantRatioMax_lt_layerOpenBoundaryWindowCap_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hpβ : p.β = 0)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p))) :
    spec.subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
      <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec spec.maxEigenIndex := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_physicalNormWindowCap
      H transitionPairs p spec spec.maxEigenIndex
      (spec.signedPositiveColumn_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      (subdominantRatioMax_lt_layerOpenPhysicalNormCap_beta_zero
        H transitionPairs p hpβ spec)

/-- Cubic specialization of the beta-zero canonical boundary-window seed. -/
theorem cubic_subdominantRatioMax_lt_openBoundaryWindowCap_beta_zero
    (d R : ℕ) (p : IsingParams ℝ) (hpβ : p.β = 0)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p))) :
    spec.subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight (cubicLayerGraph d R) p)
          (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
      <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p) spec spec.maxEigenIndex :=
  subdominantRatioMax_lt_layerOpenBoundaryWindowCap_beta_zero
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hpβ spec

/-- The beta-zero canonical boundary-window inequality persists eventually
under scalar continuity of the canonical ratio and boundary cap. -/
theorem eventually_subdominantRatioMax_lt_openBoundaryWindowCap_of_continuousAt_beta_zero
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ᶠ β in 𝓝 0, ratio β < cap β := by
  intro ratio cap hratio hcap
  have hseed : ratio 0 < cap 0 := by
    simpa [ratio, cap] using
      (subdominantRatioMax_lt_layerOpenBoundaryWindowCap_beta_zero
        H transitionPairs ({ p with β := 0 } : IsingParams ℝ) rfl (spec 0))
  exact
    eventually_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec (fun β => (spec β).maxEigenIndex) ratio
      hratio hcap hseed

/-- The beta-zero canonical boundary-window inequality persists on an
absolute-value neighborhood under scalar continuity. -/
theorem exists_pos_abs_lt_subdominantRatioMax_lt_openBoundaryWindowCap_of_continuousAt_beta_zero
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∃ ε > 0, ∀ β : ℝ, |β| < ε → ratio β < cap β := by
  intro ratio cap hratio hcap
  have hseed : ratio 0 < cap 0 := by
    simpa [ratio, cap] using
      (subdominantRatioMax_lt_layerOpenBoundaryWindowCap_beta_zero
        H transitionPairs ({ p with β := 0 } : IsingParams ℝ) rfl (spec 0))
  exact
    exists_pos_abs_lt_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec (fun β => (spec β).maxEigenIndex) ratio
      hratio hcap hseed

/-- The beta-zero canonical boundary-window inequality persists on a positive
closed one-sided high-temperature interval under scalar continuity. -/
theorem exists_pos_Icc_subdominantRatioMax_lt_openBoundaryWindowCap_of_continuousAt_beta_zero
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → ratio β < cap β := by
  intro ratio cap hratio hcap
  have hseed : ratio 0 < cap 0 := by
    simpa [ratio, cap] using
      (subdominantRatioMax_lt_layerOpenBoundaryWindowCap_beta_zero
        H transitionPairs ({ p with β := 0 } : IsingParams ℝ) rfl (spec 0))
  exact
    exists_pos_Icc_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec (fun β => (spec β).maxEigenIndex) ratio
      hratio hcap hseed

/-! ## Local simple-parity canonical boundary-window consumers -/

/-- On any punctured one-sided interval where the canonical boundary-window
inequality and columnwise simple-eigenspace input hold, the max-index
simple-parity route gives a finite open spin-observable min-gap certificate at
each `β` in the interval. -/
noncomputable def layerOpenMinGapCert_of_Ioc_canonicalRatioBoundaryWindow_localSimpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (βmax : ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (hwindow :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        (spec β).subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
          <
            layerOpenBoundarySpectralWindowCap
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (spec β) (spec β).maxEigenIndex)
    (hsimple :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).ColumnSimpleEigenspaces)
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight transitionPairs ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParitySpin_boundaryWindow
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β)
      ((spec β).subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      ((spec β).subdominantRatio_maxEigenIndex_nonneg
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      (hwindow β hβ)
      ((spec β).eigenvalue_abs_le_subdominantRatio_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))
          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
      (hsimple β hβ)

/-- Under scalar continuity and local simple-eigenspace input on a punctured
one-sided interval, finite open-slab same-transverse-site decay holds on a
possibly smaller punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_IocSimpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ βlocal : ℝ, 0 < βlocal →
          (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
            (spec β).ColumnSimpleEigenspaces) →
            ∃ βmax > 0,
              ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
                ∀ x : S, ∀ left sep right : ℕ, 0 < sep →
                  |correlation
                    (layerOpenSlabGraph (S := S) H transitionPairs
                      (left + sep + right))
                    ({ p with β := β } : IsingParams ℝ)
                    ({Prod.mk (layerOpenLeftIndex left sep right) x,
                      Prod.mk (layerOpenRightIndex left sep right) x} :
                        Finset (LayerOpenSlabSite (left + sep + right) S))|
                  ≤
                    ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                      (layerOpenBalancedBoundaryVector
                        (layerInternalWeight H
                          ({ p with β := β } : IsingParams ℝ)))
                      (layerOpenBalancedBoundaryVector
                        (layerInternalWeight H
                          ({ p with β := β } : IsingParams ℝ))) /
                        (spec β).boundarySpectralPartitionPrefactor
                          (layerOpenBalancedBoundaryVector
                            (layerInternalWeight H
                              ({ p with β := β } : IsingParams ℝ)))
                          (spec β).maxEigenIndex (ratio β)) *
                      (ratio β) ^ sep := by
  intro ratio cap hratio hcap βlocal hβlocal hsimple
  rcases
    exists_pos_Icc_subdominantRatioMax_lt_openBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases exists_pos_Ioc_subset_Icc_Ioc hβwindow_pos hβlocal with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  letI : Nonempty (LayerState S) := ⟨default⟩
  rcases hsubset β hβ with ⟨hβ_window, hβ_simple⟩
  exact
    correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (ratio β)
      (by
        simpa [ratio] using
          ((spec β).subdominantRatio_maxEigenIndex_nonneg
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))))
      (by
        simpa [ratio, cap] using hwindow β hβ_window)
      (by
        simpa [ratio] using
          ((spec β).eigenvalue_abs_le_subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))))
      (hsimple β hβ_simple) left sep right hsep

/-- Under scalar continuity and local simple-eigenspace input on a punctured
absolute-value neighborhood, finite open-slab same-transverse-site decay holds
on a punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_absSimpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
          (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : S, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (layerOpenSlabGraph (S := S) H transitionPairs
                    (left + sep + right))
                  ({ p with β := β } : IsingParams ℝ)
                  ({Prod.mk (layerOpenLeftIndex left sep right) x,
                    Prod.mk (layerOpenRightIndex left sep right) x} :
                      Finset (LayerOpenSlabSite (left + sep + right) S))|
                ≤
                  ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight H
                        ({ p with β := β } : IsingParams ℝ)))
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight H
                        ({ p with β := β } : IsingParams ℝ))) /
                      (spec β).boundarySpectralPartitionPrefactor
                        (layerOpenBalancedBoundaryVector
                          (layerInternalWeight H
                            ({ p with β := β } : IsingParams ℝ)))
                        (spec β).maxEigenIndex (ratio β)) *
                    (ratio β) ^ sep := by
  intro ratio cap hratio hcap hsimple_abs
  rcases
    exists_pos_Icc_subdominantRatioMax_lt_openBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases hsimple_abs with ⟨εsimple, hεsimple_pos, hsimple⟩
  rcases exists_pos_Ioc_subset_Icc_punctured_abs hβwindow_pos hεsimple_pos with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  letI : Nonempty (LayerState S) := ⟨default⟩
  rcases hsubset β hβ with ⟨hβ_window, hβ_abs_pos, hβ_abs⟩
  exact
    correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (ratio β)
      (by
        simpa [ratio] using
          ((spec β).subdominantRatio_maxEigenIndex_nonneg
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))))
      (by
        simpa [ratio, cap] using hwindow β hβ_window)
      (by
        simpa [ratio] using
          ((spec β).eigenvalue_abs_le_subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))))
      (hsimple β hβ_abs_pos hβ_abs) left sep right hsep

/-- Under scalar continuity and local simple-eigenspace input eventually near
but away from `β = 0`, finite open-slab same-transverse-site decay holds on a
punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventuallySimpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : S, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (layerOpenSlabGraph (S := S) H transitionPairs
                    (left + sep + right))
                  ({ p with β := β } : IsingParams ℝ)
                  ({Prod.mk (layerOpenLeftIndex left sep right) x,
                    Prod.mk (layerOpenRightIndex left sep right) x} :
                      Finset (LayerOpenSlabSite (left + sep + right) S))|
                ≤
                  ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight H
                        ({ p with β := β } : IsingParams ℝ)))
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight H
                        ({ p with β := β } : IsingParams ℝ))) /
                      (spec β).boundarySpectralPartitionPrefactor
                        (layerOpenBalancedBoundaryVector
                          (layerInternalWeight H
                            ({ p with β := β } : IsingParams ℝ)))
                        (spec β).maxEigenIndex (ratio β)) *
                    (ratio β) ^ sep := by
  intro ratio cap hratio hcap hsimple_eventually
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_absSimpleParity
      H transitionPairs p hp spec hratio hcap
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_canonical
        hsimple_eventually)

/-! ## Cubic local simple-parity canonical boundary-window consumers -/

/-- Cubic specialization of the pointwise canonical-ratio boundary-window
local simple-parity certificate constructor. -/
noncomputable def cubicLayerOpenMinGapCert_of_Ioc_canonicalRatioBoundaryWindow_localSimpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (βmax : ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (hwindow :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        (spec β).subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight (cubicLayerGraph d R)
                ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight (cubicLayerTransitionPairs d R)
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
          <
            layerOpenBoundarySpectralWindowCap
              (layerInternalWeight (cubicLayerGraph d R)
                ({ p with β := β } : IsingParams ℝ))
              (spec β) (spec β).maxEigenIndex)
    (hsimple :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).ColumnSimpleEigenspaces)
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : CubicLayerSite d R) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight (cubicLayerTransitionPairs d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_Ioc_canonicalRatioBoundaryWindow_localSimpleParity
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp βmax spec
    hwindow hsimple β hβ x

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_IocSimpleParity`. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_IocSimpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ βlocal : ℝ, 0 < βlocal →
          (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
            (spec β).ColumnSimpleEigenspaces) →
            ∃ βmax > 0,
              ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
                ∀ x : CubicLayerSite d R, ∀ left sep right : ℕ, 0 < sep →
                  |correlation
                    (cubicLayerOpenSlabGraph d R (left + sep + right))
                    ({ p with β := β } : IsingParams ℝ)
                    ({Prod.mk (layerOpenLeftIndex left sep right) x,
                      Prod.mk (layerOpenRightIndex left sep right) x} :
                        Finset
                          (LayerOpenSlabSite
                            (left + sep + right) (CubicLayerSite d R)))|
                  ≤
                    ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                      (layerOpenBalancedBoundaryVector
                        (layerInternalWeight (cubicLayerGraph d R)
                          ({ p with β := β } : IsingParams ℝ)))
                      (layerOpenBalancedBoundaryVector
                        (layerInternalWeight (cubicLayerGraph d R)
                          ({ p with β := β } : IsingParams ℝ))) /
                        (spec β).boundarySpectralPartitionPrefactor
                          (layerOpenBalancedBoundaryVector
                            (layerInternalWeight (cubicLayerGraph d R)
                              ({ p with β := β } : IsingParams ℝ)))
                          (spec β).maxEigenIndex (ratio β)) *
                      (ratio β) ^ sep := by
  intro ratio cap hratio hcap βlocal hβlocal hsimple
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_IocSimpleParity
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec
      hratio hcap βlocal hβlocal hsimple with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_absSimpleParity`. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_absSimpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
          (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : CubicLayerSite d R, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (cubicLayerOpenSlabGraph d R (left + sep + right))
                  ({ p with β := β } : IsingParams ℝ)
                  ({Prod.mk (layerOpenLeftIndex left sep right) x,
                    Prod.mk (layerOpenRightIndex left sep right) x} :
                      Finset
                        (LayerOpenSlabSite
                          (left + sep + right) (CubicLayerSite d R)))|
                ≤
                  ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight (cubicLayerGraph d R)
                        ({ p with β := β } : IsingParams ℝ)))
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight (cubicLayerGraph d R)
                        ({ p with β := β } : IsingParams ℝ))) /
                      (spec β).boundarySpectralPartitionPrefactor
                        (layerOpenBalancedBoundaryVector
                          (layerInternalWeight (cubicLayerGraph d R)
                            ({ p with β := β } : IsingParams ℝ)))
                        (spec β).maxEigenIndex (ratio β)) *
                    (ratio β) ^ sep := by
  intro ratio cap hratio hcap hsimple_abs
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalRatioBoundaryWindow_absSimpleParity
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec
      hratio hcap hsimple_abs with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventuallySimpleParity`. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventuallySimple
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
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
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : CubicLayerSite d R, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (cubicLayerOpenSlabGraph d R (left + sep + right))
                  ({ p with β := β } : IsingParams ℝ)
                  ({Prod.mk (layerOpenLeftIndex left sep right) x,
                    Prod.mk (layerOpenRightIndex left sep right) x} :
                      Finset
                        (LayerOpenSlabSite
                          (left + sep + right) (CubicLayerSite d R)))|
                ≤
                  ((spec β).boundaryMarkedSpectralPrefactor (layerSpinAt x)
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight (cubicLayerGraph d R)
                        ({ p with β := β } : IsingParams ℝ)))
                    (layerOpenBalancedBoundaryVector
                      (layerInternalWeight (cubicLayerGraph d R)
                        ({ p with β := β } : IsingParams ℝ))) /
                      (spec β).boundarySpectralPartitionPrefactor
                        (layerOpenBalancedBoundaryVector
                          (layerInternalWeight (cubicLayerGraph d R)
                            ({ p with β := β } : IsingParams ℝ)))
                        (spec β).maxEigenIndex (ratio β)) *
                    (ratio β) ^ sep := by
  intro ratio cap hratio hcap hsimple_eventually
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventuallySimpleParity
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec
      hratio hcap hsimple_eventually with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

end TransferMatrix

end IsingModel
