import IsingModel.TransferMatrix.LayerOpenHighTemperatureSimpleParity

/-!
# Local high-temperature open simple-parity consumers

This file weakens the global simple-eigenspace input in the high-temperature
simple-parity physical norm-window consumers to local high-temperature inputs.
If the physical norm-window inequality holds on a high-temperature interval and
the chosen spectral-data family has columnwise simple eigenspaces on a local
punctured one-sided interval, on a punctured absolute-value neighborhood, or
eventually near but away from `β = 0`, then the same finite open-slab and cubic
open-slab conclusions hold on a smaller punctured one-sided interval.

The results remain finite and conditional.  They do not prove continuity of
spectral-theorem data, eigenbasis perturbation, stability of `maxEigenIndex`,
columnwise simple eigenspaces, a concrete interacting cubic-layer spectral
window, a thermodynamic limit, or final hyperplane exponential decay.

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
private theorem exists_pos_punctured_abs_lt_of_eventually_nhds_zero_local
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

/-- A positive one-sided interval and a positive punctured absolute-value
neighborhood contain a common positive punctured one-sided subinterval. -/
private theorem exists_pos_Ioc_subset_Icc_punctured_abs
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ c > 0, ∀ β : ℝ, β ∈ Set.Ioc 0 c →
      β ∈ Set.Icc 0 a ∧ 0 < |β| ∧ |β| < ε := by
  refine ⟨min a (ε / 2), lt_min ha (by positivity), ?_⟩
  intro β hβ
  have hβ_le_a : β ≤ a := le_trans hβ.2 (min_le_left a (ε / 2))
  have hβ_le_half : β ≤ ε / 2 := le_trans hβ.2 (min_le_right a (ε / 2))
  refine ⟨⟨le_of_lt hβ.1, hβ_le_a⟩, ?_⟩
  have hβ_abs : |β| = β := abs_of_nonneg (le_of_lt hβ.1)
  constructor
  · simpa [hβ_abs] using hβ.1
  · rw [hβ_abs]
    linarith

/-! ## Local simple-parity consumers on high-temperature intervals -/

/-- On any interval where the physical norm-window inequality and columnwise
simple eigenspaces both hold, the existing simple-parity physical route gives a
finite open spin-observable min-gap certificate at each `β` in the interval. -/
noncomputable def
    layerOpenMinGapCert_of_Ioc_physicalNormWindow_localSimpleParity
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
      ∀ β : ℝ, β ∈ Set.Icc 0 βmax →
        (spec β).subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight transitionPairs
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
          <
            layerOpenPhysicalBoundaryNormWindowCap
              H transitionPairs ({ p with β := β } : IsingParams ℝ)
              (spec β) (spec β).maxEigenIndex)
    (hsimple :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).ColumnSimpleEigenspaces)
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight transitionPairs ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParityCanonicalRatioPhysicalNormWindow
    H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp) x
    (spec β) (hwindow β ⟨le_of_lt hβ.1, hβ.2⟩) (hsimple β hβ)

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces on
a punctured one-sided interval, finite open-slab same-transverse-site decay
holds on a possibly smaller punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_physicalNormWindow_IocSimpleParity
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
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ βsimple : ℝ, 0 < βsimple →
          (∀ β : ℝ, β ∈ Set.Ioc 0 βsimple →
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
                            (spec β).maxEigenIndex
                            ((spec β).subdominantRatio_maxEigenIndex
                              (layerSymmetricTransferMatrix_entrywisePositive
                                (layerInternalWeight H
                                  ({ p with β := β } : IsingParams ℝ))
                                (layerTransitionWeight transitionPairs
                                  ({ p with β := β } : IsingParams ℝ))
                                (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                        ((spec β).subdominantRatio_maxEigenIndex
                          (layerSymmetricTransferMatrix_entrywisePositive
                            (layerInternalWeight H
                              ({ p with β := β } : IsingParams ℝ))
                            (layerTransitionWeight transitionPairs
                              ({ p with β := β } : IsingParams ℝ))
                            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^
                          sep := by
  intro ratio cap hratio hcap βsimple hβsimple hsimple
  rcases
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      H transitionPairs p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases exists_pos_Ioc_subset_Icc_Ioc hβwindow_pos hβsimple with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with ⟨hβ_window, hβ_simple⟩
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ_window) (hsimple β hβ_simple) left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces on
a punctured absolute-value neighborhood, finite open-slab same-transverse-site
decay holds on a punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_physicalNormWindow_absSimpleParity
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
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
          (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : S, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right))
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
                          (spec β).maxEigenIndex
                          ((spec β).subdominantRatio_maxEigenIndex
                            (layerSymmetricTransferMatrix_entrywisePositive
                              (layerInternalWeight H
                                ({ p with β := β } : IsingParams ℝ))
                              (layerTransitionWeight transitionPairs
                                ({ p with β := β } : IsingParams ℝ))
                              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                      ((spec β).subdominantRatio_maxEigenIndex
                        (layerSymmetricTransferMatrix_entrywisePositive
                          (layerInternalWeight H
                            ({ p with β := β } : IsingParams ℝ))
                          (layerTransitionWeight transitionPairs
                            ({ p with β := β } : IsingParams ℝ))
                          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  intro ratio cap hratio hcap hsimple_abs
  rcases
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      H transitionPairs p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases hsimple_abs with ⟨ε, hε_pos, hsimple⟩
  rcases exists_pos_Ioc_subset_Icc_punctured_abs hβwindow_pos hε_pos with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with ⟨hβ_window, hβ_abs_pos, hβ_abs⟩
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ_window) (hsimple β hβ_abs_pos hβ_abs)
      left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces
eventually near but away from `β = 0`, finite open-slab same-transverse-site
decay holds on a punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_physicalNormWindow_eventuallySimpleParity
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
      layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
              ∀ x : S, ∀ left sep right : ℕ, 0 < sep →
                |correlation
                  (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right))
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
                          (spec β).maxEigenIndex
                          ((spec β).subdominantRatio_maxEigenIndex
                            (layerSymmetricTransferMatrix_entrywisePositive
                              (layerInternalWeight H
                                ({ p with β := β } : IsingParams ℝ))
                              (layerTransitionWeight transitionPairs
                                ({ p with β := β } : IsingParams ℝ))
                              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                      ((spec β).subdominantRatio_maxEigenIndex
                        (layerSymmetricTransferMatrix_entrywisePositive
                          (layerInternalWeight H
                            ({ p with β := β } : IsingParams ℝ))
                          (layerTransitionWeight transitionPairs
                            ({ p with β := β } : IsingParams ℝ))
                          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  intro ratio cap hratio hcap hsimple_eventually
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_physicalNormWindow_absSimpleParity
      H transitionPairs p hp spec hratio hcap
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_local hsimple_eventually)

/-! ## Cubic local simple-parity consumers -/

/-- On any cubic interval where the physical norm-window inequality and
columnwise simple eigenspaces both hold, the existing simple-parity physical
route gives a finite open spin-observable min-gap certificate at each `β` in
the interval. -/
noncomputable def
    cubicLayerOpenMinGapCert_of_Ioc_physicalNormWindow_localSimpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (βmax : ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (hwindow :
      ∀ β : ℝ, β ∈ Set.Icc 0 βmax →
        (spec β).subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight (cubicLayerGraph d R)
                ({ p with β := β } : IsingParams ℝ))
              (layerTransitionWeight (cubicLayerTransitionPairs d R)
                ({ p with β := β } : IsingParams ℝ))
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
          <
            cubicLayerOpenPhysicalBoundaryNormWindowCap
              d R ({ p with β := β } : IsingParams ℝ)
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
  layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParityCanonicalRatioPhysicalNormWindow
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R)
    ({ p with β := β } : IsingParams ℝ) (by simpa using hp) x (spec β)
    (by
      simpa [cubicLayerOpenPhysicalBoundaryNormWindowCap] using
        hwindow β ⟨le_of_lt hβ.1, hβ.2⟩)
    (hsimple β hβ)

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces on
a punctured one-sided interval, finite cubic open-slab same-transverse-site
decay holds on a possibly smaller punctured one-sided high-temperature
interval. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_physicalNormWindow_IocSimpleParity
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
      cubicLayerOpenPhysicalBoundaryNormWindowCap
        d R ({ p with β := β } : IsingParams ℝ)
        (spec β) (spec β).maxEigenIndex
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ βsimple : ℝ, 0 < βsimple →
          (∀ β : ℝ, β ∈ Set.Ioc 0 βsimple →
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
                            (spec β).maxEigenIndex
                            ((spec β).subdominantRatio_maxEigenIndex
                              (layerSymmetricTransferMatrix_entrywisePositive
                                (layerInternalWeight (cubicLayerGraph d R)
                                  ({ p with β := β } : IsingParams ℝ))
                                (layerTransitionWeight (cubicLayerTransitionPairs d R)
                                  ({ p with β := β } : IsingParams ℝ))
                                (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                        ((spec β).subdominantRatio_maxEigenIndex
                          (layerSymmetricTransferMatrix_entrywisePositive
                            (layerInternalWeight (cubicLayerGraph d R)
                              ({ p with β := β } : IsingParams ℝ))
                            (layerTransitionWeight (cubicLayerTransitionPairs d R)
                              ({ p with β := β } : IsingParams ℝ))
                            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^
                          sep := by
  intro ratio cap hratio hcap βsimple hβsimple hsimple
  rcases
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      d R p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases exists_pos_Ioc_subset_Icc_Ioc hβwindow_pos hβsimple with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with ⟨hβ_window, hβ_simple⟩
  exact
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      d R ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ_window) (hsimple β hβ_simple) left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces on
a punctured absolute-value neighborhood, finite cubic open-slab
same-transverse-site decay holds on a punctured one-sided high-temperature
interval. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_physicalNormWindow_absSimpleParity
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
      cubicLayerOpenPhysicalBoundaryNormWindowCap
        d R ({ p with β := β } : IsingParams ℝ)
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
                          (spec β).maxEigenIndex
                          ((spec β).subdominantRatio_maxEigenIndex
                            (layerSymmetricTransferMatrix_entrywisePositive
                              (layerInternalWeight (cubicLayerGraph d R)
                                ({ p with β := β } : IsingParams ℝ))
                              (layerTransitionWeight (cubicLayerTransitionPairs d R)
                                ({ p with β := β } : IsingParams ℝ))
                              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                      ((spec β).subdominantRatio_maxEigenIndex
                        (layerSymmetricTransferMatrix_entrywisePositive
                          (layerInternalWeight (cubicLayerGraph d R)
                            ({ p with β := β } : IsingParams ℝ))
                          (layerTransitionWeight (cubicLayerTransitionPairs d R)
                            ({ p with β := β } : IsingParams ℝ))
                          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  intro ratio cap hratio hcap hsimple_abs
  rcases
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      d R p spec hratio hcap with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases hsimple_abs with ⟨ε, hε_pos, hsimple⟩
  rcases exists_pos_Ioc_subset_Icc_punctured_abs hβwindow_pos hε_pos with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with ⟨hβ_window, hβ_abs_pos, hβ_abs⟩
  exact
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      d R ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ_window) (hsimple β hβ_abs_pos hβ_abs)
      left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces
eventually near but away from `β = 0`, finite cubic open-slab same-transverse-site
decay holds on a punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_physicalNormWindow_eventuallySimpleParity
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
      cubicLayerOpenPhysicalBoundaryNormWindowCap
        d R ({ p with β := β } : IsingParams ℝ)
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
                          (spec β).maxEigenIndex
                          ((spec β).subdominantRatio_maxEigenIndex
                            (layerSymmetricTransferMatrix_entrywisePositive
                              (layerInternalWeight (cubicLayerGraph d R)
                                ({ p with β := β } : IsingParams ℝ))
                              (layerTransitionWeight (cubicLayerTransitionPairs d R)
                                ({ p with β := β } : IsingParams ℝ))
                              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
                      ((spec β).subdominantRatio_maxEigenIndex
                        (layerSymmetricTransferMatrix_entrywisePositive
                          (layerInternalWeight (cubicLayerGraph d R)
                            ({ p with β := β } : IsingParams ℝ))
                          (layerTransitionWeight (cubicLayerTransitionPairs d R)
                            ({ p with β := β } : IsingParams ℝ))
                          (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  intro ratio cap hratio hcap hsimple_eventually
  exact
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_physicalNormWindow_absSimpleParity
      d R p hp spec hratio hcap
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_local hsimple_eventually)

end TransferMatrix

end IsingModel
