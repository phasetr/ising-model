import IsingModel.TransferMatrix.LayerOpenHighTemperatureNormWindow
import IsingModel.TransferMatrix.LayerOpenParitySimple

/-!
# High-temperature open simple-parity norm-window consumers

This file composes the high-temperature physical open norm-window bridge with
the existing simple-parity open-boundary consumers.  `ContinuousAt` hypotheses
for the chosen finite spectral-data family's canonical ratio and physical
norm-window cap supply the scalar `Tendsto` inputs from
`LayerOpenHighTemperatureNormWindow`.  On the resulting one-sided
high-temperature interval, the existing physical norm-window simple-parity
route gives finite open-slab and cubic open-slab correlation bounds.

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

/-! ## Continuous-at wrappers for the scalar high-temperature bridge -/

/-- Under explicit scalar `ContinuousAt` hypotheses for a chosen finite
spectral-data family, the beta-zero physical norm-window inequality persists
eventually near `β = 0`. -/
theorem eventually_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
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
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ᶠ β in 𝓝 0, ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    eventually_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      H transitionPairs p spec hratio.tendsto hcap.tendsto

/-- Under explicit scalar `ContinuousAt` hypotheses for a chosen finite
spectral-data family, the physical norm-window inequality holds on an
absolute-value neighborhood of `β = 0`. -/
theorem
    exists_pos_abs_lt_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
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
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∃ ε > 0, ∀ β : ℝ, |β| < ε → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_abs_lt_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      H transitionPairs p spec hratio.tendsto hcap.tendsto

/-- Under explicit scalar `ContinuousAt` hypotheses for a chosen finite
spectral-data family, the physical norm-window inequality holds on a one-sided
high-temperature interval `0 ≤ β ≤ βmax`. -/
theorem
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
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
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      H transitionPairs p spec hratio.tendsto hcap.tendsto

/-! ## Cubic continuous-at wrappers -/

/-- Cubic specialization of the eventual finite high-temperature physical
norm-window bridge from scalar `ContinuousAt` hypotheses. -/
theorem
    eventually_cubic_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
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
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∀ᶠ β in 𝓝 0, ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    eventually_cubic_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      d R p spec hratio.tendsto hcap.tendsto

/-- Cubic specialization of the one-sided finite high-temperature physical
norm-window bridge from scalar `ContinuousAt` hypotheses. -/
theorem
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
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
    ContinuousAt ratio 0 →
      ContinuousAt cap 0 →
        ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → ratio β < cap β := by
  intro ratio cap hratio hcap
  exact
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_tendsto_beta_zero
      d R p spec hratio.tendsto hcap.tendsto

/-! ## Simple-parity consumers on high-temperature intervals -/

/-- On any interval where the physical norm-window inequality holds, the
existing simple-parity physical route gives a finite open spin-observable
min-gap certificate at each `β` in the interval. -/
noncomputable def
    layerOpenMinGapCert_of_Icc_physicalNormWindow_simpleParity
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
    (hsimple : ∀ β : ℝ, (spec β).ColumnSimpleEigenspaces)
    (β : ℝ) (hβ : β ∈ Set.Icc 0 βmax) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight transitionPairs ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParityCanonicalRatioPhysicalNormWindow
    H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp) x
    (spec β) (hwindow β hβ) (hsimple β)

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces
for the chosen spectral-data family, finite open-slab same-transverse-site
decay holds throughout a one-sided high-temperature interval. -/
theorem
    exists_pos_Icc_openSlab_abs_le_of_continuousAt_physicalNormWindow_simpleParity
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
        (∀ β : ℝ, (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Icc 0 βmax →
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
  intro ratio cap hratio hcap hsimple
  rcases
    exists_pos_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      H transitionPairs p spec hratio hcap with
    ⟨βmax, hβmax_pos, hwindow⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ) (hsimple β) left sep right hsep

/-! ## Cubic simple-parity consumers on high-temperature intervals -/

/-- On any cubic interval where the physical norm-window inequality holds, the
existing simple-parity physical route gives a finite open spin-observable
min-gap certificate at each `β` in the interval. -/
noncomputable def
    cubicLayerOpenMinGapCert_of_Icc_physicalNormWindow_simpleParity
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
    (hsimple : ∀ β : ℝ, (spec β).ColumnSimpleEigenspaces)
    (β : ℝ) (hβ : β ∈ Set.Icc 0 βmax) (x : CubicLayerSite d R) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight (cubicLayerTransitionPairs d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParityCanonicalRatioPhysicalNormWindow
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R)
    ({ p with β := β } : IsingParams ℝ) (by simpa using hp) x (spec β)
    (by simpa [cubicLayerOpenPhysicalBoundaryNormWindowCap] using hwindow β hβ)
    (hsimple β)

/-- Under scalar `ContinuousAt` hypotheses and columnwise simple eigenspaces
for the chosen cubic spectral-data family, finite cubic open-slab
same-transverse-site decay holds throughout a one-sided high-temperature
interval. -/
theorem
    exists_pos_Icc_cubicOpenSlab_abs_le_of_continuousAt_physicalNormWindow_simpleParity
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
        (∀ β : ℝ, (spec β).ColumnSimpleEigenspaces) →
          ∃ βmax > 0,
            ∀ β : ℝ, β ∈ Set.Icc 0 βmax →
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
  intro ratio cap hratio hcap hsimple
  rcases
    exists_pos_cubic_Icc_subdominantRatioMax_lt_openPhysicalNormCap_of_continuousAt_beta_zero
      d R p spec hratio hcap with
    ⟨βmax, hβmax_pos, hwindow⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  exact
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      d R ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (hwindow β hβ) (hsimple β) left sep right hsep

end TransferMatrix

end IsingModel
