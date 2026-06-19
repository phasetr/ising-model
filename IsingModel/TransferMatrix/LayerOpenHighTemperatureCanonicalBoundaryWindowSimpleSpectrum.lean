import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum
import IsingModel.TransferMatrix.LayerOpenHighTemperatureCanonicalBoundaryWindowSimple

/-!
# Simple-spectrum canonical high-temperature boundary-window consumers

This file replaces the local `ColumnSimpleEigenspaces` input in the canonical
high-temperature boundary-window route by the more elementary, checkable
simple-spectrum hypothesis (eigenvalue injectivity) for the chosen
spectral-data family.  Each consumer is a thin wrapper over the corresponding
`...SimpleParity` consumer after converting `SimpleSpectrum` to
`ColumnSimpleEigenspaces` via `columnSimpleEigenspaces_of_simpleSpectrum`.

These results are finite and conditional.  They do not prove that
spectral-theorem data varies continuously, that an interacting cubic-layer
family has a simple spectrum, an interacting spectral window, a thermodynamic
limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Filter

open scoped Topology

/-- On any punctured one-sided interval where the canonical boundary-window
inequality and columnwise simple-eigenspace input hold, the max-index
simple-parity route gives a finite open spin-observable min-gap certificate at
each `β` in the interval. -/
noncomputable def layerOpenMinGapCert_of_Ioc_canonicalBoundaryWindow_localSimpleSpectrum
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
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).SimpleSpectrum)
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight transitionPairs ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x)
  :=
  layerOpenMinGapCert_of_Ioc_canonicalBoundaryWindow_localSimpleParity
    H transitionPairs p hp βmax spec hwindow
    (fun β hβ => (spec β).columnSimpleEigenspaces_of_simpleSpectrum (hsimple β hβ))
    β hβ x

/-- Under scalar continuity and local simple-eigenspace input on a punctured
one-sided interval, finite open-slab same-transverse-site decay holds on a
possibly smaller punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_IocSimpleSpectrum
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
            (spec β).SimpleSpectrum) →
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
                      (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap βlocal hβlocal hsimple
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_IocSimpleParity
      H transitionPairs p hp spec hratio hcap βlocal hβlocal
      (fun β hβ => (spec β).columnSimpleEigenspaces_of_simpleSpectrum (hsimple β hβ))

/-- Under scalar continuity and local simple-eigenspace input on a punctured
absolute-value neighborhood, finite open-slab same-transverse-site decay holds
on a punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_absSimpleSpectrum
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
          (spec β).SimpleSpectrum) →
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
                    (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap hsimple_abs
  obtain ⟨ε, hε, h⟩ := hsimple_abs
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_absSimpleParity
      H transitionPairs p hp spec hratio hcap
      ⟨ε, hε, fun β hβ1 hβ2 =>
        (spec β).columnSimpleEigenspaces_of_simpleSpectrum (h β hβ1 hβ2)⟩

/-- Under scalar continuity and local simple-eigenspace input eventually near
but away from `β = 0`, finite open-slab same-transverse-site decay holds on a
punctured one-sided high-temperature interval. -/
theorem
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventualSimpleSpectrum
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
        (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).SimpleSpectrum) →
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
                    (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap hsimple_eventually
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventualSimpleParity
      H transitionPairs p hp spec hratio hcap
      (hsimple_eventually.mono fun β h hβ =>
        (spec β).columnSimpleEigenspaces_of_simpleSpectrum (h hβ))

/-! ## Cubic simple-spectrum canonical boundary-window consumers -/

/-- Cubic specialization of the pointwise canonical-ratio boundary-window
local simple-parity certificate constructor. -/
noncomputable def cubicLayerOpenMinGapCert_of_Ioc_canonicalBoundaryWindow_localSimpleSpectrum
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
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).SimpleSpectrum)
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : CubicLayerSite d R) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight (cubicLayerTransitionPairs d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x)
  :=
  cubicLayerOpenMinGapCert_of_Ioc_canonicalBoundaryWindow_localSimpleParity
    d R p hp βmax spec hwindow
    (fun β hβ => (spec β).columnSimpleEigenspaces_of_simpleSpectrum (hsimple β hβ))
    β hβ x

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_IocSimpleSpectrum`. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_IocSimpleSpectrum
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
            (spec β).SimpleSpectrum) →
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
                      (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap βlocal hβlocal hsimple
  exact
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_IocSimpleParity
      d R p hp spec hratio hcap βlocal hβlocal
      (fun β hβ => (spec β).columnSimpleEigenspaces_of_simpleSpectrum (hsimple β hβ))

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_absSimpleSpectrum`. -/
theorem
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_absSimpleSpectrum
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
          (spec β).SimpleSpectrum) →
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
                    (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap hsimple_abs
  obtain ⟨ε, hε, h⟩ := hsimple_abs
  exact
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_absSimpleParity
      d R p hp spec hratio hcap
      ⟨ε, hε, fun β hβ1 hβ2 =>
        (spec β).columnSimpleEigenspaces_of_simpleSpectrum (h β hβ1 hβ2)⟩

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventualSimpleSpectrum`. -/
theorem
  exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventualSimpleSpectrum
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
        (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).SimpleSpectrum) →
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
                    (ratio β) ^ sep
  := by
  intro ratio cap hratio hcap hsimple_eventually
  exact
    exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_canonicalBoundaryWindow_eventualSimpleParity
      d R p hp spec hratio hcap
      (hsimple_eventually.mono fun β h hβ =>
        (spec β).columnSimpleEigenspaces_of_simpleSpectrum (h hβ))

end TransferMatrix

end IsingModel
