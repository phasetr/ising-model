import IsingModel.TransferMatrix.LayerOpenHighTemperatureLocalSimpleParity
import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple

/-!
# Local high-temperature boundary-window simple-parity consumers

This file adds the high-temperature local-input layer for the explicit
open-boundary boundary-window simple-parity route.  A chosen spectral-data
family supplies explicit `top` and `theta` functions.  If `theta` and the
corresponding boundary-window cap are continuous at `β = 0`, and the strict
seed inequality `theta 0 < cap 0` holds, then the window inequality persists on
a small high-temperature interval.  Intersecting that interval with local
nonnegativity, subdominant, simple-eigenspace, and signed-positive inputs gives
finite open-slab and cubic open-slab estimates on a punctured one-sided
interval.

The results remain finite and conditional.  They do not prove spectral-data
continuity, eigenbasis perturbation theory, stability of `maxEigenIndex`,
concrete local simplicity or signed positivity, a concrete interacting
cubic-layer spectral window, a thermodynamic limit, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Filter
open scoped Topology

/-! ## Local interval helpers -/

/-- An eventual property near `0` contains an absolute-value neighborhood. -/
private theorem exists_pos_abs_lt_of_eventually_nhds_zero_boundary
    {P : ℝ → Prop} (hP : ∀ᶠ β in 𝓝 0, P β) :
    ∃ ε > 0, ∀ β : ℝ, |β| < ε → P β := by
  rw [Metric.eventually_nhds_iff] at hP
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun β hβ => hball (y := β) ?_⟩
  simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using hβ

/-- An eventual punctured property near `0` contains a punctured
absolute-value neighborhood. -/
private theorem exists_pos_punctured_abs_lt_of_eventually_nhds_zero_boundary
    {P : ℝ → Prop} (hP : ∀ᶠ β in 𝓝 0, β ≠ 0 → P β) :
    ∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε → P β := by
  rw [Metric.eventually_nhds_iff] at hP
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun β hβ_ne hβ => hball (y := β) ?_ ?_⟩
  · simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using hβ
  · exact abs_pos.mp hβ_ne

/-- An absolute-value neighborhood of `0` contains a positive closed
one-sided interval. -/
private theorem exists_pos_Icc_of_abs_neighborhood_boundary
    {P : ℝ → Prop} (hP : ∃ ε > 0, ∀ β : ℝ, |β| < ε → P β) :
    ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → P β := by
  rcases hP with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, by positivity, fun β hβ => hball β ?_⟩
  rcases hβ with ⟨hβ_nonneg, hβ_le⟩
  rw [abs_of_nonneg hβ_nonneg]
  linarith

/-- A positive closed one-sided interval and four positive punctured
one-sided intervals contain a common positive punctured one-sided subinterval. -/
private theorem exists_pos_Ioc_subset_Icc_Ioc4
    {a b c d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    ∃ f > 0, ∀ β : ℝ, β ∈ Set.Ioc 0 f →
      β ∈ Set.Icc 0 a ∧ β ∈ Set.Ioc 0 b ∧ β ∈ Set.Ioc 0 c ∧
        β ∈ Set.Ioc 0 d ∧ β ∈ Set.Ioc 0 e := by
  refine ⟨min a (min b (min c (min d e))), ?_, ?_⟩
  · exact lt_min ha (lt_min hb (lt_min hc (lt_min hd he)))
  · intro β hβ
    have hβ_le_a : β ≤ a :=
      le_trans hβ.2 (min_le_left a (min b (min c (min d e))))
    have hβ_le_b : β ≤ b :=
      le_trans hβ.2
        (le_trans (min_le_right a (min b (min c (min d e))))
          (min_le_left b (min c (min d e))))
    have hβ_le_c : β ≤ c :=
      le_trans hβ.2
        (le_trans (min_le_right a (min b (min c (min d e))))
          (le_trans (min_le_right b (min c (min d e)))
            (min_le_left c (min d e))))
    have hβ_le_d : β ≤ d :=
      le_trans hβ.2
        (le_trans (min_le_right a (min b (min c (min d e))))
          (le_trans (min_le_right b (min c (min d e)))
            (le_trans (min_le_right c (min d e)) (min_le_left d e))))
    have hβ_le_e : β ≤ e :=
      le_trans hβ.2
        (le_trans (min_le_right a (min b (min c (min d e))))
          (le_trans (min_le_right b (min c (min d e)))
            (le_trans (min_le_right c (min d e)) (min_le_right d e))))
    exact
      ⟨⟨le_of_lt hβ.1, hβ_le_a⟩, ⟨hβ.1, hβ_le_b⟩,
        ⟨hβ.1, hβ_le_c⟩, ⟨hβ.1, hβ_le_d⟩, ⟨hβ.1, hβ_le_e⟩⟩

/-- A positive closed one-sided interval and four positive punctured
absolute-value neighborhoods contain a common positive punctured one-sided
subinterval. -/
private theorem exists_pos_Ioc_subset_Icc_punctured_abs4
    {a ε₁ ε₂ ε₃ ε₄ : ℝ} (ha : 0 < a) (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃) (hε₄ : 0 < ε₄) :
    ∃ f > 0, ∀ β : ℝ, β ∈ Set.Ioc 0 f →
      β ∈ Set.Icc 0 a ∧
        0 < |β| ∧ |β| < ε₁ ∧
        0 < |β| ∧ |β| < ε₂ ∧
        0 < |β| ∧ |β| < ε₃ ∧
        0 < |β| ∧ |β| < ε₄ := by
  refine
    ⟨min a (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))),
      ?_, ?_⟩
  · exact
      lt_min ha
        (lt_min (by positivity)
          (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  · intro β hβ
    have hβ_le_a : β ≤ a :=
      le_trans hβ.2
        (min_le_left a
          (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
    have hβ_le_ε₁ : β ≤ ε₁ / 2 :=
      le_trans hβ.2
        (le_trans
          (min_le_right a
            (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
          (min_le_left (ε₁ / 2)
            (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
    have hβ_le_ε₂ : β ≤ ε₂ / 2 :=
      le_trans hβ.2
        (le_trans
          (min_le_right a
            (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
          (le_trans
            (min_le_right (ε₁ / 2)
              (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2))))
            (min_le_left (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
    have hβ_le_ε₃ : β ≤ ε₃ / 2 :=
      le_trans hβ.2
        (le_trans
          (min_le_right a
            (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
          (le_trans
            (min_le_right (ε₁ / 2)
              (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2))))
            (le_trans
              (min_le_right (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))
              (min_le_left (ε₃ / 2) (ε₄ / 2)))))
    have hβ_le_ε₄ : β ≤ ε₄ / 2 :=
      le_trans hβ.2
        (le_trans
          (min_le_right a
            (min (ε₁ / 2) (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))))
          (le_trans
            (min_le_right (ε₁ / 2)
              (min (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2))))
            (le_trans
              (min_le_right (ε₂ / 2) (min (ε₃ / 2) (ε₄ / 2)))
              (min_le_right (ε₃ / 2) (ε₄ / 2)))))
    have hβ_abs : |β| = β := abs_of_nonneg (le_of_lt hβ.1)
    have hβ_abs_pos : 0 < |β| := by simpa [hβ_abs] using hβ.1
    have hβ_abs_ε₁ : |β| < ε₁ := by rw [hβ_abs]; linarith
    have hβ_abs_ε₂ : |β| < ε₂ := by rw [hβ_abs]; linarith
    have hβ_abs_ε₃ : |β| < ε₃ := by rw [hβ_abs]; linarith
    have hβ_abs_ε₄ : |β| < ε₄ := by rw [hβ_abs]; linarith
    exact
      ⟨⟨le_of_lt hβ.1, hβ_le_a⟩,
        hβ_abs_pos, hβ_abs_ε₁,
        hβ_abs_pos, hβ_abs_ε₂,
        hβ_abs_pos, hβ_abs_ε₃,
        hβ_abs_pos, hβ_abs_ε₄⟩

/-! ## Boundary-window scalar bridges -/

/-- A strict explicit boundary-window inequality at `β = 0` persists
eventually under scalar `ContinuousAt` hypotheses for `theta` and the chosen
cap family. -/
theorem eventually_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          ∀ᶠ β in 𝓝 0, theta β < cap β := by
  intro cap htheta hcap h0
  exact htheta.tendsto.eventually_lt hcap.tendsto h0

/-- A strict explicit boundary-window inequality at `β = 0` persists on an
absolute-value neighborhood under scalar `ContinuousAt` hypotheses. -/
theorem exists_pos_abs_lt_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          ∃ ε > 0, ∀ β : ℝ, |β| < ε → theta β < cap β := by
  intro cap htheta hcap h0
  exact
    exists_pos_abs_lt_of_eventually_nhds_zero_boundary
      (eventually_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
        H transitionPairs p spec top theta htheta hcap h0)

/-- A strict explicit boundary-window inequality at `β = 0` persists on a
closed one-sided high-temperature interval under scalar `ContinuousAt`
hypotheses. -/
theorem exists_pos_Icc_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          ∃ βmax > 0, ∀ β : ℝ, β ∈ Set.Icc 0 βmax → theta β < cap β := by
  intro cap htheta hcap h0
  exact
    exists_pos_Icc_of_abs_neighborhood_boundary
      (exists_pos_abs_lt_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
        H transitionPairs p spec top theta htheta hcap h0)

/-! ## Generic local simple-parity boundary-window consumers -/

/-- On any interval where the explicit boundary-window, nonnegativity,
subdominant, columnwise simple-eigenspace, and signed-positive hypotheses all
hold, the existing simple-parity boundary-window route gives a finite open
spin-observable min-gap certificate at each `β` in the interval. -/
noncomputable def layerOpenMinGapCert_of_Ioc_boundaryWindow_localSimpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (βmax : ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ)
    (hwindow :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        theta β <
          layerOpenBoundarySpectralWindowCap
            (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
            (spec β) (top β))
    (htheta : ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → 0 ≤ theta β)
    (hsub :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        ∀ i, i ≠ top β →
          |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β))
    (hsimple :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).ColumnSimpleEigenspaces)
    (hsigned :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).SignedPositiveColumn (top β))
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : S) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight transitionPairs ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerSubdominant_signedPositiveSimpleParitySpin_boundaryWindow
    H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp) x
    (spec β) (top β) (theta β) (htheta β hβ) (hwindow β hβ)
    (hsub β hβ) (hsimple β hβ) (hsigned β hβ)

/-- Under scalar `ContinuousAt` hypotheses and local explicit simple-parity
boundary-window inputs on a punctured one-sided interval, finite open-slab
same-transverse-site decay holds on a possibly smaller punctured one-sided
high-temperature interval. -/
theorem exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_IocInputs
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          ∀ βlocal : ℝ, 0 < βlocal →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal → 0 ≤ theta β) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              ∀ i, i ≠ top β →
                |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              (spec β).ColumnSimpleEigenspaces) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              (spec β).SignedPositiveColumn (top β)) →
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
                              (top β) (theta β)) *
                          (theta β) ^ sep := by
  intro cap htheta hcap h0 βlocal hβlocal htheta_nonneg hsub hsimple hsigned
  rcases
    exists_pos_Icc_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec top theta htheta hcap h0 with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases
    exists_pos_Ioc_subset_Icc_Ioc4 hβwindow_pos hβlocal hβlocal hβlocal hβlocal with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with
    ⟨hβ_window, hβ_nonneg, hβ_sub, hβ_simple, hβ_signed⟩
  exact
    correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (top β) (theta β) (htheta_nonneg β hβ_nonneg)
      (hwindow β hβ_window) (hsub β hβ_sub) (hsimple β hβ_simple)
      (hsigned β hβ_signed) left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and local explicit simple-parity
boundary-window inputs on punctured absolute-value neighborhoods, finite
open-slab same-transverse-site decay holds on a punctured one-sided
high-temperature interval. -/
theorem exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_absInputs
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε → 0 ≤ theta β) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            ∀ i, i ≠ top β →
              |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            (spec β).ColumnSimpleEigenspaces) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            Nonempty ((spec β).SignedPositiveColumn (top β))) →
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
                            (top β) (theta β)) *
                        (theta β) ^ sep := by
  intro cap htheta hcap h0 htheta_abs hsub_abs hsimple_abs hsigned_abs
  rcases
    exists_pos_Icc_theta_lt_layerOpenBoundaryWindowCap_of_continuousAt_beta_zero
      H transitionPairs p spec top theta htheta hcap h0 with
    ⟨βwindow, hβwindow_pos, hwindow⟩
  rcases htheta_abs with ⟨εtheta, hεtheta_pos, htheta_nonneg⟩
  rcases hsub_abs with ⟨εsub, hεsub_pos, hsub⟩
  rcases hsimple_abs with ⟨εsimple, hεsimple_pos, hsimple⟩
  rcases hsigned_abs with ⟨εsigned, hεsigned_pos, hsigned⟩
  rcases
    exists_pos_Ioc_subset_Icc_punctured_abs4 hβwindow_pos hεtheta_pos
      hεsub_pos hεsimple_pos hεsigned_pos with
    ⟨βmax, hβmax_pos, hsubset⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  rcases hsubset β hβ with
    ⟨hβ_window, hβ_abs_pos_theta, hβ_abs_theta, hβ_abs_pos_sub, hβ_abs_sub,
      hβ_abs_pos_simple, hβ_abs_simple, hβ_abs_pos_signed, hβ_abs_signed⟩
  exact
    correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
      H transitionPairs ({ p with β := β } : IsingParams ℝ) (by simpa using hp)
      x (spec β) (top β) (theta β)
      (htheta_nonneg β hβ_abs_pos_theta hβ_abs_theta) (hwindow β hβ_window)
      (hsub β hβ_abs_pos_sub hβ_abs_sub) (hsimple β hβ_abs_pos_simple hβ_abs_simple)
      (Classical.choice (hsigned β hβ_abs_pos_signed hβ_abs_signed)) left sep right hsep

/-- Under scalar `ContinuousAt` hypotheses and local explicit simple-parity
boundary-window inputs eventually near but away from `β = 0`, finite
open-slab same-transverse-site decay holds on a punctured one-sided
high-temperature interval. -/
theorem exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_eventuallyInputs
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight transitionPairs
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState S) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight H ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          (∀ᶠ β in 𝓝 0, β ≠ 0 → 0 ≤ theta β) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 →
            ∀ i, i ≠ top β →
              |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).ColumnSimpleEigenspaces) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 →
            Nonempty ((spec β).SignedPositiveColumn (top β))) →
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
                            (top β) (theta β)) *
                        (theta β) ^ sep := by
  intro cap htheta hcap h0 htheta_eventually hsub_eventually hsimple_eventually
    hsigned_eventually
  exact
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_absInputs
      H transitionPairs p hp spec top theta htheta hcap h0
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_boundary htheta_eventually)
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_boundary hsub_eventually)
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_boundary hsimple_eventually)
      (exists_pos_punctured_abs_lt_of_eventually_nhds_zero_boundary hsigned_eventually)

/-! ## Cubic local simple-parity boundary-window consumers -/

/-- Cubic specialization of the pointwise explicit boundary-window local
simple-parity certificate constructor. -/
noncomputable def cubicLayerOpenMinGapCert_of_Ioc_boundaryWindow_localSimpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (βmax : ℝ)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState (CubicLayerSite d R)) (theta : ℝ → ℝ)
    (hwindow :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        theta β <
          layerOpenBoundarySpectralWindowCap
            (layerInternalWeight (cubicLayerGraph d R)
              ({ p with β := β } : IsingParams ℝ))
            (spec β) (top β))
    (htheta : ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → 0 ≤ theta β)
    (hsub :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax →
        ∀ i, i ≠ top β →
          |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β))
    (hsimple :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).ColumnSimpleEigenspaces)
    (hsigned :
      ∀ β : ℝ, β ∈ Set.Ioc 0 βmax → (spec β).SignedPositiveColumn (top β))
    (β : ℝ) (hβ : β ∈ Set.Ioc 0 βmax) (x : CubicLayerSite d R) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight (cubicLayerGraph d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerTransitionWeight (cubicLayerTransitionPairs d R)
        ({ p with β := β } : IsingParams ℝ))
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_Ioc_boundaryWindow_localSimpleParity
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp βmax spec
    top theta hwindow htheta hsub hsimple hsigned β hβ x

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_IocInputs`. -/
theorem exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_boundaryWindow_IocInputs
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState (CubicLayerSite d R)) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          ∀ βlocal : ℝ, 0 < βlocal →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal → 0 ≤ theta β) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              ∀ i, i ≠ top β →
                |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              (spec β).ColumnSimpleEigenspaces) →
            (∀ β : ℝ, β ∈ Set.Ioc 0 βlocal →
              (spec β).SignedPositiveColumn (top β)) →
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
                              (top β) (theta β)) *
                          (theta β) ^ sep := by
  intro cap htheta hcap h0 βlocal hβlocal htheta_nonneg hsub hsimple hsigned
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_IocInputs
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec top theta
      htheta hcap h0 βlocal hβlocal htheta_nonneg hsub hsimple hsigned with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_absInputs`. -/
theorem exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_boundaryWindow_absInputs
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState (CubicLayerSite d R)) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε → 0 ≤ theta β) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            ∀ i, i ≠ top β →
              |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            (spec β).ColumnSimpleEigenspaces) →
          (∃ ε > 0, ∀ β : ℝ, 0 < |β| → |β| < ε →
            Nonempty ((spec β).SignedPositiveColumn (top β))) →
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
                            (top β) (theta β)) *
                        (theta β) ^ sep := by
  intro cap htheta hcap h0 htheta_abs hsub_abs hsimple_abs hsigned_abs
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_absInputs
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec top theta
      htheta hcap h0 htheta_abs hsub_abs hsimple_abs hsigned_abs with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

/-- Cubic version of
`exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_eventuallyInputs`. -/
theorem exists_pos_Ioc_cubicOpenSlab_abs_le_of_continuousAt_boundaryWindow_eventuallyInputs
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
    (spec : (β : ℝ) →
      RealOrthogonalSpectralData
        (layerSymmetricTransferMatrix
          (layerInternalWeight (cubicLayerGraph d R)
            ({ p with β := β } : IsingParams ℝ))
          (layerTransitionWeight (cubicLayerTransitionPairs d R)
            ({ p with β := β } : IsingParams ℝ))))
    (top : ℝ → LayerState (CubicLayerSite d R)) (theta : ℝ → ℝ) :
    let cap : ℝ → ℝ := fun β =>
      layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (cubicLayerGraph d R)
          ({ p with β := β } : IsingParams ℝ))
        (spec β) (top β)
    ContinuousAt theta 0 →
      ContinuousAt cap 0 →
        theta 0 < cap 0 →
          (∀ᶠ β in 𝓝 0, β ≠ 0 → 0 ≤ theta β) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 →
            ∀ i, i ≠ top β →
              |(spec β).eigenvalue i| ≤ theta β * (spec β).eigenvalue (top β)) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 → (spec β).ColumnSimpleEigenspaces) →
          (∀ᶠ β in 𝓝 0, β ≠ 0 →
            Nonempty ((spec β).SignedPositiveColumn (top β))) →
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
                            (top β) (theta β)) *
                        (theta β) ^ sep := by
  intro cap htheta hcap h0 htheta_eventually hsub_eventually hsimple_eventually
    hsigned_eventually
  rcases
    exists_pos_Ioc_openSlab_abs_le_of_continuousAt_boundaryWindow_eventuallyInputs
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp spec top theta
      htheta hcap h0 htheta_eventually hsub_eventually hsimple_eventually
      hsigned_eventually with
    ⟨βmax, hβmax_pos, hbound⟩
  refine ⟨βmax, hβmax_pos, ?_⟩
  intro β hβ x left sep right hsep
  simpa [cubicLayerOpenSlabGraph] using hbound β hβ x left sep right hsep

end TransferMatrix

end IsingModel
