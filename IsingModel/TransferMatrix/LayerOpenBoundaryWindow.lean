import IsingModel.TransferMatrix.LayerOpenPerron

/-!
# Open-boundary spectral boundary-window bridges

This file packages the finite open-boundary denominator smallness condition as
a positive spectral boundary-coordinate threshold.  It keeps the existing
Perron-facing open-boundary route unchanged, but adds wrappers that replace the
explicit `boundaryPrefactor_small` input by `theta` being below the boundary
window attached to the chosen dominant spectral channel.

The results are finite and conditional.  They do not prove an interacting
cubic-layer spectral window, parity-adapted spectral data, a thermodynamic
limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Boundary-coordinate window -/

/-- The squared boundary-coordinate mass away from a chosen spectral channel. -/
noncomputable def boundaryCoordinateRestSq {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) : ℝ :=
  ∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2

/-- The finite boundary-coordinate threshold that makes the open denominator
prefactor positive.  If there is no off-top boundary mass, the threshold is
normalized to `1`. -/
noncomputable def boundarySpectralWindowThreshold {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) : ℝ :=
  if E.boundaryCoordinateRestSq v top = 0 then 1
  else (E.boundaryCoordinates v top) ^ 2 / E.boundaryCoordinateRestSq v top

/-- The usable boundary window, capped at `1` so that it also supplies the
ordinary `theta < 1` hypothesis required by the spectral decay theorem. -/
noncomputable def boundarySpectralWindowCap {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) : ℝ :=
  min 1 (E.boundarySpectralWindowThreshold v top)

/-- The off-top squared boundary-coordinate mass is nonnegative. -/
theorem boundaryCoordinateRestSq_nonneg {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) :
    0 ≤ E.boundaryCoordinateRestSq v top := by
  dsimp [boundaryCoordinateRestSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (E.boundaryCoordinates v i)

/-- A positive top squared boundary coordinate makes the boundary threshold
positive. -/
theorem boundarySpectralWindowThreshold_pos_of_top_sq_pos {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω)
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2) :
    0 < E.boundarySpectralWindowThreshold v top := by
  dsimp [boundarySpectralWindowThreshold]
  split_ifs with hrest
  · norm_num
  · have hrest_nonneg := E.boundaryCoordinateRestSq_nonneg v top
    have hrest_pos : 0 < E.boundaryCoordinateRestSq v top :=
      lt_of_le_of_ne hrest_nonneg (fun h => hrest h.symm)
    exact div_pos htop hrest_pos

/-- A positive top squared boundary coordinate makes the capped boundary window
positive. -/
theorem boundarySpectralWindowCap_pos_of_top_sq_pos {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω)
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2) :
    0 < E.boundarySpectralWindowCap v top := by
  exact lt_min zero_lt_one
    (E.boundarySpectralWindowThreshold_pos_of_top_sq_pos v top htop)

/-- Being below the capped boundary window implies `theta < 1`. -/
theorem theta_lt_one_of_lt_boundarySpectralWindowCap {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω)
    {theta : ℝ} (htheta : theta < E.boundarySpectralWindowCap v top) :
    theta < 1 :=
  lt_of_lt_of_le htheta (min_le_left _ _)

/-- Being below the capped boundary window implies being below the raw boundary
threshold. -/
theorem theta_lt_boundarySpectralWindowThreshold_of_lt_boundarySpectralWindowCap
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω)
    {theta : ℝ} (htheta : theta < E.boundarySpectralWindowCap v top) :
    theta < E.boundarySpectralWindowThreshold v top :=
  lt_of_lt_of_le htheta (min_le_right _ _)

/-- A positive top coordinate and a boundary-window bound imply the open
denominator smallness inequality. -/
theorem boundaryPrefactor_small_of_lt_boundarySpectralWindowThreshold
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) {theta : ℝ}
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2)
    (htheta : theta < E.boundarySpectralWindowThreshold v top) :
    (∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2) *
        theta <
      (E.boundaryCoordinates v top) ^ 2 := by
  change E.boundaryCoordinateRestSq v top * theta <
    (E.boundaryCoordinates v top) ^ 2
  by_cases hrest : E.boundaryCoordinateRestSq v top = 0
  · rw [hrest]
    simpa using htop
  · have hrest_nonneg := E.boundaryCoordinateRestSq_nonneg v top
    have hrest_pos : 0 < E.boundaryCoordinateRestSq v top :=
      lt_of_le_of_ne hrest_nonneg (fun h => hrest h.symm)
    have htheta_div :
        theta <
          (E.boundaryCoordinates v top) ^ 2 /
            E.boundaryCoordinateRestSq v top := by
      simpa [boundarySpectralWindowThreshold, hrest] using htheta
    simpa [mul_comm] using (lt_div_iff₀ hrest_pos).mp htheta_div

/-- The capped boundary window implies the open denominator smallness
inequality. -/
theorem boundaryPrefactor_small_of_lt_boundarySpectralWindowCap
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) {theta : ℝ}
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2)
    (htheta : theta < E.boundarySpectralWindowCap v top) :
    (∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2) *
        theta <
      (E.boundaryCoordinates v top) ^ 2 :=
  E.boundaryPrefactor_small_of_lt_boundarySpectralWindowThreshold v top htop
    (E.theta_lt_boundarySpectralWindowThreshold_of_lt_boundarySpectralWindowCap
      v top htheta)

/-- The capped boundary window gives positivity of the open spectral partition
prefactor. -/
theorem boundarySpectralPartitionPrefactor_pos_of_lt_boundarySpectralWindowCap
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) {theta : ℝ}
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2)
    (htheta : theta < E.boundarySpectralWindowCap v top) :
    0 < E.boundarySpectralPartitionPrefactor v top theta :=
  E.boundarySpectralPartitionPrefactor_pos_of_small v top theta
    (E.boundaryPrefactor_small_of_lt_boundarySpectralWindowCap v top htop htheta)

end RealOrthogonalSpectralData

/-! ## Open Perron-facing wrappers -/

/-- The boundary-window cap for the balanced open boundary vector. -/
noncomputable def layerOpenBoundarySpectralWindowCap
    (u : Ω → ℝ) {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) : ℝ :=
  E.boundarySpectralWindowCap (layerOpenBalancedBoundaryVector u) top

/-- The balanced open boundary-vector window is positive against a
signed-positive spectral column. -/
theorem layerOpenBoundarySpectralWindowCap_pos_of_signedPositiveColumn
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a)
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) (hpos : E.SignedPositiveColumn top) :
    0 < layerOpenBoundarySpectralWindowCap u E top :=
  E.boundarySpectralWindowCap_pos_of_top_sq_pos
    (layerOpenBalancedBoundaryVector u) top
    (layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn u hu E top hpos)

/-- Open min-gap certificate with denominator smallness supplied by the
boundary-coordinate window. -/
noncomputable def
    layerOpenMinGapCert_of_signedPositiveBoundaryWindow
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix f top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumn
    u k f hu hk_pos E top theta theta_nonneg
    (E.theta_lt_one_of_lt_boundarySpectralWindowCap
      (layerOpenBalancedBoundaryVector u) top theta_lt_boundary_window)
    (E.boundaryPrefactor_small_of_lt_boundarySpectralWindowCap
      (layerOpenBalancedBoundaryVector u) top
      (layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn u hu E top
        dominant_column_signed_pos)
      theta_lt_boundary_window)
    subdominant_abs_le central_dominant_channel_zero dominant_column_signed_pos

/-- Max-index open min-gap certificate with denominator smallness supplied by
the boundary-coordinate window. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexBoundaryWindow
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E E.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i E.maxEigenIndex *
        E.markedMatrix f E.maxEigenIndex l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinGapCert_of_signedPositiveBoundaryWindow
    u k f hu hk_pos E E.maxEigenIndex theta theta_nonneg
    theta_lt_boundary_window subdominant_abs_le central_dominant_channel_zero
    (E.signedPositiveColumn_maxEigenIndex
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))

/-- Open spin-observable min-gap certificate with central-channel cancellation
from flip parity and denominator smallness from the boundary-coordinate window. -/
noncomputable def
    layerOpenMinGapCert_of_subdominant_signedPositiveFlipParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (hparity : E.ColumnFlipParity (layerStateFlipEquiv S))
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerOpenMinGapCert_of_signedPositiveBoundaryWindow
    u k (layerSpinAt x) hu hk_pos E top theta theta_nonneg
    theta_lt_boundary_window subdominant_abs_le
    (layerOpenBoundaryMarkedCentral_zero_of_layerSpinAt_flipParity
      u x E top hu_flip
      (layerSymmetricTransfer_signedPositiveColumn_flip_even
        u k hu hk_pos hu_flip hk_flip E top dominant_column_signed_pos)
      hparity)
    dominant_column_signed_pos

/-- Max-index open spin-observable min-gap certificate with flip-parity
cancellation and boundary-window denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexFlipParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta < layerOpenBoundarySpectralWindowCap u E E.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex)
    (hparity : E.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_subdominant_signedPositiveFlipParitySpin_boundaryWindow
      u k x hu hk_pos hu_flip hk_flip E E.maxEigenIndex theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hparity
      (E.signedPositiveColumn_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))

/-- Physical open spin-observable min-gap certificate with flip-parity
cancellation and boundary-window denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_layerSubdominant_signedPositiveFlipParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S))
    (dominant_column_signed_pos : spec.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_subdominant_signedPositiveFlipParitySpin_boundaryWindow
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) x
    (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)
    (layerInternalWeight_flip_of_h_zero H p hp)
    (layerTransitionWeight_flip_flip transitionPairs p)
    spec top theta theta_nonneg theta_lt_boundary_window
    subdominant_abs_le hparity dominant_column_signed_pos

/-- Physical max-index open spin-observable min-gap certificate with
flip-parity cancellation and boundary-window denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexFlipParitySpin_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_maxEigenIndexFlipParitySpin_boundaryWindow
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) x
      (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)
      (layerInternalWeight_flip_of_h_zero H p hp)
      (layerTransitionWeight_flip_flip transitionPairs p)
      spec theta theta_nonneg theta_lt_boundary_window
      subdominant_abs_le hparity

/-- Project-level finite open-slab same-transverse-site correlation decay from
signed-positive flip parity and boundary-window denominator control. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveFlipParity_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S))
    (dominant_column_signed_pos : spec.SignedPositiveColumn top)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta) *
          theta ^ sep := by
  let cert :
      LayerOpenMinSpectralGapCertificate
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerSpinAt x) :=
    layerOpenMinGapCert_of_layerSubdominant_signedPositiveFlipParitySpin_boundaryWindow
      H transitionPairs p hp x spec top theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hparity
      dominant_column_signed_pos
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate
      (S := S) H transitionPairs p x cert left sep right hsep

/-- Project-level finite open-slab same-transverse-site correlation decay from
max-index flip parity and boundary-window denominator control. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_maxEigenIndexFlipParity_boundaryWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight H p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S))
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
              spec.maxEigenIndex theta) *
          theta ^ sep := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let cert :
      LayerOpenMinSpectralGapCertificate
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerSpinAt x) :=
    layerOpenMinGapCert_of_layerMaxEigenIndexFlipParitySpin_boundaryWindow
      H transitionPairs p hp x spec theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hparity
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate
      (S := S) H transitionPairs p x cert left sep right hsep

/-- Cubic transverse open slabs inherit the boundary-window flip-parity
open-boundary dominance consumer from the generic open-slab theorem. -/
theorem
    correlation_cubicOpenSlab_same_transverse_abs_le_of_signedPositiveBoundaryWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (top : LayerState (CubicLayerSite d R)) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p) spec top)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv (CubicLayerSite d R)))
    (dominant_column_signed_pos : spec.SignedPositiveColumn top)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (cubicLayerOpenSlabGraph d R (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R)))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p))
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector
                (layerInternalWeight (cubicLayerGraph d R) p)) top theta) *
          theta ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveFlipParity_boundaryWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec top theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hparity
      dominant_column_signed_pos left sep right hsep

/-- Cubic transverse open slabs inherit the max-index boundary-window
flip-parity open-boundary dominance consumer from the generic open-slab
theorem. -/
theorem
    correlation_cubicOpenSlab_same_transverse_abs_le_of_maxEigenIndexBoundaryWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_boundary_window :
      theta <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (cubicLayerGraph d R) p) spec spec.maxEigenIndex)
    (subdominant_abs_le :
      ∀ i, i ≠ spec.maxEigenIndex →
        |spec.eigenvalue i| ≤ theta * spec.eigenvalue spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv (CubicLayerSite d R)))
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (cubicLayerOpenSlabGraph d R (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R)))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p))
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector
                (layerInternalWeight (cubicLayerGraph d R) p))
              spec.maxEigenIndex theta) *
          theta ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_maxEigenIndexFlipParity_boundaryWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec theta theta_nonneg
      theta_lt_boundary_window subdominant_abs_le hparity left sep right hsep

end TransferMatrix

end IsingModel
