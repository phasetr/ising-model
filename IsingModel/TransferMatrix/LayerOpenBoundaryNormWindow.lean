import IsingModel.TransferMatrix.LayerOpenSubdominantWindow

/-!
# Open-boundary norm-window bridges

This file packages a finite norm-window sufficient condition for the existing
open-boundary spectral boundary-coordinate window.  The condition replaces the
off-top boundary-coordinate mass in the denominator by the full squared norm of
the balanced open boundary vector:

`theta < min 1 (topBoundaryCoordinate ^ 2 / vectorSqNorm boundaryVector)`.

This is weaker as a conclusion and stronger as a hypothesis than the sharp
boundary-coordinate window, but it is often easier to connect to concrete
finite layer estimates because the norm of the balanced open boundary vector is
the finite one-layer partition sum.  The results remain finite and conditional:
they do not construct parity-adapted spectral data, prove an interacting
cubic-layer spectral window, pass to a thermodynamic limit, or prove final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Norm control for boundary coordinates -/

/-- Boundary coordinates agree with the spectral coordinates used by the
Perron-facing norm API. -/
theorem boundaryCoordinates_eq_spectralCoord {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (i : Ω) :
    E.boundaryCoordinates v i = E.spectralCoord v i := by
  unfold boundaryCoordinates spectralCoord
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Boundary coordinates preserve the squared Euclidean norm. -/
theorem sum_boundaryCoordinates_sq {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) :
    (∑ i, (E.boundaryCoordinates v i) ^ 2) = vectorSqNorm v := by
  calc
    (∑ i, (E.boundaryCoordinates v i) ^ 2)
        = ∑ i, (E.spectralCoord v i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [E.boundaryCoordinates_eq_spectralCoord]
    _ = vectorSqNorm v := E.sum_spectralCoord_sq v

/-- The off-top boundary-coordinate mass is bounded by the full vector norm. -/
theorem boundaryCoordinateRestSq_le_vectorSqNorm {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) :
    E.boundaryCoordinateRestSq v top ≤ vectorSqNorm v := by
  have hsplit :
      (∑ i, (E.boundaryCoordinates v i) ^ 2) =
        (E.boundaryCoordinates v top) ^ 2 +
          E.boundaryCoordinateRestSq v top := by
    rw [← Finset.add_sum_erase (Finset.univ)
      (fun i => (E.boundaryCoordinates v i) ^ 2) (Finset.mem_univ top)]
    simp [boundaryCoordinateRestSq]
  calc
    E.boundaryCoordinateRestSq v top
        ≤ (E.boundaryCoordinates v top) ^ 2 +
            E.boundaryCoordinateRestSq v top := by
          nlinarith [sq_nonneg (E.boundaryCoordinates v top)]
    _ = ∑ i, (E.boundaryCoordinates v i) ^ 2 := hsplit.symm
    _ = vectorSqNorm v := E.sum_boundaryCoordinates_sq v

/-- A norm-window bound implies the sharper boundary-coordinate window used by
the open-boundary denominator route. -/
theorem theta_lt_boundarySpectralWindowCap_of_lt_normWindow
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω)
    {theta : ℝ}
    (htop : 0 < (E.boundaryCoordinates v top) ^ 2)
    (htheta :
      theta <
        min 1 ((E.boundaryCoordinates v top) ^ 2 / vectorSqNorm v)) :
    theta < E.boundarySpectralWindowCap v top := by
  have htheta_one : theta < 1 := lt_of_lt_of_le htheta (min_le_left _ _)
  have htheta_norm :
      theta < (E.boundaryCoordinates v top) ^ 2 / vectorSqNorm v :=
    lt_of_lt_of_le htheta (min_le_right _ _)
  have htheta_threshold :
      theta < E.boundarySpectralWindowThreshold v top := by
    dsimp [boundarySpectralWindowThreshold]
    split_ifs with hrest
    · exact htheta_one
    · have hrest_nonneg := E.boundaryCoordinateRestSq_nonneg v top
      have hrest_pos : 0 < E.boundaryCoordinateRestSq v top :=
        lt_of_le_of_ne hrest_nonneg (fun h => hrest h.symm)
      have hrest_le_norm := E.boundaryCoordinateRestSq_le_vectorSqNorm v top
      have hdiv :
          (E.boundaryCoordinates v top) ^ 2 / vectorSqNorm v ≤
            (E.boundaryCoordinates v top) ^ 2 /
              E.boundaryCoordinateRestSq v top :=
        div_le_div_of_nonneg_left htop.le hrest_pos hrest_le_norm
      exact lt_of_lt_of_le htheta_norm hdiv
  exact lt_min htheta_one htheta_threshold

end RealOrthogonalSpectralData

/-! ## Balanced open boundary norm windows -/

omit [DecidableEq Ω] in
/-- The squared norm of the balanced open boundary vector is the finite
one-layer weight sum. -/
theorem vectorSqNorm_layerOpenBalancedBoundaryVector
    (u : Ω → ℝ) (hu : ∀ a, 0 ≤ u a) :
    vectorSqNorm (layerOpenBalancedBoundaryVector u) = ∑ a, u a := by
  unfold vectorSqNorm layerOpenBalancedBoundaryVector
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.sq_sqrt (hu a)]

/-- A norm-window cap for the balanced open boundary vector. -/
noncomputable def layerOpenBoundaryNormWindowCap
    (u : Ω → ℝ) {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) : ℝ :=
  min 1
    ((E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) top) ^ 2 /
      ∑ a, u a)

/-- The balanced open norm-window cap implies the existing open boundary
spectral-window cap. -/
theorem theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap
    (u : Ω → ℝ) (hu : ∀ a, 0 ≤ u a)
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (top : Ω)
    {theta : ℝ}
    (htop :
      0 < (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) top) ^ 2)
    (htheta : theta < layerOpenBoundaryNormWindowCap u E top) :
    theta < layerOpenBoundarySpectralWindowCap u E top := by
  have hnorm := vectorSqNorm_layerOpenBalancedBoundaryVector u hu
  exact
    E.theta_lt_boundarySpectralWindowCap_of_lt_normWindow
      (layerOpenBalancedBoundaryVector u) top htop
      (by
        simpa [layerOpenBoundaryNormWindowCap, hnorm] using htheta)

/-- A signed-positive spectral column supplies the top-coordinate positivity
needed to pass from the norm window to the boundary-coordinate window. -/
theorem
    theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap_signedPositive
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a)
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M) (top : Ω)
    (hpos : E.SignedPositiveColumn top) {theta : ℝ}
    (htheta : theta < layerOpenBoundaryNormWindowCap u E top) :
    theta < layerOpenBoundarySpectralWindowCap u E top :=
  theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap
    u (fun a => (hu a).le) E top
    (layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
      u hu E top hpos)
    htheta

/-! ## Canonical-ratio norm-window certificate wrappers -/

/-- Max-index open min-gap certificate with denominator smallness supplied by
the norm-window sufficient condition. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexCanonicalRatioBoundaryNormWindow
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio_norm :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < layerOpenBoundaryNormWindowCap u E E.maxEigenIndex)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i E.maxEigenIndex *
        E.markedMatrix f E.maxEigenIndex l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinGapCert_of_maxEigenIndexCanonicalRatioBoundaryWindow
    u k f hu hk_pos E
    (theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap_signedPositive
      u hu E E.maxEigenIndex
      (E.signedPositiveColumn_maxEigenIndex
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
      hratio_norm)
    central_dominant_channel_zero

/-- Open spin-observable min-gap certificate with flip-parity cancellation,
canonical max-index ratio, and norm-window denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio_norm :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < layerOpenBoundaryNormWindowCap u E E.maxEigenIndex)
    (hparity : E.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryWindow
      u k x hu hk_pos hu_flip hk_flip E
      (theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap_signedPositive
        u hu E E.maxEigenIndex
        (E.signedPositiveColumn_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))
        hratio_norm)
      hparity

/-- Physical zero-field open spin-observable min-gap certificate with
flip-parity cancellation, canonical max-index ratio, and norm-window
denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexFlipParityCanonicalRatioBoundaryNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_norm :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundaryNormWindowCap
            (layerInternalWeight H p) spec spec.maxEigenIndex)
    (hparity : spec.ColumnFlipParity (layerStateFlipEquiv S)) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryNormWindow
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p) x
      (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)
      (layerInternalWeight_flip_of_h_zero H p hp)
      (layerTransitionWeight_flip_flip transitionPairs p)
      spec hratio_norm hparity

/-! ## Project-level open-slab norm-window consumers -/

/-- Project-level finite open-slab same-transverse-site correlation decay with
the canonical max-index subdominant ratio and norm-window denominator control. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_norm :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundaryNormWindowCap
            (layerInternalWeight H p) spec spec.maxEigenIndex)
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
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight H p)
                  (layerTransitionWeight transitionPairs p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryWindow
      H transitionPairs p hp x spec
      (theta_lt_layerOpenBoundarySpectralWindowCap_of_lt_normWindowCap_signedPositive
        (layerInternalWeight H p) (fun _ => Real.exp_pos _) spec
        spec.maxEigenIndex
        (spec.signedPositiveColumn_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))
        hratio_norm)
      hparity left sep right hsep

/-- Cubic transverse open slabs inherit the canonical-ratio norm-window
consumer from the generic open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryNormWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (hratio_norm :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenBoundaryNormWindowCap
            (layerInternalWeight (cubicLayerGraph d R) p)
            spec spec.maxEigenIndex)
    (hparity :
      spec.ColumnFlipParity (layerStateFlipEquiv (CubicLayerSite d R)))
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
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight (cubicLayerGraph d R) p)
                  (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioBoundaryNormWindow
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec hratio_norm hparity
      left sep right hsep

end TransferMatrix

end IsingModel
