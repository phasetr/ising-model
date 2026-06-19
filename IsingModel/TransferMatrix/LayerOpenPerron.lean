import IsingModel.TransferMatrix.LayerOpenSpectralDecay
import IsingModel.TransferMatrix.LayerPerronExistence

/-!
# Perron-facing constructors for open-boundary layer spectral bounds

This file packages finite, conditional open-boundary spectral inputs in a form
closer to the Perron-facing layer route.  It proves positivity of the balanced
open boundary vector, a reusable sufficient condition for the open spectral
denominator prefactor, and constructors that fix the transfer scale to a
signed-positive dominant spectral column.

The results remain finite and conditional.  In particular, the quantitative
boundary-prefactor smallness and the open central marked-channel cancellation
remain explicit inputs.  This file does not prove a physical interacting
spectral window, a thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Boundary-vector positivity -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced open boundary vector is strictly positive when the layer
weight is strictly positive. -/
theorem layerOpenBalancedBoundaryVector_pos
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a) :
    VectorPositive (layerOpenBalancedBoundaryVector u) := by
  intro a
  exact Real.sqrt_pos.mpr (hu a)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced open boundary vector is invariant under global spin flip when
the underlying layer weight is. -/
theorem layerOpenBalancedBoundaryVector_flip_of_u_flip
    {S : Type*} (u : LayerState S → ℝ)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (ω : LayerState S) :
    layerOpenBalancedBoundaryVector u (layerStateFlipEquiv S ω) =
      layerOpenBalancedBoundaryVector u ω := by
  change Real.sqrt (u (Config.flip ω)) = Real.sqrt (u ω)
  simpa [layerStateFlipEquiv_apply] using congrArg Real.sqrt (hu_flip ω)

namespace RealOrthogonalSpectralData

/-! ## Boundary prefactor positivity -/

/-- A direct smallness condition makes the open boundary spectral denominator
prefactor positive. -/
theorem boundarySpectralPartitionPrefactor_pos_of_small {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) (theta : ℝ)
    (hsmall :
      (∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2) *
          theta <
        (E.boundaryCoordinates v top) ^ 2) :
    0 < E.boundarySpectralPartitionPrefactor v top theta := by
  dsimp [boundarySpectralPartitionPrefactor]
  linarith

/-- A positive boundary vector has a strictly positive signed top boundary
coordinate against a signed-positive spectral column. -/
theorem sign_mul_boundaryCoordinates_pos_of_vectorPositive_signedPositiveColumn
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (v : Ω → ℝ) (top : Ω)
    (hv : VectorPositive v) (hpos : E.SignedPositiveColumn top) :
    0 < hpos.sign * E.boundaryCoordinates v top := by
  have hsum :
      0 < ∑ x, v x * (hpos.sign * E.changeOfBasis x top) := by
    refine Finset.sum_pos' ?_ ?_
    · intro x _hx
      exact (mul_pos (hv x) (hpos.positive x)).le
    · exact ⟨top, Finset.mem_univ top,
        mul_pos (hv top) (hpos.positive top)⟩
  have hcoord :
      hpos.sign * E.boundaryCoordinates v top =
        ∑ x, v x * (hpos.sign * E.changeOfBasis x top) := by
    dsimp [boundaryCoordinates]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  simpa [hcoord]

/-- A positive boundary vector has nonzero top boundary coordinate against a
signed-positive spectral column. -/
theorem boundaryCoordinates_ne_zero_of_vectorPositive_signedPositiveColumn
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (v : Ω → ℝ) (top : Ω)
    (hv : VectorPositive v) (hpos : E.SignedPositiveColumn top) :
    E.boundaryCoordinates v top ≠ 0 := by
  intro hzero
  have hpositive :=
    E.sign_mul_boundaryCoordinates_pos_of_vectorPositive_signedPositiveColumn
      v top hv hpos
  simp [hzero] at hpositive

/-- A positive boundary vector has positive squared top boundary coordinate
against a signed-positive spectral column. -/
theorem boundaryCoordinates_sq_pos_of_vectorPositive_signedPositiveColumn
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (v : Ω → ℝ) (top : Ω)
    (hv : VectorPositive v) (hpos : E.SignedPositiveColumn top) :
    0 < (E.boundaryCoordinates v top) ^ 2 :=
  sq_pos_of_ne_zero
    (E.boundaryCoordinates_ne_zero_of_vectorPositive_signedPositiveColumn
      v top hv hpos)

end RealOrthogonalSpectralData

/-! ## Open Perron-facing certificate constructors -/

/-- The balanced open boundary vector has nonzero top spectral coordinate
against a signed-positive dominant spectral column. -/
theorem layerOpenBoundaryCoordinate_ne_zero_of_signedPositiveColumn
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a)
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) (hpos : E.SignedPositiveColumn top) :
    E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) top ≠ 0 :=
  E.boundaryCoordinates_ne_zero_of_vectorPositive_signedPositiveColumn
    (layerOpenBalancedBoundaryVector u) top
    (layerOpenBalancedBoundaryVector_pos u hu) hpos

/-- The balanced open boundary vector has positive squared top spectral
coordinate against a signed-positive dominant spectral column. -/
theorem layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a)
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (top : Ω) (hpos : E.SignedPositiveColumn top) :
    0 < (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) top) ^ 2 :=
  E.boundaryCoordinates_sq_pos_of_vectorPositive_signedPositiveColumn
    (layerOpenBalancedBoundaryVector u) top
    (layerOpenBalancedBoundaryVector_pos u hu) hpos

/-- Constructor for an open min-gap certificate with the transfer scale fixed
to a signed-positive dominant spectral column.  The open boundary denominator
prefactor is discharged from the explicit boundary-coordinate smallness
condition. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumn
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (boundaryPrefactor_small :
      (∑ i ∈ Finset.univ.erase top,
          (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i) ^ 2) *
          theta <
        (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) top) ^ 2)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix f top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0)
    (dominant_column_signed_pos : E.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate u k f := by
  letI : Nonempty Ω := ⟨top⟩
  exact
    layerOpenMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
      u k f hu E top (E.eigenvalue top) theta
      (E.eigenvalue_pos_of_signedPositiveColumn
        (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top
        dominant_column_signed_pos)
      theta_nonneg theta_lt_one
      (E.boundarySpectralPartitionPrefactor_pos_of_small
        (layerOpenBalancedBoundaryVector u) top theta boundaryPrefactor_small)
      rfl subdominant_abs_le central_dominant_channel_zero

/-- Maximal-index open min-gap certificate constructor.  The signed-positive
dominant column is supplied by the finite Perron-facing maximal-column
construction for an entrywise positive balanced transfer matrix. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_orthogonalMaxEigenIndex
    [Nonempty Ω]
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk_pos : ∀ a b, 0 < k a b)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (boundaryPrefactor_small :
      (∑ i ∈ Finset.univ.erase E.maxEigenIndex,
          (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i) ^ 2) *
          theta <
        (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u)
          E.maxEigenIndex) ^ 2)
    (subdominant_abs_le :
      ∀ i, i ≠ E.maxEigenIndex →
        |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i E.maxEigenIndex *
        E.markedMatrix f E.maxEigenIndex l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumn
    u k f hu hk_pos E E.maxEigenIndex theta theta_nonneg theta_lt_one
    boundaryPrefactor_small subdominant_abs_le central_dominant_channel_zero
    (E.signedPositiveColumn_maxEigenIndex
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos))

/-- Physical layer wrapper for open min-gap certificates with scale fixed to a
signed-positive dominant spectral column and denominator positivity supplied by
the matching open boundary-prefactor smallness condition. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_layerOrthogonalSubdominantBounds_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (boundaryPrefactor_small :
      (∑ i ∈ Finset.univ.erase top,
          (spec.boundaryCoordinates
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i) ^ 2) *
          theta <
        (spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top) ^ 2)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0)
    (dominant_column_signed_pos : spec.SignedPositiveColumn top) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinSpectralGapCertificate_of_orthogonalSubdominantBounds_signedPositiveColumn
    (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
    (layerSpinAt x) (fun _ => Real.exp_pos _)
    (fun _ _ => Real.exp_pos _) spec top theta theta_nonneg theta_lt_one
    boundaryPrefactor_small subdominant_abs_le central_dominant_channel_zero
    dominant_column_signed_pos

/-- Project-level finite open-slab same-transverse-site correlation decay from
signed-positive open-boundary dominance data. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveBoundaryDominance
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (boundaryPrefactor_small :
      (∑ i ∈ Finset.univ.erase top,
          (spec.boundaryCoordinates
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i) ^ 2) *
          theta <
        (spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top) ^ 2)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0)
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
    layerOpenMinSpectralGapCertificate_of_layerOrthogonalSubdominantBounds_signedPositiveColumn
      H transitionPairs p x spec top theta theta_nonneg theta_lt_one
      boundaryPrefactor_small subdominant_abs_le central_dominant_channel_zero
      dominant_column_signed_pos
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate
      (S := S) H transitionPairs p x cert left sep right hsep

/-- Cubic transverse open slabs inherit the signed-positive open-boundary
dominance consumer from the generic open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveBoundaryDominance
    (d R : ℕ) (p : IsingParams ℝ) (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (top : LayerState (CubicLayerSite d R)) (theta : ℝ)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (boundaryPrefactor_small :
      (∑ i ∈ Finset.univ.erase top,
          (spec.boundaryCoordinates
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (cubicLayerGraph d R) p)) i) ^ 2) *
          theta <
        (spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) top) ^ 2)
    (subdominant_abs_le :
      ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * spec.eigenvalue top)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt x) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) l = 0)
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
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_signedPositiveBoundaryDominance
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p x spec top theta theta_nonneg
      theta_lt_one boundaryPrefactor_small subdominant_abs_le
      central_dominant_channel_zero dominant_column_signed_pos left sep right hsep

end TransferMatrix

end IsingModel
