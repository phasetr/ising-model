import IsingModel.TransferMatrix.LayerInfiniteTemperatureSpectralWindow
import IsingModel.TransferMatrix.LayerOpenPhysicalNormWindow

/-!
# Infinite-temperature open physical norm windows

This file closes the finite physical open-boundary norm-window input at the
infinite-temperature slice `p.β = 0`.  At this slice the balanced physical
transfer matrix is the all-ones matrix, the balanced open boundary vector is
constant one, and the physical norm-window cap at the maximal Perron column is
exactly `1`.  The existing canonical Perron ratio is strictly less than `1`,
so it is strictly below the physical norm-window cap.

This is only the `β = 0` finite-layer statement.  It does not prove a
high-temperature neighborhood, an interacting cubic-layer spectral window,
parity-adapted spectral data, a thermodynamic limit, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Constant-vector all-ones facts -/

omit [DecidableEq Ω] in
/-- The squared norm of the constant-one vector is the cardinality of the
index type. -/
theorem vectorSqNorm_one :
    vectorSqNorm (fun _ : Ω => (1 : ℝ)) = Fintype.card Ω := by
  simp [vectorSqNorm]

omit [DecidableEq Ω] in
/-- The constant-one vector is an eigenvector of the all-ones matrix with
eigenvalue equal to the cardinality. -/
theorem allOnesMatrix_mulVec_one :
    (allOnesMatrix Ω).mulVec (fun _ : Ω => (1 : ℝ)) =
      (Fintype.card Ω : ℝ) • (fun _ : Ω => (1 : ℝ)) := by
  ext i
  simp [allOnesMatrix_mulVec]

namespace RealOrthogonalSpectralData

/-- If a matrix is the all-ones matrix, then its maximal spectral-data
eigenvalue is the cardinality eigenvalue. -/
theorem maxEigenIndex_eigenvalue_of_matrix_eq_allOnes [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : M = allOnesMatrix Ω) :
    E.eigenvalue E.maxEigenIndex = (Fintype.card Ω : ℝ) := by
  by_cases hzero : E.eigenvalue E.maxEigenIndex = 0
  · have hM_pos : MatrixEntrywisePositive M := by
      rw [hM]
      exact allOnesMatrix_entrywisePositive (Ω := Ω)
    have hpos := E.eigenvalue_pos_maxEigenIndex hM_pos
    linarith
  · exact
      allOnesMatrix_eigenvalue_eq_card_of_ne_zero
        (E.changeOfBasis_column_ne_zero E.maxEigenIndex)
        (by
          have h := E.mulVec_changeOfBasis_column E.maxEigenIndex
          calc
            (allOnesMatrix Ω).mulVec
                (fun x => E.changeOfBasis x E.maxEigenIndex)
                = M.mulVec (fun x => E.changeOfBasis x E.maxEigenIndex) := by
                  exact
                    congrArg
                      (fun N : Matrix Ω Ω ℝ =>
                        N.mulVec (fun x => E.changeOfBasis x E.maxEigenIndex))
                      hM.symm
            _ = E.eigenvalue E.maxEigenIndex •
                  (fun x => E.changeOfBasis x E.maxEigenIndex) := h)
        hzero

/-- If a matrix is the all-ones matrix, then its maximal spectral column has
constant-one boundary coordinate with squared value equal to the cardinality. -/
theorem boundaryCoordinates_one_sq_maxEigenIndex_of_matrix_eq_allOnes
    [Nonempty Ω] {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : M = allOnesMatrix Ω) :
    (E.boundaryCoordinates (fun _ : Ω => (1 : ℝ)) E.maxEigenIndex) ^ 2 =
      Fintype.card Ω := by
  have hM_pos : MatrixEntrywisePositive M := by
    rw [hM]
    exact allOnesMatrix_entrywisePositive (Ω := Ω)
  have hone_eig :
      M.mulVec (fun _ : Ω => (1 : ℝ)) =
        E.eigenvalue E.maxEigenIndex • (fun _ : Ω => (1 : ℝ)) := by
    calc
      M.mulVec (fun _ : Ω => (1 : ℝ))
          = (allOnesMatrix Ω).mulVec (fun _ : Ω => (1 : ℝ)) := by
            exact
              congrArg
                (fun N : Matrix Ω Ω ℝ =>
                  N.mulVec (fun _ : Ω => (1 : ℝ)))
                hM
      _ = (Fintype.card Ω : ℝ) • (fun _ : Ω => (1 : ℝ)) :=
            allOnesMatrix_mulVec_one (Ω := Ω)
      _ = E.eigenvalue E.maxEigenIndex • (fun _ : Ω => (1 : ℝ)) := by
            rw [E.maxEigenIndex_eigenvalue_of_matrix_eq_allOnes hM]
  obtain ⟨c, hc⟩ :=
    E.eigenspace_simple_maxEigenIndex hM_pos hone_eig
  have hcoord :
      E.boundaryCoordinates (fun _ : Ω => (1 : ℝ)) E.maxEigenIndex = c := by
    rw [hc]
    unfold boundaryCoordinates
    calc
      ∑ x, c * E.changeOfBasis x E.maxEigenIndex *
          E.changeOfBasis x E.maxEigenIndex
          = c * vectorSqNorm (fun x => E.changeOfBasis x E.maxEigenIndex) := by
            unfold vectorSqNorm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = c := by
        rw [E.vectorSqNorm_changeOfBasis_column]
        ring
  have hnorm :
      vectorSqNorm (fun _ : Ω => (1 : ℝ)) =
        vectorSqNorm (c • fun x => E.changeOfBasis x E.maxEigenIndex) := by
    rw [hc]
  have hnorm_smul :
      vectorSqNorm (c • fun x => E.changeOfBasis x E.maxEigenIndex) = c ^ 2 := by
    calc
      vectorSqNorm (c • fun x => E.changeOfBasis x E.maxEigenIndex)
          = c ^ 2 * vectorSqNorm (fun x => E.changeOfBasis x E.maxEigenIndex) := by
            unfold vectorSqNorm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            simp [Pi.smul_apply, smul_eq_mul]
            ring
      _ = c ^ 2 := by
        rw [E.vectorSqNorm_changeOfBasis_column]
        ring
  have hc_sq : c ^ 2 = Fintype.card Ω := by
    rw [hnorm_smul, vectorSqNorm_one] at hnorm
    exact hnorm.symm
  rw [hcoord, hc_sq]

/-- The maximal all-ones spectral column has constant-one boundary coordinate
with squared value equal to the cardinality. -/
theorem boundaryCoordinates_one_sq_maxEigenIndex_allOnes [Nonempty Ω]
    (E : RealOrthogonalSpectralData (allOnesMatrix Ω)) :
    (E.boundaryCoordinates (fun _ : Ω => (1 : ℝ)) E.maxEigenIndex) ^ 2 =
      Fintype.card Ω :=
  E.boundaryCoordinates_one_sq_maxEigenIndex_of_matrix_eq_allOnes rfl

end RealOrthogonalSpectralData

/-! ## Infinite-temperature physical open norm windows -/

/-- At `β = 0`, the balanced open boundary vector is constant one. -/
theorem layerOpenBalancedBoundaryVector_beta_zero
    {S : Type*} [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (p : IsingParams ℝ)
    (hpβ : p.β = 0) :
    layerOpenBalancedBoundaryVector (layerInternalWeight H p) =
      fun _ : LayerState S => (1 : ℝ) := by
  ext ω
  simp [layerOpenBalancedBoundaryVector, layerInternalWeight_beta_zero H p hpβ]

/-- At `β = 0`, the one-layer internal partition sum is the number of layer
states. -/
theorem sum_layerInternalWeight_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (p : IsingParams ℝ)
    (hpβ : p.β = 0) :
    (∑ ω : LayerState S, layerInternalWeight H p ω) =
      Fintype.card (LayerState S) := by
  simp [layerInternalWeight_beta_zero H p hpβ]

/-- At `β = 0`, the physical open-boundary norm-window cap at the maximal
Perron column is exactly `1`. -/
theorem layerOpenPhysicalBoundaryNormWindowCap_beta_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hpβ : p.β = 0)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p))) :
    layerOpenPhysicalBoundaryNormWindowCap
        H transitionPairs p spec spec.maxEigenIndex = 1 := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  have hM := layerSymmetricTransferMatrix_beta_zero H transitionPairs p hpβ
  rw [layerOpenPhysicalBoundaryNormWindowCap,
    layerOpenBalancedBoundaryVector_beta_zero H p hpβ,
    sum_layerInternalWeight_beta_zero H p hpβ,
    spec.boundaryCoordinates_one_sq_maxEigenIndex_of_matrix_eq_allOnes hM]
  have hcard_ne : ((Fintype.card (LayerState S) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := LayerState S))
  rw [div_self hcard_ne]
  simp

/-- At `β = 0`, the canonical max-index ratio is strictly below the physical
open-boundary norm-window cap. -/
theorem subdominantRatioMax_lt_layerOpenPhysicalNormCap_beta_zero
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
        layerOpenPhysicalBoundaryNormWindowCap
          H transitionPairs p spec spec.maxEigenIndex := by
  rw [layerOpenPhysicalBoundaryNormWindowCap_beta_zero H transitionPairs p hpβ spec]
  exact
    spec.subdominantRatio_maxEigenIndex_lt_one
      (layerSymmetricTransferMatrix_entrywisePositive
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))

/-! ## Cubic specializations -/

/-- At `β = 0`, the cubic physical open-boundary norm-window cap at the
maximal Perron column is exactly `1`. -/
theorem cubicLayerOpenPhysicalBoundaryNormWindowCap_beta_zero
    (d R : ℕ) (p : IsingParams ℝ) (hpβ : p.β = 0)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p))) :
    cubicLayerOpenPhysicalBoundaryNormWindowCap d R p spec spec.maxEigenIndex = 1 := by
  exact
    layerOpenPhysicalBoundaryNormWindowCap_beta_zero
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hpβ spec

/-- At `β = 0`, the cubic canonical max-index ratio is strictly below the
physical open-boundary norm-window cap. -/
theorem cubic_subdominantRatioMax_lt_openPhysicalNormCap_beta_zero
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
        cubicLayerOpenPhysicalBoundaryNormWindowCap
          d R p spec spec.maxEigenIndex := by
  exact
    subdominantRatioMax_lt_layerOpenPhysicalNormCap_beta_zero
      (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hpβ spec

end TransferMatrix

end IsingModel
