import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge

/-!
# Balanced layer symmetric spectral data (GJ §17.1)

The finite Hermitian spectral-theorem eigenvalue/eigenvector data of the
balanced layer transfer matrix, and the diagonal similarity relating the
ordinary and balanced layer transfer matrices.  Child module of the
`LayerSpectral.FlipParity` scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The finite Hermitian spectral-theorem eigenvalues of the balanced layer
transfer matrix.  They are indexed by the layer-state type. -/
noncomputable def layerSymmetricTransferEigenvalues
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    Ω → ℝ :=
  (layerSymmetricTransferMatrix_isHermitian u k hk).eigenvalues

/-- The finite Hermitian spectral-theorem orthonormal eigenbasis of the balanced
layer transfer matrix. -/
noncomputable def layerSymmetricTransferEigenvectorBasis
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    OrthonormalBasis Ω ℝ (EuclideanSpace ℝ Ω) :=
  (layerSymmetricTransferMatrix_isHermitian u k hk).eigenvectorBasis

/-- The balanced layer spectral basis diagonalizes the balanced transfer matrix. -/
theorem layerSymmetricTransferMatrix_mulVec_eigenvectorBasis
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) (j : Ω) :
    layerSymmetricTransferMatrix u k
        *ᵥ ⇑(layerSymmetricTransferEigenvectorBasis u k hk j)
      = (layerSymmetricTransferEigenvalues u k hk j)
        • ⇑(layerSymmetricTransferEigenvectorBasis u k hk j) := by
  exact (layerSymmetricTransferMatrix_isHermitian u k hk).mulVec_eigenvectorBasis j

/-- The balanced finite layer partition trace is the sum of powers of the
finite Hermitian spectral-theorem eigenvalues of the balanced transfer matrix. -/
theorem layerSymmetricTransferPartitionTrace_eq_sum_eigenvalues_pow
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) (N : ℕ) :
    layerSymmetricTransferPartitionTrace u k N
      = ∑ i, layerSymmetricTransferEigenvalues u k hk i ^ N := by
  rw [layerSymmetricTransferPartitionTrace, layerSymmetricTransferEigenvalues]
  exact trace_pow_eq_sum_hermitian_eigenvalues_pow
    (layerSymmetricTransferMatrix_isHermitian u k hk) N

/-- Explicit real orthogonal spectral data for the balanced layer transfer
matrix, obtained from the finite Hermitian spectral theorem. -/
noncomputable def layerSymmetricTransferOrthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k) :=
  RealOrthogonalSpectralData.ofHermitian
    (layerSymmetricTransferMatrix_isHermitian u k hk)

/-- Diagonal similarity between the ordinary layer transfer matrix and the
balanced layer transfer matrix:
`T = D⁻¹ S D`. -/
theorem layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferMatrix u k
      = layerTransferSqrtDiagonalInv u
        * layerSymmetricTransferMatrix u k * layerTransferSqrtDiagonal u := by
  ext a b
  simp [layerTransferMatrix, layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
    layerSymmetricTransferMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  field_simp [(Real.sqrt_pos_of_pos (hu a)).ne']
  rw [Real.sq_sqrt (le_of_lt (hu b))]
  ring

/-- The finite layer partition trace is unchanged by replacing the transfer
matrix with its balanced diagonally similar form. -/
theorem layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hu : ∀ a, 0 < u a) (n : ℕ) :
    layerTransferPartitionTrace u k n
      = layerSymmetricTransferPartitionTrace u k n := by
  rw [layerTransferPartitionTrace, layerSymmetricTransferPartitionTrace,
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu]
  exact trace_matrix_conj_pow (layerSymmetricTransferMatrix u k)
    (layerTransferSqrtDiagonalInv u) (layerTransferSqrtDiagonal u)
    (layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu)
    (layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu) n

/-- The finite layer two-insertion trace is unchanged by replacing the transfer
matrix with its balanced diagonally similar form. -/
theorem layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (a b : ℕ) :
    layerTransferCorrelation_matrixElement u k f a b
      = layerSymmetricTransferCorrelationTrace u k f a b := by
  rw [layerTransferCorrelation_matrixElement, layerSymmetricTransferCorrelationTrace,
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu]
  exact trace_diagonal_conj_pow_diagonal_conj_pow
    (layerSymmetricTransferMatrix u k)
    (layerTransferSqrtDiagonalInv u) (layerTransferSqrtDiagonal u) f
    (layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu)
    (layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu)
    (diagonal_mul_comm f fun x => (Real.sqrt (u x))⁻¹)
    (diagonal_mul_comm (fun x => Real.sqrt (u x)) f) a b

end TransferMatrix

end IsingModel
