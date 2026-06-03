import IsingModel.TransferMatrix.OneDim
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonalization and matrix powers of the 1D Ising transfer matrix (GJ §17.1, §17.5)

This file diagonalizes the one-dimensional Ising transfer matrix `T(a)` of
`IsingModel.TransferMatrix.isingTransferMatrix1D` in the Hadamard basis and
derives the closed form of its matrix powers.  The trace of the `N`-th power is
the cyclic-chain partition-function value

  `Tr(T(a)ᴺ) = λ₊ᴺ + λ₋ᴺ`,   `λ₊ = eᵃ + e⁻ᵃ`,   `λ₋ = eᵃ - e⁻ᵃ`,

the heart of the transfer-matrix solution of the one-dimensional Ising chain
(Glimm–Jaffe §17.1).  The Hadamard matrix `H = !![1, 1; 1, -1]` intertwines
`T(a)` with the diagonal matrix `D = diagonal ![λ₊, λ₋]` via `T(a)·H = H·D`,
which powers to `T(a)ᴺ·H = H·Dᴺ` with no matrix inverse; the trace and
determinant closed forms then follow from `H⁻¹·H = 1` and `trace_mul_comm`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), §17.5
  (pp. 311–312, mass and exponential decay).
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix

/-- The `2 × 2` **Hadamard matrix** `H = !![1, 1; 1, -1]`, whose columns are the
eigenvectors of the 1D Ising transfer matrix. -/
def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- The Hadamard matrix squares to `2·I`: `H · H = 2 • 1`. -/
theorem hadamardMatrix_mul_self :
    hadamardMatrix * hadamardMatrix = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- The determinant of the Hadamard matrix is `-2`. -/
@[simp] theorem hadamardMatrix_det : hadamardMatrix.det = -2 := by
  rw [hadamardMatrix, Matrix.det_fin_two_of]; norm_num

/-- The Hadamard determinant is a unit (`-2 ≠ 0`), so `H` is invertible. -/
theorem hadamardMatrix_isUnit_det : IsUnit hadamardMatrix.det := by
  rw [hadamardMatrix_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- The inverse of the Hadamard matrix is `H⁻¹ = (1/2) • H`. -/
theorem hadamardMatrix_inv : hadamardMatrix⁻¹ = (1 / 2 : ℝ) • hadamardMatrix := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, hadamardMatrix_mul_self, smul_smul]
  norm_num

/-- The **diagonal matrix of transfer-matrix eigenvalues**,
`D(a) = diagonal ![λ₊, λ₋]` with `λ₊ = eᵃ + e⁻ᵃ`, `λ₋ = eᵃ - e⁻ᵃ`. -/
noncomputable def transferDiagonal (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![transferEigenvalueTop a, transferEigenvalueBot a]

@[simp] theorem transferDiagonal_zero_zero (a : ℝ) :
    transferDiagonal a 0 0 = transferEigenvalueTop a := by
  simp [transferDiagonal, Matrix.diagonal_apply_eq]

@[simp] theorem transferDiagonal_one_one (a : ℝ) :
    transferDiagonal a 1 1 = transferEigenvalueBot a := by
  simp [transferDiagonal, Matrix.diagonal_apply_eq]

@[simp] theorem transferDiagonal_zero_one (a : ℝ) : transferDiagonal a 0 1 = 0 := by
  simp [transferDiagonal, Matrix.diagonal_apply_ne]

@[simp] theorem transferDiagonal_one_zero (a : ℝ) : transferDiagonal a 1 0 = 0 := by
  simp [transferDiagonal, Matrix.diagonal_apply_ne]

/-- **Hadamard intertwining**: `T(a) · H = H · D(a)`. The Hadamard columns are
the eigenvectors of the transfer matrix, so conjugation by `H` diagonalizes
`T(a)`; this inverse-free form is the engine of the power formulas below. -/
theorem isingTransferMatrix1D_mul_hadamard (a : ℝ) :
    isingTransferMatrix1D a * hadamardMatrix
      = hadamardMatrix * transferDiagonal a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      transferEigenvalueTop, transferEigenvalueBot] <;>
    ring

/-- **Power intertwining**: `T(a)ᴺ · H = H · D(a)ᴺ`, by induction on `N` using
`isingTransferMatrix1D_mul_hadamard`. No matrix inverse is required. -/
theorem isingTransferMatrix1D_pow_mul_hadamard (a : ℝ) (N : ℕ) :
    isingTransferMatrix1D a ^ N * hadamardMatrix
      = hadamardMatrix * transferDiagonal a ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_assoc, isingTransferMatrix1D_mul_hadamard,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

/-- **Diagonalization of the power**: `T(a)ᴺ = H · D(a)ᴺ · H⁻¹`. -/
theorem isingTransferMatrix1D_pow_eq_conj (a : ℝ) (N : ℕ) :
    isingTransferMatrix1D a ^ N
      = hadamardMatrix * transferDiagonal a ^ N * hadamardMatrix⁻¹ := by
  have h1 : hadamardMatrix * hadamardMatrix⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hadamardMatrix_isUnit_det
  calc
    isingTransferMatrix1D a ^ N
        = isingTransferMatrix1D a ^ N * (hadamardMatrix * hadamardMatrix⁻¹) := by
          rw [h1, Matrix.mul_one]
    _ = isingTransferMatrix1D a ^ N * hadamardMatrix * hadamardMatrix⁻¹ := by
          rw [← Matrix.mul_assoc]
    _ = hadamardMatrix * transferDiagonal a ^ N * hadamardMatrix⁻¹ := by
          rw [isingTransferMatrix1D_pow_mul_hadamard]

/-- The `N`-th power of `D(a)` is `diagonal ![λ₊ᴺ, λ₋ᴺ]`. -/
theorem transferDiagonal_pow (a : ℝ) (N : ℕ) :
    transferDiagonal a ^ N
      = Matrix.diagonal ![transferEigenvalueTop a ^ N, transferEigenvalueBot a ^ N] := by
  rw [transferDiagonal, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp [Pi.pow_apply]

/-- **Trace of the power = cyclic-chain partition function** (Glimm–Jaffe §17.1):
`Tr(T(a)ᴺ) = λ₊ᴺ + λ₋ᴺ`.  This is the partition function `Z_N` of the `N`-site
cyclic Ising chain at zero field, written via the transfer matrix.  Derived from
the diagonalization `T(a)ᴺ = H·D(a)ᴺ·H⁻¹` by cycling `H⁻¹` past the trace
(`trace_mul_comm`, `H⁻¹·H = 1`) and reading off the diagonal of `D(a)ᴺ`. -/
theorem trace_isingTransferMatrix1D_pow (a : ℝ) (N : ℕ) :
    (isingTransferMatrix1D a ^ N).trace
      = transferEigenvalueTop a ^ N + transferEigenvalueBot a ^ N := by
  rw [isingTransferMatrix1D_pow_eq_conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hadamardMatrix_isUnit_det, Matrix.one_mul,
    transferDiagonal_pow, Matrix.trace_fin_two, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq]
  simp

/-- **Determinant of the power**: `det(T(a)ᴺ) = (λ₊·λ₋)ᴺ`.  Combines
`Matrix.det_pow` with the single-step determinant `det_isingTransferMatrix1D`. -/
theorem det_isingTransferMatrix1D_pow (a : ℝ) (N : ℕ) :
    (isingTransferMatrix1D a ^ N).det
      = (transferEigenvalueTop a * transferEigenvalueBot a) ^ N := by
  rw [Matrix.det_pow, det_isingTransferMatrix1D]

end TransferMatrix

end IsingModel
