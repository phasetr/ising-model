import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# 1D Ising transfer matrix (Glimm–Jaffe §17.1, §17.5)

The transfer-matrix method of Glimm–Jaffe §17.1 (and the source of the
exponential decay in §17.5, pp. 311–312) is, in its simplest concrete instance,
the `2 × 2` real matrix governing the one-dimensional Ising chain at zero
external field.  Indexing the two spin values `s : Fin 2 → ℝ` by `s 0 = +1`,
`s 1 = -1`, the (zero-field) transfer matrix is

  `T(a)ᵢⱼ = exp (a · sᵢ · sⱼ)`,   `a = β J`,

so `T(a) = !![eᵃ, e⁻ᵃ; e⁻ᵃ, eᵃ]`.  This file records its spectral data with no
general-`d` spectral framework: the symmetric `2 × 2` matrix, its trace and
determinant, the Hadamard-basis eigenpairs

  `T · (1, 1) = λ₊ · (1, 1)`,   `T · (1, -1) = λ₋ · (1, -1)`,

with `λ₊ = eᵃ + e⁻ᵃ = 2 cosh a` and `λ₋ = eᵃ - e⁻ᵃ = 2 sinh a`, and the
spectral ratio `λ₋ / λ₊ = tanh a` — the source of the correlation decay rate
`-log tanh a` for the one-dimensional chain.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), §17.5
  (pp. 311–312, mass and exponential decay).
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix

/-- The two spin values of the 1D Ising chain, `s 0 = +1` and `s 1 = -1`. -/
def spin1D : Fin 2 → ℝ := ![1, -1]

@[simp] theorem spin1D_zero : spin1D 0 = 1 := rfl

@[simp] theorem spin1D_one : spin1D 1 = -1 := rfl

/-- The **1D Ising transfer matrix** at zero external field with parameter
`a = β J`: the `2 × 2` matrix `T(a)ᵢⱼ = exp (a · sᵢ · sⱼ)` (Glimm–Jaffe §17.1).
Explicitly `T(a) = !![eᵃ, e⁻ᵃ; e⁻ᵃ, eᵃ]`. -/
noncomputable def isingTransferMatrix1D (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => Real.exp (a * spin1D i * spin1D j)

@[simp] theorem isingTransferMatrix1D_zero_zero (a : ℝ) :
    isingTransferMatrix1D a 0 0 = Real.exp a := by
  simp [isingTransferMatrix1D]

@[simp] theorem isingTransferMatrix1D_zero_one (a : ℝ) :
    isingTransferMatrix1D a 0 1 = Real.exp (-a) := by
  simp [isingTransferMatrix1D]

@[simp] theorem isingTransferMatrix1D_one_zero (a : ℝ) :
    isingTransferMatrix1D a 1 0 = Real.exp (-a) := by
  simp [isingTransferMatrix1D]

@[simp] theorem isingTransferMatrix1D_one_one (a : ℝ) :
    isingTransferMatrix1D a 1 1 = Real.exp a := by
  simp [isingTransferMatrix1D]

/-- The 1D Ising transfer matrix is symmetric (`Tᵀ = T`), reflecting the
symmetry `sᵢ · sⱼ = sⱼ · sᵢ` of the spin coupling. -/
theorem isingTransferMatrix1D_transpose (a : ℝ) :
    (isingTransferMatrix1D a)ᵀ = isingTransferMatrix1D a := by
  ext i j
  simp only [Matrix.transpose_apply, isingTransferMatrix1D, Matrix.of_apply]
  ring_nf

/-- All entries of the 1D Ising transfer matrix are strictly positive. -/
theorem isingTransferMatrix1D_pos (a : ℝ) (i j : Fin 2) :
    0 < isingTransferMatrix1D a i j := Real.exp_pos _

/-- The larger transfer-matrix eigenvalue `λ₊(a) = eᵃ + e⁻ᵃ`. -/
noncomputable def transferEigenvalueTop (a : ℝ) : ℝ := Real.exp a + Real.exp (-a)

/-- The smaller transfer-matrix eigenvalue `λ₋(a) = eᵃ - e⁻ᵃ`. -/
noncomputable def transferEigenvalueBot (a : ℝ) : ℝ := Real.exp a - Real.exp (-a)

/-- The top eigenvalue equals `2 cosh a`. -/
theorem transferEigenvalueTop_eq (a : ℝ) :
    transferEigenvalueTop a = 2 * Real.cosh a := by
  rw [transferEigenvalueTop, Real.cosh_eq]; ring

/-- The bottom eigenvalue equals `2 sinh a`. -/
theorem transferEigenvalueBot_eq (a : ℝ) :
    transferEigenvalueBot a = 2 * Real.sinh a := by
  rw [transferEigenvalueBot, Real.sinh_eq]; ring

/-- The top eigenvalue is strictly positive. -/
theorem transferEigenvalueTop_pos (a : ℝ) : 0 < transferEigenvalueTop a := by
  rw [transferEigenvalueTop_eq]
  exact mul_pos two_pos (Real.cosh_pos a)

/-- The trace of the 1D Ising transfer matrix is `2 eᵃ = λ₊ + λ₋`. -/
theorem trace_isingTransferMatrix1D (a : ℝ) :
    (isingTransferMatrix1D a).trace = transferEigenvalueTop a + transferEigenvalueBot a := by
  rw [Matrix.trace_fin_two]
  simp only [isingTransferMatrix1D_zero_zero, isingTransferMatrix1D_one_one,
    transferEigenvalueTop, transferEigenvalueBot]
  ring

/-- The determinant of the 1D Ising transfer matrix is
`e²ᵃ - e⁻²ᵃ = λ₊ · λ₋`. -/
theorem det_isingTransferMatrix1D (a : ℝ) :
    (isingTransferMatrix1D a).det = transferEigenvalueTop a * transferEigenvalueBot a := by
  rw [Matrix.det_fin_two]
  simp only [isingTransferMatrix1D_zero_zero, isingTransferMatrix1D_one_one,
    isingTransferMatrix1D_zero_one, isingTransferMatrix1D_one_zero,
    transferEigenvalueTop, transferEigenvalueBot]
  ring

/-- The symmetric Hadamard eigenvector `(1, 1)` of the transfer matrix. -/
def hadamardTop : Fin 2 → ℝ := ![1, 1]

/-- The antisymmetric Hadamard eigenvector `(1, -1)` of the transfer matrix. -/
def hadamardBot : Fin 2 → ℝ := ![1, -1]

/-- **Top eigenpair**: `T(a) · (1, 1) = λ₊ · (1, 1)` with `λ₊ = eᵃ + e⁻ᵃ`. The
symmetric Hadamard vector is the Perron–Frobenius eigenvector. -/
theorem isingTransferMatrix1D_mulVec_hadamardTop (a : ℝ) :
    (isingTransferMatrix1D a).mulVec hadamardTop
      = transferEigenvalueTop a • hadamardTop := by
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hadamardTop,
      transferEigenvalueTop]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hadamardTop,
      transferEigenvalueTop]
    ring

/-- **Bottom eigenpair**: `T(a) · (1, -1) = λ₋ · (1, -1)` with `λ₋ = eᵃ - e⁻ᵃ`. -/
theorem isingTransferMatrix1D_mulVec_hadamardBot (a : ℝ) :
    (isingTransferMatrix1D a).mulVec hadamardBot
      = transferEigenvalueBot a • hadamardBot := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hadamardBot,
      transferEigenvalueBot] <;> ring

/-- **Spectral ratio**: `λ₋ / λ₊ = tanh a`. This ratio of the subdominant to the
dominant transfer-matrix eigenvalue is the source of the correlation decay rate
`-log tanh a` for the one-dimensional Ising chain (Glimm–Jaffe §17.5). -/
theorem transferEigenvalue_ratio (a : ℝ) :
    transferEigenvalueBot a / transferEigenvalueTop a = Real.tanh a := by
  rw [transferEigenvalueTop_eq, transferEigenvalueBot_eq, Real.tanh_eq_sinh_div_cosh]
  rw [mul_div_mul_left _ _ (two_ne_zero)]

end TransferMatrix

end IsingModel
