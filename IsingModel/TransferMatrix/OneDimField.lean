import IsingModel.TransferMatrix.OneDim

/-!
# 1D Ising transfer matrix with external field (Glimm–Jaffe §17.1)

The zero-field 1D Ising transfer matrix `T(a) = !![eᵃ, e⁻ᵃ; e⁻ᵃ, eᵃ]`
(`TransferMatrix/OneDim.lean`) extends to a **general external field** `h ≠ 0`.
Writing `a = β J` and `b = β h`, the symmetric transfer matrix is

  `T(a, b)ᵢⱼ = exp (a · sᵢ · sⱼ + (b/2) · (sᵢ + sⱼ))`,   `s = (+1, -1)`,

so

  `T(a, b) = !![e^{a+b}, e^{-a}; e^{-a}, e^{a-b}]`.

Unlike the zero-field case, the eigenvectors are no longer the fixed Hadamard
pair, so the spectral data is organised through the characteristic polynomial.
With trace `2 eᵃ cosh b` and determinant `e^{2a} − e^{-2a}`, the eigenvalues are

  `λ± = eᵃ cosh b ± √D`,   `D = e^{2a} sinh²b + e^{-2a} > 0`,

(`λ+ > λ- > 0` for `a > 0`), satisfying Vieta's relations `λ+ + λ- = trace`,
`λ+ · λ- = det` and the characteristic equation `λ² = trace·λ − det`.  At `b = 0`
the matrix and its eigenvalues reduce to the zero-field objects.

This is the foundational PR of the general external-field 1D programme
(Issue #3538); the partition function `Z_N = λ+^N + λ-^N`, free energy,
magnetization `m(h)`, and susceptibility `∂_h m` follow in later PRs.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), pp. 304–306.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.3.
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix

/-- The **1D Ising transfer matrix with external field**, parametrised by
`a = β J` and `b = β h`: the `2 × 2` matrix
`T(a, b)ᵢⱼ = exp (a · sᵢ · sⱼ + (b/2) · (sᵢ + sⱼ))` (Glimm–Jaffe §17.1).
Explicitly `T(a, b) = !![e^{a+b}, e^{-a}; e^{-a}, e^{a-b}]`. -/
noncomputable def isingTransferMatrix1DField (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => Real.exp (a * spin1D i * spin1D j + b / 2 * (spin1D i + spin1D j))

@[simp] theorem isingTransferMatrix1DField_zero_zero (a b : ℝ) :
    isingTransferMatrix1DField a b 0 0 = Real.exp (a + b) := by
  simp only [isingTransferMatrix1DField, Matrix.of_apply, spin1D_zero]
  congr 1; ring

@[simp] theorem isingTransferMatrix1DField_zero_one (a b : ℝ) :
    isingTransferMatrix1DField a b 0 1 = Real.exp (-a) := by
  simp only [isingTransferMatrix1DField, Matrix.of_apply, spin1D_zero, spin1D_one]
  congr 1; ring

@[simp] theorem isingTransferMatrix1DField_one_zero (a b : ℝ) :
    isingTransferMatrix1DField a b 1 0 = Real.exp (-a) := by
  simp only [isingTransferMatrix1DField, Matrix.of_apply, spin1D_zero, spin1D_one]
  congr 1; ring

@[simp] theorem isingTransferMatrix1DField_one_one (a b : ℝ) :
    isingTransferMatrix1DField a b 1 1 = Real.exp (a - b) := by
  simp only [isingTransferMatrix1DField, Matrix.of_apply, spin1D_one]
  congr 1; ring

/-- The field transfer matrix is symmetric (`Tᵀ = T`), reflecting the symmetry
`sᵢ · sⱼ = sⱼ · sᵢ` and `sᵢ + sⱼ = sⱼ + sᵢ`. -/
theorem isingTransferMatrix1DField_transpose (a b : ℝ) :
    (isingTransferMatrix1DField a b)ᵀ = isingTransferMatrix1DField a b := by
  ext i j
  simp only [Matrix.transpose_apply, isingTransferMatrix1DField, Matrix.of_apply]
  congr 1; ring

/-- All entries of the field transfer matrix are strictly positive. -/
theorem isingTransferMatrix1DField_pos (a b : ℝ) (i j : Fin 2) :
    0 < isingTransferMatrix1DField a b i j := Real.exp_pos _

/-- The **discriminant** of the field transfer matrix's characteristic
polynomial (up to the factor `4`): `D(a, b) = e^{2a} sinh²b + e^{-2a}`. -/
noncomputable def fieldTransferDiscriminant (a b : ℝ) : ℝ :=
  Real.exp (2 * a) * Real.sinh b ^ 2 + Real.exp (-(2 * a))

/-- The discriminant is strictly positive (so the eigenvalues are real and
distinct). -/
theorem fieldTransferDiscriminant_pos (a b : ℝ) :
    0 < fieldTransferDiscriminant a b := by
  have h1 : 0 ≤ Real.exp (2 * a) * Real.sinh b ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have h2 : 0 < Real.exp (-(2 * a)) := Real.exp_pos _
  rw [fieldTransferDiscriminant]; linarith

/-- The **larger eigenvalue** of the field transfer matrix,
`λ+(a, b) = eᵃ cosh b + √D`. -/
noncomputable def fieldTransferEigenvalueTop (a b : ℝ) : ℝ :=
  Real.exp a * Real.cosh b + Real.sqrt (fieldTransferDiscriminant a b)

/-- The **smaller eigenvalue** of the field transfer matrix,
`λ-(a, b) = eᵃ cosh b − √D`. -/
noncomputable def fieldTransferEigenvalueBot (a b : ℝ) : ℝ :=
  Real.exp a * Real.cosh b - Real.sqrt (fieldTransferDiscriminant a b)

/-- The trace of the field transfer matrix is `2 eᵃ cosh b`. -/
theorem trace_isingTransferMatrix1DField (a b : ℝ) :
    (isingTransferMatrix1DField a b).trace = 2 * Real.exp a * Real.cosh b := by
  have hb : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  rw [Matrix.trace_fin_two, isingTransferMatrix1DField_zero_zero,
    isingTransferMatrix1DField_one_one, Real.cosh_eq, Real.exp_add, Real.exp_sub,
    Real.exp_neg]
  field_simp

/-- The determinant of the field transfer matrix is `e^{2a} − e^{-2a}`. -/
theorem det_isingTransferMatrix1DField (a b : ℝ) :
    (isingTransferMatrix1DField a b).det = Real.exp (2 * a) - Real.exp (-(2 * a)) := by
  rw [Matrix.det_fin_two, isingTransferMatrix1DField_zero_zero,
    isingTransferMatrix1DField_one_one, isingTransferMatrix1DField_zero_one,
    isingTransferMatrix1DField_one_zero, ← Real.exp_add, ← Real.exp_add,
    show a + b + (a - b) = 2 * a from by ring, show -a + -a = -(2 * a) from by ring]

/-- **Vieta sum**: `λ+ + λ- = trace = 2 eᵃ cosh b`. -/
theorem fieldTransferEigenvalueTop_add_bot (a b : ℝ) :
    fieldTransferEigenvalueTop a b + fieldTransferEigenvalueBot a b
      = 2 * Real.exp a * Real.cosh b := by
  rw [fieldTransferEigenvalueTop, fieldTransferEigenvalueBot]; ring

/-- The eigenvalue sum equals the matrix trace. -/
theorem fieldTransferEigenvalueTop_add_bot_eq_trace (a b : ℝ) :
    fieldTransferEigenvalueTop a b + fieldTransferEigenvalueBot a b
      = (isingTransferMatrix1DField a b).trace := by
  rw [fieldTransferEigenvalueTop_add_bot, trace_isingTransferMatrix1DField]

/-- **Vieta product**: `λ+ · λ- = det = e^{2a} − e^{-2a}`.  Uses
`(X + √D)(X − √D) = X² − D` with `X = eᵃ cosh b`, `√D ² = D` (as `D ≥ 0`), and
`cosh²b = sinh²b + 1`. -/
theorem fieldTransferEigenvalueTop_mul_bot (a b : ℝ) :
    fieldTransferEigenvalueTop a b * fieldTransferEigenvalueBot a b
      = Real.exp (2 * a) - Real.exp (-(2 * a)) := by
  have hS : Real.sqrt (fieldTransferDiscriminant a b) ^ 2 = fieldTransferDiscriminant a b :=
    Real.sq_sqrt (fieldTransferDiscriminant_pos a b).le
  have hX : (Real.exp a * Real.cosh b) ^ 2 = Real.exp (2 * a) * Real.cosh b ^ 2 := by
    rw [mul_pow, pow_two (Real.exp a), ← Real.exp_add, show a + a = 2 * a from by ring]
  rw [fieldTransferEigenvalueTop, fieldTransferEigenvalueBot,
    show (Real.exp a * Real.cosh b + Real.sqrt (fieldTransferDiscriminant a b)) *
        (Real.exp a * Real.cosh b - Real.sqrt (fieldTransferDiscriminant a b))
      = (Real.exp a * Real.cosh b) ^ 2 - Real.sqrt (fieldTransferDiscriminant a b) ^ 2
      from by ring,
    hS, hX, fieldTransferDiscriminant, Real.cosh_sq]
  ring

/-- The eigenvalue product equals the matrix determinant. -/
theorem fieldTransferEigenvalueTop_mul_bot_eq_det (a b : ℝ) :
    fieldTransferEigenvalueTop a b * fieldTransferEigenvalueBot a b
      = (isingTransferMatrix1DField a b).det := by
  rw [fieldTransferEigenvalueTop_mul_bot, det_isingTransferMatrix1DField]

/-- **Characteristic equation for `λ+`**: `λ+² = trace·λ+ − det`, i.e.
`λ+² = 2 eᵃ cosh b · λ+ − (e^{2a} − e^{-2a})`. -/
theorem fieldTransferEigenvalueTop_sq (a b : ℝ) :
    fieldTransferEigenvalueTop a b ^ 2
      = 2 * Real.exp a * Real.cosh b * fieldTransferEigenvalueTop a b
        - (Real.exp (2 * a) - Real.exp (-(2 * a))) := by
  rw [← fieldTransferEigenvalueTop_add_bot, ← fieldTransferEigenvalueTop_mul_bot]; ring

/-- **Characteristic equation for `λ-`**: `λ-² = trace·λ- − det`. -/
theorem fieldTransferEigenvalueBot_sq (a b : ℝ) :
    fieldTransferEigenvalueBot a b ^ 2
      = 2 * Real.exp a * Real.cosh b * fieldTransferEigenvalueBot a b
        - (Real.exp (2 * a) - Real.exp (-(2 * a))) := by
  rw [← fieldTransferEigenvalueTop_add_bot, ← fieldTransferEigenvalueTop_mul_bot]; ring

/-- `λ- < λ+` (the discriminant is strictly positive). -/
theorem fieldTransferEigenvalueBot_lt_top (a b : ℝ) :
    fieldTransferEigenvalueBot a b < fieldTransferEigenvalueTop a b := by
  rw [fieldTransferEigenvalueBot, fieldTransferEigenvalueTop]
  have : 0 < Real.sqrt (fieldTransferDiscriminant a b) :=
    Real.sqrt_pos.mpr (fieldTransferDiscriminant_pos a b)
  linarith

/-- The top eigenvalue is strictly positive. -/
theorem fieldTransferEigenvalueTop_pos (a b : ℝ) :
    0 < fieldTransferEigenvalueTop a b := by
  rw [fieldTransferEigenvalueTop]
  have h1 : 0 < Real.exp a * Real.cosh b := mul_pos (Real.exp_pos _) (Real.cosh_pos _)
  have h2 : 0 ≤ Real.sqrt (fieldTransferDiscriminant a b) := Real.sqrt_nonneg _
  linarith

/-- The bottom eigenvalue is strictly positive for `a = β J > 0` (ferromagnetic):
`λ+ · λ- = e^{2a} − e^{-2a} > 0` and `λ+ > 0`. -/
theorem fieldTransferEigenvalueBot_pos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    0 < fieldTransferEigenvalueBot a b := by
  have hprod := fieldTransferEigenvalueTop_mul_bot a b
  have hpos : 0 < Real.exp (2 * a) - Real.exp (-(2 * a)) := by
    have hlt : Real.exp (-(2 * a)) < Real.exp (2 * a) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have htop := fieldTransferEigenvalueTop_pos a b
  by_contra h
  rw [not_lt] at h
  have hle : fieldTransferEigenvalueTop a b * fieldTransferEigenvalueBot a b ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htop.le h
  rw [hprod] at hle
  linarith

/-! ## Zero-field bridge -/

/-- At `b = 0` the field transfer matrix is the zero-field transfer matrix. -/
theorem isingTransferMatrix1DField_zero (a : ℝ) :
    isingTransferMatrix1DField a 0 = isingTransferMatrix1D a := by
  ext i j
  simp only [isingTransferMatrix1DField, isingTransferMatrix1D, Matrix.of_apply]
  congr 1; ring

/-- At `b = 0` the discriminant is `e^{-2a}`. -/
theorem fieldTransferDiscriminant_zero (a : ℝ) :
    fieldTransferDiscriminant a 0 = Real.exp (-(2 * a)) := by
  rw [fieldTransferDiscriminant, Real.sinh_zero]; ring

/-- At `b = 0` the top eigenvalue is the zero-field `λ+(a) = eᵃ + e⁻ᵃ`. -/
theorem fieldTransferEigenvalueTop_zero (a : ℝ) :
    fieldTransferEigenvalueTop a 0 = transferEigenvalueTop a := by
  rw [fieldTransferEigenvalueTop, fieldTransferDiscriminant_zero, Real.cosh_zero, mul_one,
    transferEigenvalueTop,
    show Real.exp (-(2 * a)) = Real.exp (-a) ^ 2 from by
      rw [pow_two, ← Real.exp_add]; congr 1; ring,
    Real.sqrt_sq (Real.exp_nonneg _)]

/-- At `b = 0` the bottom eigenvalue is the zero-field `λ-(a) = eᵃ − e⁻ᵃ`. -/
theorem fieldTransferEigenvalueBot_zero (a : ℝ) :
    fieldTransferEigenvalueBot a 0 = transferEigenvalueBot a := by
  rw [fieldTransferEigenvalueBot, fieldTransferDiscriminant_zero, Real.cosh_zero, mul_one,
    transferEigenvalueBot,
    show Real.exp (-(2 * a)) = Real.exp (-a) ^ 2 from by
      rw [pow_two, ← Real.exp_add]; congr 1; ring,
    Real.sqrt_sq (Real.exp_nonneg _)]

end TransferMatrix

end IsingModel
