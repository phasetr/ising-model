import IsingModel.TransferMatrix.OneDimField
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Partition function and free energy of the 1D Ising chain in a field (GJ §17.1)

Building on the field transfer matrix `T(a, b)` (`TransferMatrix/OneDimField.lean`),
this file evaluates the cyclic-chain partition function `Z_N = Tr(T(a, b)ᴺ)` and
the free-energy density.  Unlike the zero-field case there is no convenient
Hadamard eigenbasis, so the trace power is computed through the
**Cayley–Hamilton recurrence**: `T² = (tr T)·T − (det T)·1` gives the matrix
recurrence `T^{N+2} = tr·T^{N+1} − det·T^N`, hence the trace recurrence
`s_{N+2} = tr·s_{N+1} − det·s_N` with `s_N = Tr(Tᴺ)`.  The eigenvalue powers
`λ±ᴺ` satisfy the same second-order recurrence (the characteristic equation
`λ±² = tr·λ± − det`) with the same initial data `s₀ = 2 = λ₊⁰+λ₋⁰`,
`s₁ = tr = λ₊+λ₋`, so

  `Tr(T(a, b)ᴺ) = λ₊ᴺ + λ₋ᴺ`.

For `a = β J > 0` the subdominant ratio `λ₋/λ₊ ∈ (0,1)` gives the free-energy
density `(1/N) log Tr(Tᴺ) → log λ₊`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- **Cayley–Hamilton for the field transfer matrix** (`2 × 2`):
`T² = (tr T)·T − (det T)·1`, i.e.
`T² = (2 eᵃ cosh b)·T − (e^{2a} − e^{-2a})·1`. -/
theorem isingTransferMatrix1DField_sq (a b : ℝ) :
    isingTransferMatrix1DField a b ^ 2
      = (isingTransferMatrix1DField a b).trace • isingTransferMatrix1DField a b
        - (isingTransferMatrix1DField a b).det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  set T := isingTransferMatrix1DField a b with hT
  have h := Matrix.aeval_self_charpoly T
  rw [Matrix.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_one_mul] at h
  -- h : T ^ 2 - T.trace • T + T.det • 1 = 0
  rw [← sub_eq_zero,
    show T ^ 2 - (T.trace • T - T.det • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = T ^ 2 - T.trace • T + T.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) from by abel]
  exact h

/-- **Matrix power recurrence**: `T^{N+2} = (tr T)·T^{N+1} − (det T)·T^N`,
obtained by multiplying the Cayley–Hamilton identity by `T^N`. -/
theorem isingTransferMatrix1DField_pow_succ_succ (a b : ℝ) (N : ℕ) :
    isingTransferMatrix1DField a b ^ (N + 2)
      = (isingTransferMatrix1DField a b).trace • isingTransferMatrix1DField a b ^ (N + 1)
        - (isingTransferMatrix1DField a b).det • isingTransferMatrix1DField a b ^ N := by
  rw [pow_add, isingTransferMatrix1DField_sq, mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

/-- **Trace recurrence**: `Tr(T^{N+2}) = tr·Tr(T^{N+1}) − det·Tr(T^N)` with
`tr = 2 eᵃ cosh b`, `det = e^{2a} − e^{-2a}`, by linearity of the trace. -/
theorem trace_isingTransferMatrix1DField_pow_succ_succ (a b : ℝ) (N : ℕ) :
    (isingTransferMatrix1DField a b ^ (N + 2)).trace
      = (isingTransferMatrix1DField a b).trace
          * (isingTransferMatrix1DField a b ^ (N + 1)).trace
        - (isingTransferMatrix1DField a b).det
          * (isingTransferMatrix1DField a b ^ N).trace := by
  rw [isingTransferMatrix1DField_pow_succ_succ, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

/-- **Partition function of the 1D Ising chain in a field**
(Glimm–Jaffe §17.1): for all `N`,

`Tr(T(a, b)ᴺ) = λ₊(a, b)ᴺ + λ₋(a, b)ᴺ`.

Both sides satisfy the second-order recurrence `x_{N+2} = tr·x_{N+1} − det·x_N`
(trace side via Cayley–Hamilton, eigenvalue side via the characteristic equation
`λ±² = tr·λ± − det`) with the same initial data `x₀ = 2`, `x₁ = tr`. -/
theorem trace_isingTransferMatrix1DField_pow (a b : ℝ) (N : ℕ) :
    (isingTransferMatrix1DField a b ^ N).trace
      = fieldTransferEigenvalueTop a b ^ N + fieldTransferEigenvalueBot a b ^ N := by
  induction N using Nat.twoStepInduction with
  | zero => rw [pow_zero, Matrix.trace_one, pow_zero, pow_zero]; norm_num
  | one =>
    rw [pow_one, trace_isingTransferMatrix1DField, pow_one, pow_one,
      fieldTransferEigenvalueTop_add_bot]
  | more N ih0 ih1 =>
    rw [trace_isingTransferMatrix1DField_pow_succ_succ, ih1, ih0,
      trace_isingTransferMatrix1DField, det_isingTransferMatrix1DField]
    -- λ±^{N+2} = tr·λ±^{N+1} − det·λ±^N from the characteristic equation
    have htop : fieldTransferEigenvalueTop a b ^ (N + 2)
        = 2 * Real.exp a * Real.cosh b * fieldTransferEigenvalueTop a b ^ (N + 1)
          - (Real.exp (2 * a) - Real.exp (-(2 * a))) * fieldTransferEigenvalueTop a b ^ N := by
      rw [pow_add, fieldTransferEigenvalueTop_sq]; ring
    have hbot : fieldTransferEigenvalueBot a b ^ (N + 2)
        = 2 * Real.exp a * Real.cosh b * fieldTransferEigenvalueBot a b ^ (N + 1)
          - (Real.exp (2 * a) - Real.exp (-(2 * a))) * fieldTransferEigenvalueBot a b ^ N := by
      rw [pow_add, fieldTransferEigenvalueBot_sq]; ring
    rw [htop, hbot]; ring

/-- The dominant eigenvalue is strictly positive. -/
theorem fieldTransferEigenvalueTop_pos' (a b : ℝ) : 0 < fieldTransferEigenvalueTop a b :=
  fieldTransferEigenvalueTop_pos a b

/-- For `a = β J > 0` the subdominant-to-dominant ratio is in `[0,1)`:
`0 ≤ λ₋/λ₊ < 1` (since `0 < λ₋ < λ₊`). -/
theorem fieldTransferEigenvalue_ratio_nonneg {a : ℝ} (ha : 0 < a) (b : ℝ) :
    0 ≤ fieldTransferEigenvalueBot a b / fieldTransferEigenvalueTop a b :=
  div_nonneg (fieldTransferEigenvalueBot_pos ha b).le (fieldTransferEigenvalueTop_pos a b).le

/-- The subdominant-to-dominant ratio is strictly below one, `λ₋/λ₊ < 1`. -/
theorem fieldTransferEigenvalue_ratio_lt_one (a b : ℝ) :
    fieldTransferEigenvalueBot a b / fieldTransferEigenvalueTop a b < 1 :=
  (div_lt_one (fieldTransferEigenvalueTop_pos a b)).mpr (fieldTransferEigenvalueBot_lt_top a b)

/-- The powers of the eigenvalue ratio vanish, `(λ₋/λ₊)ᴺ → 0` (for `a > 0`). -/
theorem tendsto_fieldTransferEigenvalue_ratio_pow {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto
      (fun N : ℕ => (fieldTransferEigenvalueBot a b / fieldTransferEigenvalueTop a b) ^ N)
      atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (fieldTransferEigenvalue_ratio_nonneg ha b)
    (fieldTransferEigenvalue_ratio_lt_one a b)

/-- **Free-energy density from the eigenvalues** (Glimm–Jaffe §17.1): for
`a = β J > 0`,
`(1/N)·log(λ₊ᴺ + λ₋ᴺ) → log λ₊`.  The subdominant eigenvalue `λ₋ < λ₊`
contributes only the vanishing correction `(1/N)·log(1 + (λ₋/λ₊)ᴺ) → 0`. -/
theorem tendsto_log_fieldEigenvalueSum_div_nat {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun N : ℕ =>
        Real.log (fieldTransferEigenvalueTop a b ^ N
          + fieldTransferEigenvalueBot a b ^ N) / N)
      atTop (𝓝 (Real.log (fieldTransferEigenvalueTop a b))) := by
  set lt := fieldTransferEigenvalueTop a b with hlt_def
  set lb := fieldTransferEigenvalueBot a b with hlb_def
  have hlt : 0 < lt := fieldTransferEigenvalueTop_pos a b
  set r := lb / lt with hr_def
  have hr0 : 0 ≤ r := fieldTransferEigenvalue_ratio_nonneg ha b
  have hpow : Tendsto (fun N : ℕ => r ^ N) atTop (𝓝 0) :=
    tendsto_fieldTransferEigenvalue_ratio_pow ha b
  have hlog1 : Tendsto (fun N : ℕ => Real.log (1 + r ^ N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 1 + r ^ N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hpow
    have hcomp := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
    simpa [Real.log_one] using hcomp
  have hdiv : Tendsto (fun N : ℕ => Real.log (1 + r ^ N) / N) atTop (𝓝 0) := by
    have h := hlog1.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, ← div_eq_mul_one_div] using h
  have heq : ∀ᶠ N : ℕ in atTop,
      Real.log (lt ^ N + lb ^ N) / N = Real.log lt + Real.log (1 + r ^ N) / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hltN : 0 < lt ^ N := pow_pos hlt N
    have hfact : lt ^ N + lb ^ N = lt ^ N * (1 + r ^ N) := by
      rw [hr_def, div_pow, mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hltN)]
    rw [hfact, Real.log_mul (ne_of_gt hltN) (by positivity), Real.log_pow,
      add_div, mul_div_cancel_left₀ _ hN0]
  have hsum : Tendsto (fun N : ℕ => Real.log lt + Real.log (1 + r ^ N) / N)
      atTop (𝓝 (Real.log lt)) := by
    simpa using tendsto_const_nhds.add hdiv
  refine hsum.congr' ?_
  filter_upwards [heq] with N h
  exact h.symm

/-- **Free-energy density from the transfer-matrix trace** (Glimm–Jaffe §17.1):
for `a = β J > 0`,
`(1/N)·log Tr(T(a, b)ᴺ) → log λ₊`.  Since `Z_N = Tr(T(a, b)ᴺ)` is the cyclic-chain
partition function of the 1D Ising chain in a field, the limit is its free-energy
density. -/
theorem tendsto_log_trace_isingTransferMatrix1DField_pow_div_nat {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun N : ℕ => Real.log (isingTransferMatrix1DField a b ^ N).trace / N)
      atTop (𝓝 (Real.log (fieldTransferEigenvalueTop a b))) := by
  refine (tendsto_log_fieldEigenvalueSum_div_nat ha b).congr fun N => ?_
  rw [trace_isingTransferMatrix1DField_pow]

end TransferMatrix

end IsingModel
