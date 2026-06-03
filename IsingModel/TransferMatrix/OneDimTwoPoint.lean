import IsingModel.TransferMatrix.OneDimPower
import IsingModel.TransferMatrix.OneDimFreeEnergy

/-!
# Two-point function of the 1D Ising chain via the transfer matrix (GJ §17.1)

The transfer-matrix expression for the two-point function of the one-dimensional
Ising chain is `Tr(S·Tⁿ·S·T^{N-n}) / Tr(Tᴺ)`, where `S = diag(1, -1)` is the spin
operator and `T = isingTransferMatrix1D a` (`a = β J`).  (Its identification with
the Gibbs correlation `⟨σ₀σₙ⟩` via the cyclic config sum is a subsequent step; here
we compute the transfer-matrix ratio itself.)  The spin operator swaps
the two Hadamard eigenvectors of `T` (`S·H = H·P` with `P` the `2×2` swap), so

  `Tr(S·Tⁿ·S·T^{m}) = λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`   (`m = N - n`),

and the correlation ratio tends to the geometric decay

  `Tr(S·Tⁿ·S·T^{N-n}) / Tr(Tᴺ) → (λ₋/λ₊)ⁿ = (tanh βJ)ⁿ`   as `N → ∞`,

the exact exponential decay of the 1D Ising correlation with rate `-log tanh βJ`
(Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix
open Filter Topology

/-- The **spin operator** `S = diag(1, -1)` acting on the two-element spin space
`Fin 2`. -/
def spinOperator : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

/-- The `2 × 2` **swap matrix** `P`, exchanging the two basis vectors:
`P i j = 1` iff `i ≠ j`. -/
def swapMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = j then 0 else 1

@[simp] theorem swapMatrix_zero_zero : swapMatrix 0 0 = 0 := by simp [swapMatrix]
@[simp] theorem swapMatrix_zero_one : swapMatrix 0 1 = 1 := by simp [swapMatrix]
@[simp] theorem swapMatrix_one_zero : swapMatrix 1 0 = 1 := by simp [swapMatrix]
@[simp] theorem swapMatrix_one_one : swapMatrix 1 1 = 0 := by simp [swapMatrix]

/-- **The spin operator swaps the Hadamard eigenvectors**: `S · H = H · P`.  Since
`S` maps the symmetric eigenvector `(1,1)` to the antisymmetric `(1,-1)` and vice
versa, conjugation by `H` turns `S` into the swap `P`. -/
theorem spinOperator_mul_hadamard :
    spinOperator * hadamardMatrix = hadamardMatrix * swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinOperator, hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]

/-- Conjugation of the spin operator by the Hadamard matrix is the swap:
`H⁻¹ · S · H = P`. -/
theorem hadamardInv_mul_spinOperator_mul_hadamard :
    hadamardMatrix⁻¹ * spinOperator * hadamardMatrix = swapMatrix := by
  rw [Matrix.mul_assoc, spinOperator_mul_hadamard, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hadamardMatrix_isUnit_det, Matrix.one_mul]

/-- The swap matrix conjugates a diagonal matrix by exchanging its entries:
`P · diagonal ![x, y] · P = diagonal ![y, x]`. -/
theorem swapMatrix_mul_diagonal_mul_swapMatrix (x y : ℝ) :
    swapMatrix * Matrix.diagonal ![x, y] * swapMatrix = Matrix.diagonal ![y, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

/-- The swap matrix conjugates the eigenvalue diagonal power by exchanging the
two eigenvalues: `P · D(a)ᵏ · P = diagonal ![λ₋ᵏ, λ₊ᵏ]`. -/
theorem swapMatrix_mul_transferDiagonal_pow_mul_swapMatrix (a : ℝ) (k : ℕ) :
    swapMatrix * transferDiagonal a ^ k * swapMatrix
      = Matrix.diagonal ![transferEigenvalueBot a ^ k, transferEigenvalueTop a ^ k] := by
  rw [transferDiagonal_pow, swapMatrix_mul_diagonal_mul_swapMatrix]

/-- The spin operator times a transfer-matrix power, in conjugated form:
`S · Tⁿ = H · P · D(a)ⁿ · H⁻¹`. -/
theorem spinOperator_mul_pow (a : ℝ) (n : ℕ) :
    spinOperator * isingTransferMatrix1D a ^ n
      = hadamardMatrix * swapMatrix * transferDiagonal a ^ n * hadamardMatrix⁻¹ := by
  rw [isingTransferMatrix1D_pow_eq_conj]
  simp only [← Matrix.mul_assoc, spinOperator_mul_hadamard]

/-- **Transfer-matrix two-point trace** (Glimm–Jaffe §17.1):
`Tr(S·Tⁿ·S·Tᵐ) = λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`.  The spin operators turn into swaps under
the Hadamard diagonalization, exchanging the eigenvalue contributions. -/
theorem twoPointTrace (a : ℝ) (n m : ℕ) :
    (spinOperator * isingTransferMatrix1D a ^ n * spinOperator
        * isingTransferMatrix1D a ^ m).trace
      = transferEigenvalueBot a ^ n * transferEigenvalueTop a ^ m
        + transferEigenvalueTop a ^ n * transferEigenvalueBot a ^ m := by
  have hHH : hadamardMatrix⁻¹ * hadamardMatrix = 1 :=
    Matrix.nonsing_inv_mul _ hadamardMatrix_isUnit_det
  have hexpand : spinOperator * isingTransferMatrix1D a ^ n * spinOperator
      * isingTransferMatrix1D a ^ m
      = hadamardMatrix
        * (swapMatrix * transferDiagonal a ^ n * swapMatrix * transferDiagonal a ^ m)
        * hadamardMatrix⁻¹ := by
    rw [Matrix.mul_assoc (spinOperator * isingTransferMatrix1D a ^ n),
      spinOperator_mul_pow, spinOperator_mul_pow]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc hadamardMatrix⁻¹ hadamardMatrix, hHH, Matrix.one_mul]
  rw [hexpand, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hHH, Matrix.one_mul,
    swapMatrix_mul_transferDiagonal_pow_mul_swapMatrix, transferDiagonal_pow,
    Matrix.diagonal_mul_diagonal, Matrix.trace_fin_two, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq]
  simp

/-- The **transfer-matrix two-point ratio** at finite volume `N`,
`Tr(S·Tⁿ·S·T^{N-n}) / Tr(Tᴺ)`.  This is the transfer-matrix expression for the
1D Ising correlation `⟨σ₀σₙ⟩`; the identification with the Gibbs correlation via
the cyclic config sum is left for a subsequent step. -/
noncomputable def twoPointCorrelation (a : ℝ) (n N : ℕ) : ℝ :=
  (spinOperator * isingTransferMatrix1D a ^ n * spinOperator
      * isingTransferMatrix1D a ^ (N - n)).trace
    / (isingTransferMatrix1D a ^ N).trace

/-- **Closed form of the transfer-matrix two-point correlation**:
`⟨σ₀σₙ⟩_N = (λ₋ⁿ·λ₊^{N-n} + λ₊ⁿ·λ₋^{N-n}) / (λ₊ᴺ + λ₋ᴺ)`.  Direct from
`twoPointTrace` and `trace_isingTransferMatrix1D_pow`. -/
theorem twoPointCorrelation_eq (a : ℝ) (n N : ℕ) :
    twoPointCorrelation a n N
      = (transferEigenvalueBot a ^ n * transferEigenvalueTop a ^ (N - n)
          + transferEigenvalueTop a ^ n * transferEigenvalueBot a ^ (N - n))
        / (transferEigenvalueTop a ^ N + transferEigenvalueBot a ^ N) := by
  rw [twoPointCorrelation, twoPointTrace, trace_isingTransferMatrix1D_pow]

/-- The two-point correlation in terms of the eigenvalue ratio `r = λ₋/λ₊ = tanh a`:
for `n ≤ N` and `a > 0`,
`⟨σ₀σₙ⟩_N = (rⁿ + r^{N-n}) / (1 + rᴺ)`.  The dominant eigenvalue `λ₊ᴺ` cancels
between numerator and denominator. -/
theorem twoPointCorrelation_eq_ratio (a : ℝ) (n N : ℕ) (hnN : n ≤ N) :
    twoPointCorrelation a n N
      = ((transferEigenvalueBot a / transferEigenvalueTop a) ^ n
          + (transferEigenvalueBot a / transferEigenvalueTop a) ^ (N - n))
        / (1 + (transferEigenvalueBot a / transferEigenvalueTop a) ^ N) := by
  have hpos : 0 < transferEigenvalueTop a := transferEigenvalueTop_pos a
  obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
  rw [twoPointCorrelation_eq, Nat.add_sub_cancel_left, div_pow, div_pow, div_pow]
  rw [pow_add]
  field_simp

/-- **Exponential decay of the 1D Ising two-point function** (Glimm–Jaffe §17.1):
for `a = β J > 0`, the transfer-matrix two-point correlation converges to the
geometric decay `⟨σ₀σₙ⟩_N → (tanh βJ)ⁿ` as the chain length `N → ∞`.  The
subdominant eigenvalue ratio `r = tanh a ∈ (0,1)` makes the boundary terms
`r^{N-n}` and `rᴺ` vanish, leaving `rⁿ = (tanh βJ)ⁿ`. -/
theorem tendsto_twoPointCorrelation (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Tendsto (fun N => twoPointCorrelation a n N) atTop (𝓝 (Real.tanh a ^ n)) := by
  set r := transferEigenvalueBot a / transferEigenvalueTop a with hr
  have hr0 : 0 ≤ r := (transferEigenvalue_ratio_pos ha).le
  have hr1 : r < 1 := transferEigenvalue_ratio_lt_one a
  have hrtanh : r = Real.tanh a := transferEigenvalue_ratio a
  -- eventually (N ≥ n) the correlation equals (rⁿ + r^{N-n})/(1 + rᴺ)
  have heq : ∀ᶠ N in atTop, twoPointCorrelation a n N
      = (r ^ n + r ^ (N - n)) / (1 + r ^ N) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [twoPointCorrelation_eq_ratio a n N hN]
  -- r^{N-n} → 0 and rᴺ → 0
  have hpowN : Tendsto (fun N : ℕ => r ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hpowSub : Tendsto (fun N : ℕ => r ^ (N - n)) atTop (𝓝 0) :=
    hpowN.comp (tendsto_sub_atTop_nat n)
  have hnum : Tendsto (fun N : ℕ => r ^ n + r ^ (N - n)) atTop (𝓝 (r ^ n)) := by
    simpa using tendsto_const_nhds.add hpowSub
  have hden : Tendsto (fun N : ℕ => 1 + r ^ N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hpowN
  have hlim : Tendsto (fun N : ℕ => (r ^ n + r ^ (N - n)) / (1 + r ^ N))
      atTop (𝓝 (r ^ n / 1)) := hnum.div hden (by norm_num)
  rw [div_one] at hlim
  rw [← hrtanh]
  exact hlim.congr' (heq.mono fun N h => h.symm)

end TransferMatrix

end IsingModel
