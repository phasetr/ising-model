import IsingModel.TransferMatrix.LayerGibbs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

/-!
# Finite layer spectral scaffold (GJ §17.1)

This file prepares the finite cyclic layer transfer matrix for later
Perron--Frobenius and symmetric spectral arguments.  For a positive one-layer
weight `u`, the generally non-symmetric transfer matrix
`T a b = u b * k a b` is diagonally similar to the balanced matrix

`S a b = sqrt (u a) * k a b * sqrt (u b)`.

When the transition kernel `k` is symmetric, `S` is a symmetric real matrix.
The file records the diagonal similarity and the induced invariance of the
partition trace and the two-insertion marked trace.  It deliberately does not
prove a Perron--Frobenius theorem, a spectral gap, thermodynamic limits, or
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Positivity vocabulary -/

/-- Entrywise nonnegativity for a finite real matrix. -/
def MatrixEntrywiseNonnegative (M : Matrix Ω Ω ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Entrywise strict positivity for a finite real matrix. -/
def MatrixEntrywisePositive (M : Matrix Ω Ω ℝ) : Prop :=
  ∀ i j, 0 < M i j

/-- Nonnegativity for a finite real vector. -/
def VectorNonnegative (v : Ω → ℝ) : Prop :=
  ∀ i, 0 ≤ v i

/-- Strict positivity for a finite real vector. -/
def VectorPositive (v : Ω → ℝ) : Prop :=
  ∀ i, 0 < v i

omit [Fintype Ω] [DecidableEq Ω] in
/-- An entrywise positive matrix is entrywise nonnegative. -/
theorem matrixEntrywisePositive_nonnegative {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) : MatrixEntrywiseNonnegative M :=
  fun i j => (hM i j).le

omit [Fintype Ω] [DecidableEq Ω] in
/-- The ordinary layer transfer matrix is entrywise positive when the layer and
transition weights are positive. -/
theorem layerTransferMatrix_entrywisePositive
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) :
    MatrixEntrywisePositive (layerTransferMatrix u k) :=
  fun a b => mul_pos (hu b) (hk a b)

omit [DecidableEq Ω] in
/-- The product of two entrywise positive finite matrices is entrywise positive
when the index type is nonempty. -/
theorem matrixEntrywisePositive_mul [Nonempty Ω] {M N : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) (hN : MatrixEntrywisePositive N) :
    MatrixEntrywisePositive (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_pos (fun k _ => mul_pos (hM i k) (hN k j)) Finset.univ_nonempty

/-- Positive powers of an entrywise positive matrix remain entrywise positive. -/
theorem matrixEntrywisePositive_pow_of_pos [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {n : ℕ} (hn : 0 < n) :
    MatrixEntrywisePositive (M ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  cases m with
  | zero =>
      simpa using hM
  | succ m =>
      have hprev : MatrixEntrywisePositive (M ^ (m + 1)) :=
        matrixEntrywisePositive_pow_of_pos hM (Nat.succ_pos m)
      rw [pow_succ]
      exact matrixEntrywisePositive_mul hprev hM

/-- A positive power of an entrywise positive matrix has positive trace when the
index type is nonempty. -/
theorem trace_pow_pos_of_entrywisePositive [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {n : ℕ} (hn : 0 < n) :
    0 < (M ^ n).trace := by
  rw [Matrix.trace]
  exact Finset.sum_pos
    (fun i _ => matrixEntrywisePositive_pow_of_pos hM hn i i) Finset.univ_nonempty

/-- A strictly positive right eigenpair for a finite real matrix. -/
def StrictPositiveRightEigenpair (M : Matrix Ω Ω ℝ) (lam : ℝ) (v : Ω → ℝ) : Prop :=
  VectorPositive v ∧ M.mulVec v = lam • v

omit [DecidableEq Ω] in
/-- Applying an entrywise positive matrix to a strictly positive vector gives a
strictly positive vector. -/
theorem matrixEntrywisePositive_mulVec_pos [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    {v : Ω → ℝ} (hM : MatrixEntrywisePositive M) (hv : VectorPositive v) :
    VectorPositive (M.mulVec v) := by
  intro i
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos (fun j _ => mul_pos (hM i j) (hv j)) Finset.univ_nonempty

omit [DecidableEq Ω] in
/-- The eigenvalue in a strictly positive right eigenpair of an entrywise
positive matrix is positive. -/
theorem eigenvalue_pos_of_strictPositiveRightEigenpair [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (hM : MatrixEntrywisePositive M)
    {lam : ℝ} {v : Ω → ℝ} (hv : StrictPositiveRightEigenpair M lam v) :
    0 < lam := by
  let i : Ω := Classical.arbitrary Ω
  have hMv : 0 < M.mulVec v i := matrixEntrywisePositive_mulVec_pos hM hv.1 i
  have heq := congr_fun hv.2 i
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  rw [heq] at hMv
  nlinarith [hv.1 i]

/-! ## Matrix conjugation helpers -/

/-- Powers of a matrix conjugate by mutually inverse matrices. -/
theorem matrix_conj_pow {R : Type*} [Semiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    (P * A * Q) ^ n = P * A ^ n * Q := by
  induction n with
  | zero =>
      simp [hPQ]
  | succ n ih =>
      rw [pow_succ, ih]
      calc
        (P * A ^ n * Q) * (P * A * Q) = P * A ^ n * (Q * P) * A * Q := by
          noncomm_ring
        _ = P * A ^ n * 1 * A * Q := by rw [hQP]
        _ = P * (A ^ n * A) * Q := by
          noncomm_ring

/-- Trace is invariant under conjugation by mutually inverse matrices. -/
theorem trace_matrix_conj_pow {R : Type*} [CommSemiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℕ) :
    ((P * A * Q) ^ n).trace = (A ^ n).trace := by
  rw [matrix_conj_pow A P Q hPQ hQP]
  calc
    (P * A ^ n * Q).trace = (Q * (P * A ^ n)).trace := by
      rw [trace_mul_comm]
    _ = ((Q * P) * A ^ n).trace := by
      rw [mul_assoc]
    _ = (A ^ n).trace := by
      rw [hQP, one_mul]

/-- Trace is invariant under conjugation by mutually inverse matrices. -/
theorem trace_matrix_conj {R : Type*} [CommSemiring R] (A P Q : Matrix Ω Ω R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (P * A * Q).trace = A.trace := by
  simpa using trace_matrix_conj_pow A P Q hPQ hQP 1

/-- Diagonal matrices over a commutative semiring commute. -/
theorem diagonal_mul_comm {R : Type*} [CommSemiring R] (d e : Ω → R) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.mul_diagonal, mul_comm]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Matrix.mul_diagonal, hij]

/-- A two-mark trace is invariant under a conjugation that commutes with the
diagonal marking matrix. -/
theorem trace_diagonal_conj_pow_diagonal_conj_pow {R : Type*} [CommSemiring R]
    (A P Q : Matrix Ω Ω R) (f : Ω → R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hFP : Matrix.diagonal f * P = P * Matrix.diagonal f)
    (hQF : Q * Matrix.diagonal f = Matrix.diagonal f * Q)
    (a b : ℕ) :
    (Matrix.diagonal f * (P * A * Q) ^ a
        * Matrix.diagonal f * (P * A * Q) ^ b).trace
      = (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b).trace := by
  rw [matrix_conj_pow A P Q hPQ hQP a, matrix_conj_pow A P Q hPQ hQP b]
  have hmat :
      Matrix.diagonal f * (P * A ^ a * Q) * Matrix.diagonal f * (P * A ^ b * Q)
        = P * (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b) * Q := by
    calc
      Matrix.diagonal f * (P * A ^ a * Q) * Matrix.diagonal f * (P * A ^ b * Q)
          = (Matrix.diagonal f * P) * A ^ a * (Q * Matrix.diagonal f) * P * A ^ b * Q := by
            noncomm_ring
      _ = (P * Matrix.diagonal f) * A ^ a * (Matrix.diagonal f * Q) * P * A ^ b * Q := by
            rw [hFP, hQF]
      _ = P * (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b) * Q := by
            noncomm_ring [hQP]
  rw [hmat]
  exact trace_matrix_conj (Matrix.diagonal f * A ^ a * Matrix.diagonal f * A ^ b)
    P Q hPQ hQP

/-! ## Balanced layer transfer matrix -/

/-- The diagonal scaling matrix `D = diag(sqrt u)` used to balance a positive
finite layer transfer matrix. -/
noncomputable def layerTransferSqrtDiagonal (u : Ω → ℝ) : Matrix Ω Ω ℝ :=
  Matrix.diagonal fun a => Real.sqrt (u a)

/-- The inverse diagonal scaling matrix `D⁻¹ = diag((sqrt u)⁻¹)`. -/
noncomputable def layerTransferSqrtDiagonalInv (u : Ω → ℝ) : Matrix Ω Ω ℝ :=
  Matrix.diagonal fun a => (Real.sqrt (u a))⁻¹

/-- The balanced finite layer transfer matrix
`S a b = sqrt (u a) * k a b * sqrt (u b)`.  If `k` is symmetric, this is a
symmetric real matrix diagonally similar to `layerTransferMatrix u k`. -/
noncomputable def layerSymmetricTransferMatrix
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) : Matrix Ω Ω ℝ :=
  fun a b => Real.sqrt (u a) * k a b * Real.sqrt (u b)

/-- The trace-side partition function computed with the balanced layer transfer
matrix. -/
noncomputable def layerSymmetricTransferPartitionTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  (layerSymmetricTransferMatrix u k ^ n).trace

/-- The two-insertion trace computed with the balanced layer transfer matrix. -/
noncomputable def layerSymmetricTransferCorrelationTrace
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) (a b : ℕ) : ℝ :=
  (Matrix.diagonal f * layerSymmetricTransferMatrix u k ^ a
      * Matrix.diagonal f * layerSymmetricTransferMatrix u k ^ b).trace

/-- The square-root diagonal scaling and its inverse multiply to the identity. -/
theorem layerTransferSqrtDiagonalInv_mul_sqrtDiagonal
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferSqrtDiagonalInv u * layerTransferSqrtDiagonal u = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      inv_mul_cancel₀ (Real.sqrt_pos_of_pos (hu a)).ne']
  · simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      hab]

/-- The square-root diagonal scaling and its inverse multiply to the identity in
the opposite order. -/
theorem layerTransferSqrtDiagonal_mul_sqrtDiagonalInv
    (u : Ω → ℝ) (hu : ∀ a, 0 < u a) :
    layerTransferSqrtDiagonal u * layerTransferSqrtDiagonalInv u = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      mul_inv_cancel₀ (Real.sqrt_pos_of_pos (hu a)).ne']
  · simp [layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
      hab]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced transfer matrix is positive entrywise when the layer and
transition weights are positive. -/
theorem layerSymmetricTransferMatrix_pos
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) (a b : Ω) :
    0 < layerSymmetricTransferMatrix u k a b := by
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr (hu a)) (hk a b))
    (Real.sqrt_pos.mpr (hu b))

omit [Fintype Ω] [DecidableEq Ω] in
/-- The ordinary layer transfer matrix is positive entrywise when the layer and
transition weights are positive. -/
theorem layerTransferMatrix_pos
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (hk : ∀ a b, 0 < k a b) (a b : Ω) :
    0 < layerTransferMatrix u k a b := by
  exact mul_pos (hu b) (hk a b)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The balanced layer transfer matrix is symmetric when the transition weight is
symmetric. -/
theorem layerSymmetricTransferMatrix_transpose
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    (layerSymmetricTransferMatrix u k)ᵀ = layerSymmetricTransferMatrix u k := by
  ext a b
  simp [layerSymmetricTransferMatrix, hk b a]
  ring

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

/-! ## Spectral-gap certificates -/

/-- A finite spectral-gap certificate for a layer transfer matrix.

This is not a Perron--Frobenius theorem.  It packages the data that a later
spectral proof may provide: a positive scale `lambda`, a subdominant ratio
`theta < 1`, a lower bound on the partition trace, and an upper bound on the
marked two-insertion trace. -/
structure LayerSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N
  /-- Exponential upper bound on the marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerTransferCorrelation_matrixElement u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- The denominator in a spectral-gap certificate is positive. -/
theorem layerTransferPartitionTrace_pos_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f) {N : ℕ} (hN : 0 < N) :
    0 < layerTransferPartitionTrace u k N := by
  exact lt_of_lt_of_le (mul_pos h.partitionPrefactor_pos (pow_pos h.scale_pos N))
    (h.partition_lower hN)

/-- A finite spectral-gap certificate gives exponential decay of the normalised
cyclic layer two-point trace ratio in the marked separation `a`. -/
theorem layerTwoPoint_abs_le_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hN : 0 < a + b := Nat.add_pos_left ha b
  have hscaleN : 0 < h.scale ^ (a + b) := pow_pos h.scale_pos (a + b)
  have hθa : 0 ≤ h.theta ^ a := pow_nonneg h.theta_nonneg a
  have hlower_pos : 0 < h.partitionPrefactor * h.scale ^ (a + b) :=
    mul_pos h.partitionPrefactor_pos hscaleN
  have hden_lower := h.partition_lower hN
  have hden_pos : 0 < layerTransferPartitionTrace u k (a + b) :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked := h.marked_abs_le ha hb
  rw [layerTwoPoint_eq_trace_ratio, abs_div, abs_of_pos hden_pos]
  calc
    |layerTransferCorrelation_matrixElement u k f a b| /
        layerTransferPartitionTrace u k (a + b)
        = |layerTransferCorrelation_matrixElement u k f a b|
          * (layerTransferPartitionTrace u k (a + b))⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (h.prefactor * h.scale ^ (a + b) * h.theta ^ a)
          * (h.partitionPrefactor * h.scale ^ (a + b))⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg h.prefactor_nonneg hscaleN.le) hθa)
    _ = (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
            field_simp [(ne_of_gt h.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- Spin-observable wrapper for the spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_spectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (h : LayerSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  exact layerTwoPoint_abs_le_of_spectralGapCertificate h hb

/-! ## Balanced spectral-gap certificates -/

/-- A finite spectral-gap certificate stated on the balanced layer transfer
matrix.

This is the form expected from later symmetric spectral input for
`layerSymmetricTransferMatrix u k`.  The certificate is finite and algebraic:
it records bounds on the balanced partition trace and balanced marked trace,
but does not assert a Perron--Frobenius theorem or construct the bounds. -/
structure LayerBalancedSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the balanced cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N
  /-- Exponential upper bound on the balanced marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerSymmetricTransferCorrelationTrace u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- Transport a balanced trace certificate to the ordinary transfer-matrix
certificate using the diagonal similarity `T = D⁻¹ S D`. -/
def LayerBalancedSpectralGapCertificate.toLayerSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerBalancedSpectralGapCertificate u k f)
    (hu : ∀ a, 0 < u a) :
    LayerSpectralGapCertificate u k f := by
  refine
    { scale := h.scale
      theta := h.theta
      prefactor := h.prefactor
      partitionPrefactor := h.partitionPrefactor
      scale_pos := h.scale_pos
      theta_nonneg := h.theta_nonneg
      theta_lt_one := h.theta_lt_one
      prefactor_nonneg := h.prefactor_nonneg
      partitionPrefactor_pos := h.partitionPrefactor_pos
      partition_lower := ?_
      marked_abs_le := ?_ }
  · intro N hN
    rw [layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace u k hu]
    exact h.partition_lower hN
  · intro a b ha hb
    rw [layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
      u k f hu]
    exact h.marked_abs_le ha hb

/-- Constructor for an ordinary spectral-gap certificate from explicit
transfer-trace bounds. -/
def layerSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerTransferCorrelation_matrixElement u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for a balanced spectral-gap certificate from explicit balanced
trace bounds. -/
def layerBalancedSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerBalancedSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for an ordinary spectral-gap certificate from explicit balanced
trace bounds, transported across the diagonal similarity. -/
def layerSpectralGapCertificate_of_balancedTraceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f :=
  (layerBalancedSpectralGapCertificate_of_traceBounds u k f scale theta prefactor
    partitionPrefactor scale_pos theta_nonneg theta_lt_one prefactor_nonneg
    partitionPrefactor_pos partition_lower marked_abs_le).toLayerSpectralGapCertificate hu

/-- A balanced finite spectral-gap certificate gives exponential decay of the
normalised cyclic layer two-point trace ratio. -/
theorem layerTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerTwoPoint_abs_le_of_spectralGapCertificate
        (h.toLayerSpectralGapCertificate hu) hb)

/-- Spin-observable wrapper for the balanced spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerSpinTwoPoint_abs_le_of_spectralGapCertificate u k x
        (h.toLayerSpectralGapCertificate hu) hb)

end TransferMatrix

end IsingModel
