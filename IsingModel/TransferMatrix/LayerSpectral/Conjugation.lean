import IsingModel.TransferMatrix.LayerSpectral.Positivity

/-!
# Matrix conjugation and trace helpers (GJ §17.1)

Conjugation-invariance of matrix powers and of the (marked) trace under
mutually inverse similarity transforms.  Part of the `LayerSpectral` finite
spectral scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

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


end TransferMatrix

end IsingModel
