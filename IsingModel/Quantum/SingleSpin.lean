import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum mechanics of a single spin (Tasaki Ch 2.1, S = 1/2)

This file begins the formalization of Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems* (Graduate Texts in Physics, Springer 2020), starting from
Chapter 2 Section 2.1 (pp. 13-15), specialised to spin S = 1/2.

A spin-S quantum system lives on a `(2S+1)`-dimensional Hilbert space `h₀` and is
described by three self-adjoint spin operators `S^(1)`, `S^(2)`, `S^(3)` (denoted
`spinOp1Half_x`, `spinOp1Half_y`, `spinOp1Half_z` here) satisfying

    [S^(α), S^(β)] = i · ∑_γ ε_{αβγ} S^(γ)         (Tasaki 2.1.1)

and `S² = S(S+1) · I` (so `S² = (3/4) I` for `S = 1/2`).

For S = 1/2 the spin operators are `S^(α) = σ^(α)/2` where `σ^(α)` are the Pauli
matrices (Tasaki 2.1.7, 2.1.8):

    σ^(1) = (0 1; 1 0),  σ^(2) = (0 -i; i 0),  σ^(3) = (1 0; 0 -1).

This file defines the Pauli matrices and the spin-1/2 operators as concrete
`Matrix (Fin 2) (Fin 2) ℂ`, and proves the three square identities
`(σ^(α))² = I` for α = 1, 2, 3 (the diagonal `α = β` case of the full
anticommutation relation `{σ^(α), σ^(β)} = 2 δ_{αβ} I`). Off-diagonal
anticommutation and the commutation relations (Tasaki 2.1.1) are deferred
to subsequent PRs.

References:

* H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, GTP,
  Springer 2020, §2.1, pp. 13-15.
-/

namespace IsingModel.Quantum

open Complex Matrix

/-- The Pauli matrix `σ^(1) = ((0, 1), (1, 0))` (Tasaki 2.1.8). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Pauli matrix `σ^(2) = ((0, -i), (i, 0))` (Tasaki 2.1.8). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ^(3) = ((1, 0), (0, -1))` (Tasaki 2.1.8). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The spin-1/2 operator `S^(1) = σ^(1)/2` (Tasaki 2.1.7). -/
noncomputable def spinOp1Half_x : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • pauliX

/-- The spin-1/2 operator `S^(2) = σ^(2)/2` (Tasaki 2.1.7). -/
noncomputable def spinOp1Half_y : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • pauliY

/-- The spin-1/2 operator `S^(3) = σ^(3)/2` (Tasaki 2.1.7). -/
noncomputable def spinOp1Half_z : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • pauliZ

/-- The Pauli matrix `σ^(1)` squared equals the identity (`(σ^(1))² = I`). -/
theorem pauliX_sq : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Pauli matrix `σ^(3)` squared equals the identity (`(σ^(3))² = I`). -/
theorem pauliZ_sq : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `σ^(2) · σ^(2) = I`: the Pauli-Y matrix squared equals the identity. -/
theorem pauliY_sq : pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- Off-diagonal anticommutation `σ^(1) · σ^(2) + σ^(2) · σ^(1) = 0`. -/
theorem pauliX_mul_pauliY_add_pauliY_mul_pauliX :
    pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY]

/-- Off-diagonal anticommutation `σ^(2) · σ^(3) + σ^(3) · σ^(2) = 0`. -/
theorem pauliY_mul_pauliZ_add_pauliZ_mul_pauliY :
    pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, pauliZ]

/-- Off-diagonal anticommutation `σ^(1) · σ^(3) + σ^(3) · σ^(1) = 0`. -/
theorem pauliX_mul_pauliZ_add_pauliZ_mul_pauliX :
    pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ]

/-- The Pauli `XY` product: `σ^(1) · σ^(2) = i · σ^(3)`. -/
theorem pauliX_mul_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Pauli `YZ` product: `σ^(2) · σ^(3) = i · σ^(1)`. -/
theorem pauliY_mul_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Pauli `ZX` product: `σ^(3) · σ^(1) = i · σ^(2)`. -/
theorem pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Pauli commutator `[σ^(1), σ^(2)] = 2i · σ^(3)`.

Derived algebraically from `σ^(1)σ^(2) = i σ^(3)` (`pauliX_mul_pauliY`) and the
off-diagonal anticommutation `σ^(1)σ^(2) + σ^(2)σ^(1) = 0`
(`pauliX_mul_pauliY_add_pauliY_mul_pauliX`). -/
theorem pauliX_commutator_pauliY :
    pauliX * pauliY - pauliY * pauliX = (2 * Complex.I) • pauliZ := by
  have h_anti : pauliY * pauliX = -(pauliX * pauliY) :=
    eq_neg_of_add_eq_zero_right pauliX_mul_pauliY_add_pauliY_mul_pauliX
  rw [h_anti, sub_neg_eq_add, pauliX_mul_pauliY, ← two_smul ℂ (Complex.I • pauliZ),
    smul_smul]

/-- Pauli commutator `[σ^(2), σ^(3)] = 2i · σ^(1)`. -/
theorem pauliY_commutator_pauliZ :
    pauliY * pauliZ - pauliZ * pauliY = (2 * Complex.I) • pauliX := by
  have h_anti : pauliZ * pauliY = -(pauliY * pauliZ) :=
    eq_neg_of_add_eq_zero_right pauliY_mul_pauliZ_add_pauliZ_mul_pauliY
  rw [h_anti, sub_neg_eq_add, pauliY_mul_pauliZ, ← two_smul ℂ (Complex.I • pauliX),
    smul_smul]

/-- Pauli commutator `[σ^(3), σ^(1)] = 2i · σ^(2)`. -/
theorem pauliZ_commutator_pauliX :
    pauliZ * pauliX - pauliX * pauliZ = (2 * Complex.I) • pauliY := by
  have h_anti : pauliX * pauliZ = -(pauliZ * pauliX) := by
    have h := pauliX_mul_pauliZ_add_pauliZ_mul_pauliX
    have : pauliZ * pauliX + pauliX * pauliZ = 0 := by rw [add_comm]; exact h
    exact eq_neg_of_add_eq_zero_right this
  rw [h_anti, sub_neg_eq_add, pauliZ_mul_pauliX, ← two_smul ℂ (Complex.I • pauliY),
    smul_smul]

end IsingModel.Quantum
