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

end IsingModel.Quantum
