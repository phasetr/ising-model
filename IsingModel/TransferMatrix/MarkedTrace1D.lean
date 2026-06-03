import IsingModel.TransferMatrix.MarkedTraceClosedWalk
import IsingModel.TransferMatrix.OneDimTwoPoint

/-!
# Marked closed-walk sum for the 1D Ising transfer matrix (GJ §17.1)

Specialising the marked closed-walk trace identity
`IsingModel.TransferMatrix.trace_diagonal_pow_diagonal_pow_eq_sum_markedClosedWalk`
to the one-dimensional Ising transfer matrix `T = isingTransferMatrix1D a`
(`a = β J`) with diagonal marks `spin1D = ![1, -1]` (so the marking matrix is the
spin operator `S = diagonal spin1D`) and combining with the two-point trace
`twoPointTrace` gives the eigenvalue form of the marked closed-walk sum:

  `∑_{τ : Fin (n+m) → Fin 2} spin1D(τ 0)·spin1D(τ n)·closedWalkWeight T τ
     = λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`.

This is the closed-walk form of the transfer-matrix two-point numerator
`Tr(S·Tⁿ·S·Tᵐ)`, the bridge toward the Gibbs two-point function (Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-- The spin operator is the diagonal matrix of the spin labels:
`spinOperator = Matrix.diagonal spin1D`. -/
theorem spinOperator_eq_diagonal_spin1D : spinOperator = Matrix.diagonal spin1D := rfl

/-- **Marked closed-walk sum for the 1D Ising transfer matrix as eigenvalue powers**
(Glimm–Jaffe §17.1): the closed-walk form of the two-point numerator
`Tr(S·Tⁿ·S·Tᵐ)` equals `λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`,
`∑_{τ : Fin (n+m) → Fin 2} markedClosedWalkWeight T(a) spin1D τ = λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`.
Combines the marked closed-walk trace identity with `twoPointTrace`. -/
theorem sum_markedClosedWalkWeight_isingTransferMatrix1D (a : ℝ) {n m : ℕ}
    [NeZero n] [NeZero (n + m)] (hm : 0 < m) :
    ∑ τ : Fin (n + m) → Fin 2,
        markedClosedWalkWeight (isingTransferMatrix1D a) spin1D hm τ
      = transferEigenvalueBot a ^ n * transferEigenvalueTop a ^ m
        + transferEigenvalueTop a ^ n * transferEigenvalueBot a ^ m := by
  rw [← trace_diagonal_pow_diagonal_pow_eq_sum_markedClosedWalk (isingTransferMatrix1D a) spin1D hm,
    ← spinOperator_eq_diagonal_spin1D, twoPointTrace]

end TransferMatrix

end IsingModel
