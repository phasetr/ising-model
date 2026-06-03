import IsingModel.TransferMatrix.TraceSum
import IsingModel.TransferMatrix.OneDimPower

/-!
# Closed-walk sum for the 1D Ising transfer matrix (GJ §17.1, `Z_N = Tr Tᴺ = λ₊ᴺ + λ₋ᴺ`)

Specialising the general closed-walk trace identity
`IsingModel.TransferMatrix.trace_pow_eq_sum_cycle` to the one-dimensional Ising
transfer matrix `isingTransferMatrix1D a` (`a = β J`) and combining it with the
spectral trace formula `trace_isingTransferMatrix1D_pow` gives the
transfer-matrix partition function of the cyclic `N`-site chain as both a sum
over closed spin walks and a closed form in the eigenvalues:

  `∑_{σ : Fin N → Fin 2} closedWalkWeight T σ = Tr(Tᴺ) = λ₊ᴺ + λ₋ᴺ`,   `N = m + 1`.

The two-element index `Fin 2` is the spin space (`+1`/`-1`); the closed-walk
weight is the cyclic product of Boltzmann edge factors, i.e. the `h = 0` cyclic
Ising partition function `Z_N` (Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

/-- The trace of a power of the 1D Ising transfer matrix as a sum over closed
spin walks: `Tr(T(a)^(m+1)) = ∑_{σ : Fin (m+1) → Fin 2} closedWalkWeight T(a) σ`.
Direct instantiation of `trace_pow_eq_sum_cycle`. -/
theorem trace_isingTransferMatrix1D_pow_eq_sum_cycle (a : ℝ) (m : ℕ) :
    (isingTransferMatrix1D a ^ (m + 1)).trace
      = ∑ σ : Fin (m + 1) → Fin 2, closedWalkWeight (isingTransferMatrix1D a) σ :=
  trace_pow_eq_sum_cycle (isingTransferMatrix1D a) m

/-- **Cyclic 1D Ising partition function as eigenvalue powers** (Glimm–Jaffe §17.1):
the sum over closed spin walks of length `N = m+1` of the cyclic Boltzmann edge
product equals `λ₊ᴺ + λ₋ᴺ`,
`∑_{σ : Fin (m+1) → Fin 2} closedWalkWeight T(a) σ = λ₊^(m+1) + λ₋^(m+1)`.
This is the transfer-matrix evaluation `Z_N = Tr(Tᴺ) = λ₊ᴺ + λ₋ᴺ` of the cyclic
`N`-site zero-field Ising chain, combining the closed-walk identity
`trace_pow_eq_sum_cycle` with the spectral trace `trace_isingTransferMatrix1D_pow`. -/
theorem sum_closedWalkWeight_isingTransferMatrix1D (a : ℝ) (m : ℕ) :
    ∑ σ : Fin (m + 1) → Fin 2, closedWalkWeight (isingTransferMatrix1D a) σ
      = transferEigenvalueTop a ^ (m + 1) + transferEigenvalueBot a ^ (m + 1) := by
  rw [← trace_isingTransferMatrix1D_pow_eq_sum_cycle, trace_isingTransferMatrix1D_pow]

end TransferMatrix

end IsingModel
