import IsingModel.TransferMatrix.TraceSum

/-!
# Marked-insertion trace identity for two-point functions (GJ §17.1)

The transfer-matrix two-point function `⟨σ₀σₙ⟩ = Tr(S·Tⁿ·S·T^{N-n})/Tr(Tᴺ)` requires
the **marked closed-walk trace identity**: for a diagonal matrix `D = diagonal d`,

  `Tr(D·Mᵃ·D·Mᵇ) = ∑_{τ : Fin (a+b) → ι} d(τ 0)·d(τ a)·closedWalkWeight M τ`,

a sum over closed walks of length `a+b` carrying the diagonal marks `d` at the two
insertion sites `0` and `a`.  It is proved from the open-path entry formula
`pow_apply_eq_sum`: the trace expands to `∑_{i,j} dᵢ·dⱼ·(Mᵃ)ᵢⱼ·(Mᵇ)ⱼᵢ`, the two
open paths `i → j` (length `a`) and `j → i` (length `b`) glue (`markedGlue`,
`Fin.append`) into a single closed walk, and the resulting product factors back via
`Fin.prod_univ_add`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- **Trace expansion with two diagonal insertions**:
`Tr(D·Mᵃ·D·Mᵇ) = ∑_{i,j} dᵢ·dⱼ·(Mᵃ)ᵢⱼ·(Mᵇ)ⱼᵢ`, where `D = diagonal d`. -/
theorem trace_diagonal_pow_diagonal_pow_expand (M : Matrix ι ι R) (d : ι → R) (a b : ℕ) :
    (Matrix.diagonal d * M ^ a * Matrix.diagonal d * M ^ b).trace
      = ∑ i, ∑ j, d i * d j * (M ^ a) i j * (M ^ b) j i := by
  rw [Matrix.mul_assoc (Matrix.diagonal d * M ^ a) (Matrix.diagonal d) (M ^ b),
    Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul]
  ring

/-- **Single diagonal insertion**: `Tr(D·Mᵃ) = ∑_i dᵢ·(Mᵃ)ᵢᵢ`. -/
theorem trace_diagonal_mul_pow (M : Matrix ι ι R) (d : ι → R) (a : ℕ) :
    (Matrix.diagonal d * M ^ a).trace = ∑ i, d i * (M ^ a) i i := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-- **Cyclic symmetry of the two-insertion trace**: `Tr(D·Mᵃ·D·Mᵇ) = Tr(D·Mᵇ·D·Mᵃ)`,
reflecting the cyclic invariance of the trace and the symmetric placement of the
two diagonal insertions. -/
theorem trace_diagonal_pow_diagonal_pow_comm (M : Matrix ι ι R) (d : ι → R) (a b : ℕ) :
    (Matrix.diagonal d * M ^ a * Matrix.diagonal d * M ^ b).trace
      = (Matrix.diagonal d * M ^ b * Matrix.diagonal d * M ^ a).trace := by
  rw [trace_diagonal_pow_diagonal_pow_expand, trace_diagonal_pow_diagonal_pow_expand,
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

end TransferMatrix

end IsingModel
