import IsingModel.TransferMatrix.CycleGraphLink
import IsingModel.TransferMatrix.TraceSum1D

/-!
# Cyclic 1D Ising partition function `Z_N = λ₊ᴺ + λ₋ᴺ` (GJ §17.1)

This file closes the transfer-matrix evaluation of the cyclic one-dimensional
Ising partition function.  Via the spin↔`Fin 2` encoding (`up ↦ 0`, `down ↦ 1`),
under which `spin1D ∘ encode = Spin.sign` and the Boltzmann edge factor becomes a
transfer-matrix entry, the site-product form of `Z_N`
(`partitionFunction_cycleGraph_eq_sum_prod`) is identified with the closed-walk
sum `∑_σ closedWalkWeight T(βJ) σ`, which equals `λ₊ᴺ + λ₋ᴺ` by
`sum_closedWalkWeight_isingTransferMatrix1D`.  Hence the Gibbs partition function
of the cyclic `N`-site zero-field chain is

  `partitionFunction (cycleGraph N) ⟨J,0,β⟩ = λ₊ᴺ + λ₋ᴺ = (2cosh βJ)ᴺ + (2sinh βJ)ᴺ`,

the classic transfer-matrix result (Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph

/-- The spin↔`Fin 2` encoding `up ↦ 0`, `down ↦ 1`, matching the transfer-matrix
spin labelling `spin1D = ![1, -1]`. -/
def spinEquivFin2 : Spin ≃ Fin 2 where
  toFun s := match s with | .up => 0 | .down => 1
  invFun i := if i = 0 then .up else .down
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The transfer-matrix spin label of an encoded spin is its physical sign:
`spin1D (encode s) = Spin.sign ℝ s`. -/
@[simp] theorem spin1D_spinEquivFin2 (s : Spin) :
    spin1D (spinEquivFin2 s) = Spin.sign ℝ s := by
  cases s <;> simp [spinEquivFin2, spin1D, Spin.sign, Spin.toSign]

/-- The transfer-matrix entry at encoded spins is the Boltzmann edge factor:
`T(βJ) (encode s) (encode t) = exp(β·J·sign s·sign t)`. -/
theorem isingTransferMatrix1D_spinEquivFin2 (β J : ℝ) (s t : Spin) :
    isingTransferMatrix1D (β * J) (spinEquivFin2 s) (spinEquivFin2 t)
      = Real.exp (β * J * (Spin.sign ℝ s * Spin.sign ℝ t)) := by
  rw [isingTransferMatrix1D, Matrix.of_apply, spin1D_spinEquivFin2, spin1D_spinEquivFin2]
  ring_nf

/-- The per-configuration site product equals a closed-walk weight of the encoded
configuration:
`∏_i exp(β·J·edgeSpin σ s(i,i+1)) = closedWalkWeight T(βJ) (encode ∘ σ)`. -/
theorem prod_exp_edgeSpin_eq_closedWalkWeight (β J : ℝ) {n : ℕ}
    (σ : Config (Fin (n + 3))) :
    ∏ i : Fin (n + 3), Real.exp (β * J * edgeSpin (K := ℝ) σ s(i, i + 1))
      = closedWalkWeight (isingTransferMatrix1D (β * J)) (fun i => spinEquivFin2 (σ i)) := by
  rw [closedWalkWeight]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  dsimp only
  rw [isingTransferMatrix1D_spinEquivFin2, edgeSpin, Sym2.lift_mk]

/-- **Cyclic 1D Ising partition function as eigenvalue powers** (Glimm–Jaffe §17.1):
the Gibbs partition function of the cyclic `N = n+3`-site zero-field Ising chain
equals `λ₊ᴺ + λ₋ᴺ`,
`partitionFunction (cycleGraph N) ⟨J,0,β⟩ = λ₊(βJ)ᴺ + λ₋(βJ)ᴺ
  = (2cosh βJ)ᴺ + (2sinh βJ)ᴺ`.  This is the classic transfer-matrix evaluation,
obtained by identifying the site-product form of `Z_N`
(`partitionFunction_cycleGraph_eq_sum_prod`) with the closed-walk sum
(`sum_closedWalkWeight_isingTransferMatrix1D`) through the spin↔`Fin 2` encoding. -/
theorem partitionFunction_cycleGraph_eq_eigenvaluePow (n : ℕ) {J β : ℝ} :
    partitionFunction (cycleGraph (n + 3)) (⟨J, 0, β⟩ : IsingParams ℝ)
      = transferEigenvalueTop (β * J) ^ (n + 3)
        + transferEigenvalueBot (β * J) ^ (n + 3) := by
  rw [partitionFunction_cycleGraph_eq_sum_prod]
  rw [Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin (n + 3))) spinEquivFin2)
    _ (fun τ : Fin (n + 3) → Fin 2 => closedWalkWeight (isingTransferMatrix1D (β * J)) τ)]
  · rw [sum_closedWalkWeight_isingTransferMatrix1D]
  · intro σ
    rw [prod_exp_edgeSpin_eq_closedWalkWeight]
    rfl

end TransferMatrix

end IsingModel
