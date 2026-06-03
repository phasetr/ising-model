import IsingModel.TransferMatrix.CycleGraphZ
import IsingModel.TransferMatrix.MarkedTrace1D

/-!
# Gibbs two-point function of the cyclic 1D Ising chain (GJ §17.1)

The numerator of the Gibbs two-point function on the cyclic chain,
`∑_σ σ₀·σ_n·exp(-βH)`, is identified with a closed-walk sum carrying the spin
marks at the two insertion sites, by the same spin↔`Fin 2` encoding used for the
partition function (`twoPointNumerator_cycleGraph_eq_sum_siteMarked`, the marked
analogue of `partitionFunction_cycleGraph_eq_eigenvaluePow`, #3519).  Evaluating
the marked sum by the marked closed-walk trace identity
(`sum_siteMarkedClosedWalkWeight_isingTransferMatrix1D`) and dividing by the
partition function identifies the project's **Gibbs** `correlation` of the two
endpoint spins with the transfer-matrix two-point ratio:

  `correlation (cycleGraph N) ⟨J,0,β⟩ {0,n} = twoPointCorrelation (βJ) n N`
  (`correlation_cycleGraph_eq_twoPointCorrelation`).

This is the bridge that turns the abstract transfer-matrix two-point analysis
(`twoPointCorrelation_eq`, `tendsto_twoPointCorrelation`) into a statement about
the project's Gibbs correlation `⟨σ₀σₙ⟩` (Glimm–Jaffe §17.1).

This is the standard cyclic transfer-matrix computation of the 1D Ising two-point
function, providing the Gibbs reading of the mass and exponential-decay discussion
of Glimm–Jaffe §17.1.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph

/-- **Gibbs two-point numerator as a site-marked closed-walk sum** (Glimm–Jaffe §17.1):
`∑_σ spinProduct {0,n} σ · boltzmannWeight (cycleGraph N) ⟨J,0,β⟩ σ
  = ∑_{τ : Fin N → Fin 2} spin1D(τ 0)·spin1D(τ n)·closedWalkWeight T(βJ) τ` (`N = k+3`).
The spin insertions `σ₀·σ_n` become the marks `spin1D(τ 0)·spin1D(τ n)` under the
encoding, and the Boltzmann edge product becomes the closed-walk weight. -/
theorem twoPointNumerator_cycleGraph_eq_sum_siteMarked (k n : ℕ) (hn : n < k + 3)
    (hn0 : 0 < n) {J β : ℝ} :
    ∑ σ : Config (Fin (k + 3)),
        spinProduct {0, ⟨n, hn⟩} σ
          * boltzmannWeight (cycleGraph (k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ) σ
      = ∑ τ : Fin (k + 3) → Fin 2,
          spin1D (τ 0) * spin1D (τ ⟨n, hn⟩)
            * closedWalkWeight (isingTransferMatrix1D (β * J)) τ := by
  have h0n : (0 : Fin (k + 3)) ≠ ⟨n, hn⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; omega
  rw [Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin (k + 3))) spinEquivFin2)
    _ (fun τ : Fin (k + 3) → Fin 2 =>
        spin1D (τ 0) * spin1D (τ ⟨n, hn⟩)
          * closedWalkWeight (isingTransferMatrix1D (β * J)) τ)]
  intro σ
  rw [boltzmannWeight_eq_prod_exp_of_h_zero, prod_cycleGraph_edgeFinset,
    prod_exp_edgeSpin_eq_closedWalkWeight, spinProduct, Finset.prod_pair h0n]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def,
    id_eq, spin1D_spinEquivFin2, Spin.sign]
  rfl

/-- **Eigenvalue form of the site-marked closed-walk sum** (Glimm–Jaffe §17.1):
for `N = n + m` with `0 < n`, `0 < m`,
`∑_{τ : Fin N → Fin 2} spin1D(τ 0)·spin1D(τ n)·closedWalkWeight T(a) τ
  = λ₋ⁿ·λ₊ᵐ + λ₊ⁿ·λ₋ᵐ`.
This is the closed-walk form of the two-point numerator `Tr(S·Tⁿ·S·Tᵐ)`; it is
`sum_markedClosedWalkWeight_isingTransferMatrix1D` with the marked weight unfolded
to its insertion-site product form (the two mark sites `0`, `⟨n,_⟩` coincide by
proof irrelevance). -/
theorem sum_siteMarkedClosedWalkWeight_isingTransferMatrix1D (a : ℝ) {N n m : ℕ}
    [NeZero N] (hnm : N = n + m) (hn0 : 0 < n) (hm0 : 0 < m) (hn : n < N) :
    ∑ τ : Fin N → Fin 2,
        spin1D (τ 0) * spin1D (τ ⟨n, hn⟩) * closedWalkWeight (isingTransferMatrix1D a) τ
      = transferEigenvalueBot a ^ n * transferEigenvalueTop a ^ m
        + transferEigenvalueTop a ^ n * transferEigenvalueBot a ^ m := by
  subst hnm
  haveI : NeZero n := ⟨hn0.ne'⟩
  rw [← sum_markedClosedWalkWeight_isingTransferMatrix1D a hm0]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [markedClosedWalkWeight]

/-- **Gibbs two-point function of the cyclic 1D Ising chain as the transfer-matrix
ratio** (Glimm–Jaffe §17.1): for `0 < n < N` (`N = k+3`),
`correlation (cycleGraph N) ⟨J,0,β⟩ {0,n} = twoPointCorrelation (βJ) n N`.
The numerator `∑_σ σ₀σ_n·exp(-βH)` is the site-marked closed-walk sum, evaluated to
`λ₋ⁿλ₊^{N-n} + λ₊ⁿλ₋^{N-n}`, and the partition function is `λ₊ᴺ + λ₋ᴺ`, matching the
transfer-matrix ratio `twoPointCorrelation_eq`. This identifies the project's Gibbs
correlation of the two endpoint spins with the transfer-matrix two-point function. -/
theorem correlation_cycleGraph_eq_twoPointCorrelation (k n : ℕ) (hn : n < k + 3)
    (hn0 : 0 < n) {J β : ℝ} :
    correlation (cycleGraph (k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ) {0, ⟨n, hn⟩}
      = twoPointCorrelation (β * J) n (k + 3) := by
  rw [correlation, gibbsExpectation,
    twoPointNumerator_cycleGraph_eq_sum_siteMarked k n hn hn0,
    sum_siteMarkedClosedWalkWeight_isingTransferMatrix1D (β * J) (N := k + 3)
      (n := n) (m := k + 3 - n) (hnm := by omega) (hn0 := hn0) (hm0 := by omega)
      (hn := hn),
    twoPointCorrelation_eq, partitionFunction_cycleGraph_eq_eigenvaluePow,
    div_eq_inv_mul]

end TransferMatrix

end IsingModel
