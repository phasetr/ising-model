import IsingModel.TransferMatrix.CycleGraphZ
import IsingModel.TransferMatrix.OneDimFreeEnergy

/-!
# Gibbs free-energy density of the cyclic 1D Ising chain (GJ §17.1)

Combining the transfer-matrix evaluation of the Gibbs partition function
`partitionFunction (cycleGraph N) ⟨J,0,β⟩ = λ₊ᴺ + λ₋ᴺ`
(`partitionFunction_cycleGraph_eq_eigenvaluePow`, #3519) with the eigenvalue
free-energy limit `(1/N)·log(λ₊ᴺ + λ₋ᴺ) → log λ₊` (#3514) gives the per-site
free-energy density of the cyclic chain directly for the project's **Gibbs**
partition function:

  `(1/N)·log partitionFunction (cycleGraph N) ⟨J,0,β⟩ → log(2cosh βJ)`   as `N → ∞`.

This is the Gibbs (not merely transfer-matrix-trace) form of the 1D Ising
free-energy density `f = -β⁻¹ log(2cosh βJ)` (Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology SimpleGraph

/-- **Gibbs free-energy density of the cyclic 1D Ising chain** (Glimm–Jaffe §17.1):
`(1/N)·log partitionFunction (cycleGraph N) ⟨J,0,β⟩ → log(2cosh βJ)` as `N → ∞`
(over `N = n+3`).  Obtained by rewriting the Gibbs partition function as
`λ₊ᴺ + λ₋ᴺ` (`partitionFunction_cycleGraph_eq_eigenvaluePow`) and composing the
eigenvalue free-energy limit `tendsto_log_eigenvalueSum_div_nat` with `n ↦ n+3`. -/
theorem tendsto_log_partitionFunction_cycleGraph_div_nat {J β : ℝ} (hβJ : 0 < β * J) :
    Tendsto (fun n : ℕ =>
        Real.log (partitionFunction (cycleGraph (n + 3)) (⟨J, 0, β⟩ : IsingParams ℝ))
          / (n + 3))
      atTop (𝓝 (Real.log (2 * Real.cosh (β * J)))) := by
  have hcomp := (tendsto_log_eigenvalueSum_div_nat hβJ).comp (tendsto_add_atTop_nat 3)
  rw [← log_transferEigenvalueTop_eq]
  refine hcomp.congr (fun n => ?_)
  rw [Function.comp_apply, partitionFunction_cycleGraph_eq_eigenvaluePow]
  push_cast
  ring_nf

/-- **Physical Gibbs free-energy density of the cyclic 1D Ising chain**
(Glimm–Jaffe §17.1): for `β > 0`, the per-site Helmholtz free energy
`f_N = -(βN)⁻¹·log Z_N` converges to `f = -β⁻¹·log(2cosh βJ)` as `N → ∞`.  This is
`-(1/β)` times the log-partition density limit (an algebraic scaling, valid for
any `β`). -/
theorem tendsto_gibbs_freeEnergy_density {J β : ℝ} (hβJ : 0 < β * J) :
    Tendsto (fun n : ℕ =>
        -(1 / β)
          * (Real.log (partitionFunction (cycleGraph (n + 3)) (⟨J, 0, β⟩ : IsingParams ℝ))
              / (n + 3)))
      atTop (𝓝 (-(1 / β) * Real.log (2 * Real.cosh (β * J)))) :=
  (tendsto_log_partitionFunction_cycleGraph_div_nat hβJ).const_mul _

end TransferMatrix

end IsingModel
