import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag

/-!
# Concrete uniformMagnetization trivial-slice + monotonicity wrappers

Narrow child module for seven ℤ^d `uniformMagnetization_*` wrappers at
trivial parameter slices and monotonicity directions. Each wrapper is a
thin pass-through to the corresponding ambient `magnetizationInfinite_*`
lemma at `IsingModel.latticeGraph d` and `Ambient.cubicExhaustion d`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **`uniformMagnetization` at `β = 0`**:
`uniformMagnetization d ⟨J, h, 0⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_beta_zero` at site `0`:
at infinite temperature (`β = 0`) all spin correlations vanish, in
particular the magnetization. No ferromagnetic hypothesis needed. -/
theorem uniformMagnetization_beta_zero
    (d : ℕ) (J h : ℝ) :
    uniformMagnetization d (⟨J, h, 0⟩ : IsingParams ℝ) = 0 :=
  magnetizationInfinite_beta_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h 0

/-! ## Moved: uniformMagnetization monotone wrappers

The three wrappers
`uniformMagnetization_monotone_J`,
`uniformMagnetization_monotone_h`,
`uniformMagnetization_monotone_beta` now live in
`SiteIndepMagTrivialSliceMonotone.lean`. -/


/-- **`uniformMagnetization` at `J = 0`**:
`uniformMagnetization d ⟨0, h, β⟩ = tanh(β · h)` (ferromagnetic).

Concrete specialisation of `magnetizationInfinite_J_zero` at site `0`
on the `(latticeGraph d, cubicExhaustion d)` pair. Non-interacting
slice: at `J = 0` the Ising Hamiltonian has no coupling, so each site
is an independent two-state system with Boltzmann weight `exp(β h s)`,
giving `M = tanh(β h)`. -/
theorem uniformMagnetization_J_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    uniformMagnetization d (⟨0, h, β⟩ : IsingParams ℝ) = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf 0

/-- **`uniformMagnetization` at `J = h = 0`**:
`uniformMagnetization d ⟨0, 0, β⟩ = 0`.

At `J = h = 0` the Hamiltonian vanishes identically, so all site-level
correlations are zero. Direct from `correlationInfinite_zero_params_vanish`
at the singleton `{0}`. -/
theorem uniformMagnetization_zero_params
    (d : ℕ) (β : ℝ) :
    uniformMagnetization d (⟨0, 0, β⟩ : IsingParams ℝ) = 0 := by
  unfold uniformMagnetization magnetizationInfinite
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ)} (by simp)

/-- **Z₂ symmetry at `h = 0`**: `uniformMagnetization d ⟨J, 0, β⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_zero_at_h_zero` at
site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. At `h = 0`
the finite-volume Ising model is Z₂-symmetric (flip `σ ↦ −σ`), so
the magnetization vanishes stage-by-stage, hence at ∞-vol. -/
theorem uniformMagnetization_zero_at_h_zero
    (d : ℕ) (J β : ℝ) :
    uniformMagnetization d ⟨J, 0, β⟩ = 0 :=
  magnetizationInfinite_zero_at_h_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β 0

end Ambient
end IsingModel
