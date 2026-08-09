import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# The ℤ^d two-point function at degenerate parameter records

Concrete statements about `twoPointFunction` at `IsingModel.latticeGraph d` along
`Ambient.cubicExhaustion d`, at parameter records that switch part of the interaction off.

With the coupling and the external field both zero, and separately at zero inverse
temperature, the value is `0` at every separation and under no hypothesis: the
infinite-volume correlation of a nonempty site set vanishes at those records, and the
anchoring literal `{0, r}` is nonempty whatever the separation is.

With only the coupling zero the external field survives, and there the infinite-volume
correlation of a site set is `Real.tanh (β * h)` raised to that set's cardinality. The
anchoring set has cardinality `2` exactly when the separation is nonzero, so the two-point
function is `Real.tanh (β * h)` squared. That statement assumes `Ferromagnetic` on the
record `⟨0, h, β⟩` and, unlike the degenerate slices above, a nonzero separation.
No instance argument is taken anywhere in this module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **`twoPointFunction` at `J = h = 0` is 0**:
`twoPointFunction d ⟨0, 0, β⟩ r = 0`.

Both couplings vanish ⇒ the Hamiltonian is identically zero
⇒ all configurations are equiprobable ⇒ all nonempty-observable
correlations vanish. Direct from `correlationInfinite_zero_params_vanish`. -/
theorem twoPointFunction_zero_params
    (d : ℕ) (β : ℝ) (r : Fin d → ℤ) :
    twoPointFunction d (⟨0, 0, β⟩ : IsingParams ℝ) r = 0 := by
  unfold twoPointFunction
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ), r} (by simp)

/-- **`twoPointFunction` at `β = 0`**: `twoPointFunction d ⟨J, h, 0⟩ r = 0`.

At infinite temperature `β = 0`, all correlation functions vanish
(Boltzmann weight is `exp 0 = 1`, and the summand is the spin product
which sums to zero over all configurations). Concrete specialisation
of `correlationInfinite_beta_zero_vanish` at `A = {0, r}` (nonempty). -/
theorem twoPointFunction_beta_zero
    (d : ℕ) (J h : ℝ) (r : Fin d → ℤ) :
    twoPointFunction d (⟨J, h, 0⟩ : IsingParams ℝ) r = 0 := by
  unfold twoPointFunction
  exact correlationInfinite_beta_zero_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h
    {(0 : Fin d → ℤ), r} (by simp)

/-- **`twoPointFunction` at `J = 0`** (ferromagnetic `⟨0, h, β⟩`), for
distinct sites: `twoPointFunction d ⟨0, h, β⟩ r = tanh(β · h)^2`
for `r ≠ 0`.

Proof: `correlationInfinite_J_zero` gives
`correlationInfinite ... ⟨0, h, β⟩ A = tanh(β h)^|A|`; with `A = {0, r}`
and `r ≠ 0`, `|A| = 2`, giving `tanh(β h)^2`. -/
theorem twoPointFunction_J_zero_of_ne_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    twoPointFunction d (⟨0, h, β⟩ : IsingParams ℝ) r
      = Real.tanh (β * h) ^ 2 := by
  unfold twoPointFunction
  -- `correlationInfinite ... ⟨0, h, β⟩ {0, r} = tanh(β h)^|{0, r}| = tanh(β h)^2`.
  rw [correlationInfinite_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hf {(0 : Fin d → ℤ), r}]
  -- `|{0, r}| = 2` since `0 ≠ r`.
  have h_card : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair]
    exact (Ne.symm hr)
  rw [h_card]

end Ambient

end IsingModel
