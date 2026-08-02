import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeMagnetization
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationFlipSymmetry
import IsingModel.Inequalities.MonotonicityField
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreening

/-!
# Field monotonicity of the magnetization (FV §3.6, Issue #3599)

For a ferromagnetic Ising model, increasing the external field `h` increases the
magnetization.  This file lifts the field monotonicity of the
**boundary-condition** Gibbs expectation (the `+` boundary case is what the
cubic-exhaustion magnetization is built from) to the infinite-volume
magnetization `m^±(β,·)` by passing to the limit.

* `plusMagnetization_mono_h` / `minusMagnetization_mono_h` — `m^±(β,·)` is
  nondecreasing in the field.

The generic boundary-condition version of field monotonicity
(`boltzmannWeightBC_field_cross_supermodular`,
`gibbsExpectationBC_field_mono_of_nonneg`, `gibbsExpectationBC_field_mono`), which
has no dependence on the lattice `ℤ^d`, has moved to
`Inequalities/MonotonicityField.lean`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6 (magnetization, monotonicity in the field; Holley's
inequality, Theorem 3.50).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **Field monotonicity of the `+` magnetization** `m⁺(β,·)`: for `h ≤ h'`,
`m⁺(β,h) ≤ m⁺(β,h')` (increasing the field increases the magnetization).  Each
finite-volume `+` box magnetization is monotone in `h`
(`gibbsExpectationBC_field_mono` on the monotone single spin), and `m⁺` is their
limit. -/
theorem plusMagnetization_mono_h {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ)
    {h h' : ℝ} (hh : h ≤ h') :
    plusMagnetization x J h β ≤ plusMagnetization x J h' β := by
  refine le_of_tendsto_of_tendsto' (tendsto_plusMagnetization (h := h) hβ hJ x)
    (tendsto_plusMagnetization (h := h') hβ hJ x) (fun k => ?_)
  unfold plusBoxObsExpectation plusBoxExpectation
  exact gibbsExpectationBC_field_mono _ hβ hJ hh _ _ _
    ((singleSpinMonoObs x).mono.comp (restrictConfig_monotone _))

/-- **Field monotonicity of the `−` magnetization** `m⁻(β,·)`: for `h ≤ h'`,
`m⁻(β,h) ≤ m⁻(β,h')` (via the flip symmetry `m⁻(β,h) = −m⁺(β,−h)` and the `+`
monotonicity). -/
theorem minusMagnetization_mono_h {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ)
    {h h' : ℝ} (hh : h ≤ h') :
    minusMagnetization x J h β ≤ minusMagnetization x J h' β := by
  rw [minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ,
    minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ]
  exact neg_le_neg (plusMagnetization_mono_h hβ hJ x (neg_le_neg hh))

end Ambient

end IsingModel
