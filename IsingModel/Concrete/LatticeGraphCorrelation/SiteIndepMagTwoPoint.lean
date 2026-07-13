import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointZeroCollapse
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# ℤ^d two-point function bounds + symmetry wrappers

Narrow child module for 17 ℤ^d two-point / `truncated2TwoPoint` /
`truncated3TwoPoint` / `truncated4TwoPoint` bounds, trivial slices,
monotonicity, and symmetry wrappers. Theorem names are unchanged
from the former `SiteIndepMag` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Basic bounds on the ℤ^d two-point functions -/

/-! ## Moved: twoPointFunction basic bound wrappers

The three wrappers
`twoPointFunction_nonneg`,
`twoPointFunction_le_one`,
`neg_one_le_twoPointFunction` now live in
`SiteIndepMagTwoPointBounds.lean`. -/


/-- **ℤ^d `twoPointFunction ≥ tanh(β·h)²` for `r ≠ 0`** (ferromagnetic):
specialization of `correlationInfinite_ge_tanh_pow_card` at `A = {0, r}`
where `A.card = 2` (since `r ≠ 0`). -/
theorem twoPointFunction_ge_tanh_sq_of_ne
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * h) ^ 2 ≤ twoPointFunction d (⟨J, h, β⟩ : IsingParams ℝ) r := by
  have hcard : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair (Ne.symm hr)]
  have := correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ ({(0 : Fin d → ℤ), r} : Finset _)
  rw [hcard] at this
  exact this

/-- **`|twoPointFunction| ≤ 1`** unconditionally. Direct specialization
of `abs_correlationInfinite_le_one` at `A = {0, r}`. -/
theorem abs_twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    |twoPointFunction d p r| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction² ≤ 1`** unconditionally. Direct specialization
of `correlationInfinite_sq_le_one` at `A = {0, r}`. -/
theorem twoPointFunction_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction` at `h = 0, r = 0` vanishes** (Z₂ via
`twoPointFunction_zero` + `magnetizationInfinite_zero_at_h_zero`):
`twoPointFunction d ⟨J, 0, β⟩ 0 = 0`. -/
theorem twoPointFunction_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [twoPointFunction_zero,
      magnetizationInfinite_zero_at_h_zero]

/-- **`truncated2TwoPoint` at `h = 0, r = 0` vanishes**: at `r = 0`,
`truncated2TwoPoint = M · (1 − M)`; at `h = 0`, `M = 0` by Z₂, so the
product is `0`. -/
theorem truncated2TwoPoint_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [truncated2TwoPoint_zero,
      magnetizationInfinite_zero_at_h_zero]
  ring

/-! ## Moved: twoPointFunction monotone wrappers

The three wrappers `twoPointFunction_monotone_{J,h,beta}` now live in
`SiteIndepMagTwoPointMonotone.lean`. -/

/-! ## Moved: truncated2/3 TwoPoint nonneg / ge mag² / symm wrappers

The three wrappers `truncated2TwoPoint_nonneg`,
`twoPointFunction_ge_magnetization_sq`, `truncated3TwoPoint_symm_rs`
now live in `SiteIndepMagTwoPointNonnegAndGe.lean`. -/



/-! ## Moved: truncated4TwoPoint symmetry wrappers

The three wrappers `truncated4TwoPoint_symm_{rs,su,ru}` now live in
`SiteIndepMagTwoPointTruncated4Symm.lean`. -/

end Ambient

end IsingModel
