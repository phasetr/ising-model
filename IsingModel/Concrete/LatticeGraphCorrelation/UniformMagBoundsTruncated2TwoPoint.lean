import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointBounds
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointNonnegAndGe
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagRecasts

/-!
# ℤ^d truncated2TwoPoint bound wrappers

Narrow child module for seven ℤ^d `truncated2TwoPoint` bound wrappers
(`le_one`, `neg_one_le`, `abs_le_one`, `sq_le_one`,
`le_twoPointFunction`, `h_zero_eq`, `J_zero_of_ne_zero`). Each result
is proved via the
`truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq`
identity and direct inequalities on `twoPointFunction` and
`uniformMagnetization`.
-/

namespace IsingModel
namespace Ambient

/-- **`truncated2TwoPoint ≤ 1`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ 1`.

Upper bound: from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261), `twoPointFunction ≤ 1` (PR #260), and `M² ≥ 0`, we get
`truncated2TwoPoint ≤ 1 − 0 = 1`. -/
theorem truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ 1 := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_upper := twoPointFunction_le_one d p r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`-1 ≤ truncated2TwoPoint`** (ferromagnetic): from
`truncated2TwoPoint_nonneg`. -/
theorem neg_one_le_truncated2TwoPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    -1 ≤ truncated2TwoPoint d p r := by
  have := truncated2TwoPoint_nonneg d p hf r
  linarith

/-- **`|truncated2TwoPoint| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    |truncated2TwoPoint d p r| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_truncated2TwoPoint d p hf r,
    truncated2TwoPoint_le_one d p hf r⟩

/-- **`truncated2TwoPoint² ≤ 1`** (ferromagnetic). -/
theorem truncated2TwoPoint_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ^ 2 ≤ 1 := by
  have h := abs_truncated2TwoPoint_le_one d p hf r
  have : |truncated2TwoPoint d p r| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-! ## Moved: relational / trivial-slice wrappers

The three wrappers
`truncated2TwoPoint_le_twoPointFunction`,
`truncated2TwoPoint_h_zero_eq`,
`truncated2TwoPoint_J_zero_of_ne_zero` now live in
`UniformMagBoundsTruncated2TwoPointMisc.lean`. -/



end Ambient
end IsingModel
