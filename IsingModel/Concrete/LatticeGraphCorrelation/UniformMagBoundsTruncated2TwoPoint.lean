import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTrivialSlice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointBounds
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointNonnegAndGe
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagRecasts
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFunctionTrivialSlices

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

/-- **`truncated2TwoPoint ≤ twoPointFunction`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ twoPointFunction d p r`.

Immediate from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261) + `M² ≥ 0`: subtracting a nonneg quantity only decreases.
Physical content: the truncated 2-point function never exceeds the
connected 2-point function. -/
theorem truncated2TwoPoint_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ twoPointFunction d p r := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`truncated2TwoPoint` at `h = 0` equals `twoPointFunction`** (ferromagnetic):
`truncated2TwoPoint d ⟨J, 0, β⟩ r = twoPointFunction d ⟨J, 0, β⟩ r`.

At zero external field `h = 0`, Z₂ symmetry forces `M = 0`
(`uniformMagnetization_zero_at_h_zero`), so
`truncated2TwoPoint = twoPointFunction − M² = twoPointFunction`. -/
theorem truncated2TwoPoint_h_zero_eq
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) r
      = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      uniformMagnetization_zero_at_h_zero d J β]
  ring

/-- **`truncated2TwoPoint` at `J = 0` vanishes for `r ≠ 0`** (ferromagnetic):
`truncated2TwoPoint d ⟨0, h, β⟩ r = 0`.

At `J = 0` the Ising Hamiltonian has no coupling, so distinct sites are
independent. Consequently `⟨σ_0 σ_r⟩ = ⟨σ_0⟩⟨σ_r⟩ = M²`, and the
truncated 2-point function vanishes. Computation:
`truncated2TwoPoint = twoPointFunction − M² = tanh(βh)² − tanh(βh)² = 0`.
-/
theorem truncated2TwoPoint_J_zero_of_ne_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    truncated2TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r = 0 := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      twoPointFunction_J_zero_of_ne_zero d h β hf hr,
      uniformMagnetization_J_zero d h β hf]
  ring


end Ambient
end IsingModel
