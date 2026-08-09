import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed

/-!
# ℤ^d linear bounds on the two-point function including the zero endpoint

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the bound of the infinite-volume
correlation by an explicit constant times the varying parameter on the closed interval
`[0, b]`, so that the endpoint zero is included, where the inequality degenerates to `0 ≤ 0`.
The statement is given in the inverse-temperature direction, under `0 ≤ J`, and in the
coupling direction, under `0 < β`; each also assumes `0 < b`, that `b` times the parameter
held fixed times `2 * d` is below one, and that the varying parameter is non-negative and at
most `b`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Linear bound on corr_∞ at β = 0** (Step 181, β ≥ 0 version):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, β) ≤ (J·M(b)² + J·4d) · β`,
where `M(b) = bJ·2d/(1 - bJ·2d)`. Extension of Step 176 to include β = 0
(where both sides are 0).

In particular, `corr_∞(r, s, β) → 0` as `β → 0⁺` (right-continuity at 0). -/
theorem correlationInfinite_le_const_mul_beta_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β : ℝ) (hβ_nn : 0 ≤ β) (hβb : β ≤ b) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro M
  rcases eq_or_lt_of_le hβ_nn with hβ0 | hβ_pos
  · -- β = 0: both sides are 0
    rw [← hβ0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
  · -- β > 0: direct from Step 176
    exact correlationInfinite_le_const_mul_beta_of_high_temp
      Λ r_val s_val hrs J hJ b hb_pos hlt β hβ_pos hβb

/-- **Linear bound on corr_∞ at J = 0** (Step 235, J ≥ 0 version):
For `0 < β`, `0 < b`, `bβ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, J) ≤ (β·M(b)² + β·4d) · J`,
where `M(b) = bβ·2d/(1 - bβ·2d)`. Direct J-direction analogue of Step 181:
extends Step 230 to include J = 0 (where both sides are 0). -/
theorem correlationInfinite_le_const_mul_J_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J : ℝ) (hJ_nn : 0 ≤ J) (hJb : J ≤ b) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro M
  rcases eq_or_lt_of_le hJ_nn with hJ0 | hJ_pos
  · rw [← hJ0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
  · exact correlationInfinite_le_const_mul_J_of_high_temp
      Λ r_val s_val hrs β hβ b hb_pos hlt J hJ_pos hJb

end Ambient
end IsingModel
