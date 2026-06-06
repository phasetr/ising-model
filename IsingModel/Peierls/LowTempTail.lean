import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The low-temperature Peierls tail vanishes (FV §3.7.2)

The Peierls contour bound gives `µ⁺(σ₀ = -1) ≤ ∑_{r≥1} C^r e^{-2βJr} = q/(1-q)` with
`q(β) = C·e^{-2βJ}`. As `β → ∞` (with `J > 0`) the rate `q(β) → 0`, so the bound `q/(1-q) → 0`.
This is the analytic input to the low-temperature spontaneous magnetisation `m*(β) > 0`: the
opposite-spin probability is squeezed to `0`.

(The high-temperature counterpart took the `n → ∞` limit; here the limit is `β → ∞`.)

* `lowTempRate_tendsto_zero` — `C·e^{-2βJ} → 0` as `β → ∞`.
* `peierls_low_temp_tail_tendsto_zero` — `q/(1-q) → 0` as `β → ∞`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Filter Topology

/-- **The Peierls rate vanishes at low temperature**: `C·e^{-2βJ} → 0` as `β → ∞` for `J > 0`. -/
theorem lowTempRate_tendsto_zero (C J : ℝ) (hJ : 0 < J) :
    Tendsto (fun β : ℝ => C * Real.exp (-(2 * β * J))) atTop (𝓝 0) := by
  have hg : Tendsto (fun β : ℝ => 2 * β * J) atTop atTop := by
    have h2 : Tendsto (fun β : ℝ => 2 * β) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    exact h2.atTop_mul_const hJ
  have hbot : Tendsto (fun β : ℝ => -(2 * β * J)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hg
  have hexp : Tendsto (fun β : ℝ => Real.exp (-(2 * β * J))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  simpa using hexp.const_mul C

/-- **The low-temperature Peierls tail vanishes**: the geometric bound `q/(1-q)` with
`q = C·e^{-2βJ}` tends to `0` as `β → ∞`, so the opposite-spin probability is squeezed to `0`. -/
theorem peierls_low_temp_tail_tendsto_zero (C J : ℝ) (hJ : 0 < J) :
    Tendsto (fun β : ℝ => C * Real.exp (-(2 * β * J)) *
      (1 - C * Real.exp (-(2 * β * J)))⁻¹) atTop (𝓝 0) := by
  have hq := lowTempRate_tendsto_zero C J hJ
  have hden : Tendsto (fun β : ℝ => 1 - C * Real.exp (-(2 * β * J))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  have hinv : Tendsto (fun β : ℝ => (1 - C * Real.exp (-(2 * β * J)))⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ (one_ne_zero)
  simpa using hq.mul hinv

end IsingModel
