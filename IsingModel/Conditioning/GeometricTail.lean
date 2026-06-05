import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Geometric series tail and exponential decay

The tail of a geometric series, `∑_{ℓ≥n} q^ℓ = q^n/(1-q)`, tends to `0` as `n → ∞` and
equals an exponential `e^{-cn}/(1-q)` with `c = -log q > 0`. This is the analytic input to
the FV §3.7.3 estimate `⟨σ₀⟩⁺_{B(n)} ≤ ∑_{ℓ≥n}(4d²·tanh βJ)^ℓ ≤ e^{-cn}` for `β < 1/(4d²)`,
the high-temperature `m*(β)=0` (Issue #3613).

* `tsum_geometric_tail` — `∑'_ℓ q^{n+ℓ} = q^n·(1-q)⁻¹`.
* `tendsto_geometric_tail` — the tail tends to `0` as `n → ∞`.
* `pow_eq_exp_mul_log` — `q^n = exp(n·log q)` (the `e^{-cn}` form).

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Filter Topology

/-- **Geometric series tail**: for `0 ≤ q < 1`, `∑'_ℓ q^{n+ℓ} = q^n·(1-q)⁻¹`. -/
theorem tsum_geometric_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    ∑' ℓ : ℕ, q ^ (n + ℓ) = q ^ n * (1 - q)⁻¹ := by
  simp_rw [pow_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]

/-- **The geometric tail vanishes**: for `0 ≤ q < 1`, `q^n·(1-q)⁻¹ → 0` as `n → ∞`. -/
theorem tendsto_geometric_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun n => q ^ n * (1 - q)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (1 - q)⁻¹
  simpa using h

/-- **Power as an exponential**: for `0 < q`, `q^n = exp(n·log q)`; with `0 < q < 1` the
exponent is `-c·n` for `c = -log q > 0`, the FV `e^{-cn}` decay form. -/
theorem pow_eq_exp_mul_log {q : ℝ} (hq : 0 < q) (n : ℕ) :
    q ^ n = Real.exp (n * Real.log q) := by
  rw [Real.exp_nat_mul, Real.exp_log hq]

end IsingModel
