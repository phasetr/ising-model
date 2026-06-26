import IsingModel.TransferMatrix.OneDimTwoPoint
import IsingModel.RealTanhAux

/-!
# Correlation length and mass of the 1D Ising chain (GJ §17.1, §17.5)

The transfer-matrix two-point ratio of the one-dimensional Ising chain decays as
`twoPointCorrelation a n N → (tanh βJ)ⁿ` (`tendsto_twoPointCorrelation`, #3517; its
identification with the Gibbs `⟨σ₀σₙ⟩` is a separate step).  Writing this as a
pure exponential identifies the **mass** `m = -log tanh βJ` (the inverse
correlation length, the §17.5 mass for the 1D chain) and the **correlation
length** `ξ = 1/m`:

  `(tanh βJ)ⁿ = exp(-m·n)`,   `⟨σ₀σₙ⟩_N → exp(-m·n)`   as `N → ∞`,

with `m > 0` for `a = βJ > 0` (`tanh a ∈ (0,1)`, so `log tanh a < 0`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1, §17.5.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- The **mass** (inverse correlation length) of the 1D Ising chain,
`m = -log tanh a` with `a = β J`.  This is the §17.5 mass governing the
exponential decay of the two-point function. -/
noncomputable def correlationMass (a : ℝ) : ℝ := -Real.log (Real.tanh a)

/-- The **correlation length** of the 1D Ising chain, `ξ = 1/m = -1/log tanh a`. -/
noncomputable def correlationLength (a : ℝ) : ℝ := 1 / correlationMass a

/-- For `a = β J > 0` the mass is strictly positive: `tanh a ∈ (0,1)` gives
`log tanh a < 0`, hence `m = -log tanh a > 0`. -/
theorem correlationMass_pos {a : ℝ} (ha : 0 < a) : 0 < correlationMass a := by
  rw [correlationMass]
  apply neg_pos.mpr
  apply Real.log_neg
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos a)
  · exact Real.tanh_lt_one a

/-- The correlation length is strictly positive for `a = β J > 0`. -/
theorem correlationLength_pos {a : ℝ} (ha : 0 < a) : 0 < correlationLength a :=
  div_pos one_pos (correlationMass_pos ha)

/-- The mass is the reciprocal of the correlation length, `m = 1/ξ`. -/
theorem correlationMass_eq_inv_length (a : ℝ) :
    correlationMass a = 1 / correlationLength a := by
  rw [correlationLength, one_div_one_div]

/-- **Geometric decay as a pure exponential**: `(tanh a)ⁿ = exp(-m·n)` with
`m = correlationMass a`, for `a = β J > 0` (so `tanh a > 0`). -/
theorem tanh_pow_eq_exp_neg_mass {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.tanh a ^ n = Real.exp (-(correlationMass a) * n) := by
  have htanh_pos : 0 < Real.tanh a := real_tanh_pos ha
  rw [correlationMass, neg_neg, mul_comm, ← Real.log_pow,
    Real.exp_log (pow_pos htanh_pos n)]

/-- **Exponential decay of the 1D Ising two-point function at the correlation
length** (Glimm–Jaffe §17.1, §17.5): for `a = β J > 0`, the transfer-matrix
two-point correlation converges to the pure exponential `exp(-m·n)` with mass
`m = correlationMass a = -log tanh βJ`,
`⟨σ₀σₙ⟩_N → exp(-m·n)` as `N → ∞`. -/
theorem tendsto_twoPointCorrelation_exp_neg_mass {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun N => twoPointCorrelation a n N) atTop
      (𝓝 (Real.exp (-(correlationMass a) * n))) := by
  rw [← tanh_pow_eq_exp_neg_mass ha n]
  exact tendsto_twoPointCorrelation a ha n

end TransferMatrix

end IsingModel
