import IsingModel.TransferMatrix.OneDimCorrelationLength

/-!
# Magnetic susceptibility of the 1D Ising chain (GJ §17.1)

Summing the two-point decay `(tanh βJ)ⁿ` of the one-dimensional Ising chain over
all separations gives the magnetic susceptibility.  With `r = tanh βJ ∈ [0,1)`
the geometric series `∑ₙ rⁿ = (1-r)⁻¹` converges, and the two-sided lattice sum
`χ = ∑_{x ∈ ℤ} ⟨σ₀σ_x⟩ = 1 + 2·∑_{n ≥ 1} rⁿ` gives

  `χ = (1 + tanh βJ) / (1 - tanh βJ)`,

finite for `βJ > 0` (`tanh βJ < 1`) and diverging only in the zero-temperature
limit `βJ → ∞` (`tanh βJ → 1`) — the 1D Ising chain has no finite-temperature
phase transition (Glimm–Jaffe §17.1).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-- For `a = β J > 0` the geometric series of the two-point decay rate is
summable (`tanh a ∈ [0,1)`). -/
theorem summable_tanh_pow {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.tanh a ^ n) := by
  apply summable_geometric_of_lt_one _ (Real.tanh_lt_one a)
  rw [Real.tanh_eq_sinh_div_cosh]
  exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos a))

/-- The geometric sum of the two-point decay rate: `∑ₙ (tanh a)ⁿ = (1 - tanh a)⁻¹`. -/
theorem tsum_tanh_pow {a : ℝ} (ha : 0 < a) :
    ∑' n : ℕ, Real.tanh a ^ n = (1 - Real.tanh a)⁻¹ := by
  apply tsum_geometric_of_lt_one _ (Real.tanh_lt_one a)
  rw [Real.tanh_eq_sinh_div_cosh]
  exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos a))

/-- The **magnetic susceptibility** of the 1D Ising chain,
`χ = (1 + tanh βJ) / (1 - tanh βJ)`, the two-sided lattice sum of the two-point
function `∑_{x ∈ ℤ} ⟨σ₀σ_x⟩` (the field-derivative susceptibility is `β·χ`). -/
noncomputable def isingSusceptibility1D (a : ℝ) : ℝ :=
  (1 + Real.tanh a) / (1 - Real.tanh a)

/-- The susceptibility as twice the one-sided geometric sum minus one:
`χ = 2·∑ₙ (tanh a)ⁿ - 1` (the `n = 0` diagonal term is counted once). -/
theorem isingSusceptibility1D_eq_two_tsum_sub_one {a : ℝ} (ha : 0 < a) :
    isingSusceptibility1D a = 2 * (∑' n : ℕ, Real.tanh a ^ n) - 1 := by
  have h1 : (1 : ℝ) - Real.tanh a ≠ 0 := by
    have := Real.tanh_lt_one a; linarith
  rw [isingSusceptibility1D, tsum_tanh_pow ha]
  field_simp
  ring

/-- The susceptibility is strictly positive for `a = β J > 0`. -/
theorem isingSusceptibility1D_pos {a : ℝ} (ha : 0 < a) : 0 < isingSusceptibility1D a := by
  have htanh_pos : 0 < Real.tanh a := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos a)
  have htanh_lt : Real.tanh a < 1 := Real.tanh_lt_one a
  rw [isingSusceptibility1D]
  apply div_pos <;> linarith

end TransferMatrix

end IsingModel
