import IsingModel.TransferMatrix.OneDimPower
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Free-energy density of the 1D Ising chain from the transfer matrix (GJ §17.1)

Building on the trace formula `Tr(T(a)ᴺ) = λ₊ᴺ + λ₋ᴺ` of
`IsingModel.TransferMatrix.trace_isingTransferMatrix1D_pow`, this file derives the
per-site **log-partition (dimensionless free-energy) density** of the
one-dimensional Ising chain at zero field,

  `lim_{N → ∞} (1/N)·log Tr(T(a)ᴺ) = log λ₊ = log(2·cosh a)`,   `a = β J > 0`.

Since `Z_N = Tr(T(a)ᴺ)` is the partition function of the `N`-site cyclic Ising
chain, this is the transfer-matrix computation of the 1D Ising free-energy
density `f = -β⁻¹·lim_N (1/N)·log Z_N = -β⁻¹ log(2 cosh βJ)` (Glimm–Jaffe §17.1).
The mechanism is the
spectral gap `λ₋ < λ₊`: writing `λ₊ᴺ + λ₋ᴺ = λ₊ᴺ·(1 + (λ₋/λ₊)ᴺ)` with
`λ₋/λ₊ = tanh a ∈ (0,1)`, the subdominant eigenvalue contributes a vanishing
`(1/N)·log(1 + tanhᴺ a) → 0`, leaving the dominant eigenvalue `log λ₊`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- For `a > 0` the subdominant eigenvalue is strictly positive,
`λ₋ = 2·sinh a > 0`. -/
theorem transferEigenvalueBot_pos {a : ℝ} (ha : 0 < a) : 0 < transferEigenvalueBot a := by
  rw [transferEigenvalueBot_eq]
  exact mul_pos two_pos (Real.sinh_pos_iff.mpr ha)

/-- The spectral gap: the subdominant eigenvalue is strictly below the dominant
one, `λ₋ < λ₊` (their difference is `2·e⁻ᵃ > 0`, for every `a`). -/
theorem transferEigenvalueBot_lt_top (a : ℝ) :
    transferEigenvalueBot a < transferEigenvalueTop a := by
  rw [transferEigenvalueBot, transferEigenvalueTop]
  have : 0 < Real.exp (-a) := Real.exp_pos _
  linarith

/-- For `a > 0` the eigenvalue ratio is strictly positive,
`0 < λ₋/λ₊ = tanh a`. -/
theorem transferEigenvalue_ratio_pos {a : ℝ} (ha : 0 < a) :
    0 < transferEigenvalueBot a / transferEigenvalueTop a := by
  rw [transferEigenvalue_ratio, Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos a)

/-- The eigenvalue ratio is strictly below one, `λ₋/λ₊ = tanh a < 1`. -/
theorem transferEigenvalue_ratio_lt_one (a : ℝ) :
    transferEigenvalueBot a / transferEigenvalueTop a < 1 := by
  rw [transferEigenvalue_ratio]
  exact Real.tanh_lt_one a

/-- The powers of the eigenvalue ratio vanish: `(λ₋/λ₊)ᴺ → 0` as `N → ∞`
(for `a > 0`), since `λ₋/λ₊ = tanh a ∈ (0,1)`. -/
theorem tendsto_transferEigenvalue_ratio_pow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (transferEigenvalueBot a / transferEigenvalueTop a) ^ N)
      atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (transferEigenvalue_ratio_pos ha).le
    (transferEigenvalue_ratio_lt_one a)

/-- **Free-energy density from the eigenvalues** (Glimm–Jaffe §17.1): for
`a = β J > 0`,
`(1/N)·log(λ₊ᴺ + λ₋ᴺ) → log λ₊`.  The subdominant eigenvalue `λ₋ < λ₊`
contributes only the vanishing correction `(1/N)·log(1 + (λ₋/λ₊)ᴺ) → 0`. -/
theorem tendsto_log_eigenvalueSum_div_nat {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
        Real.log (transferEigenvalueTop a ^ N + transferEigenvalueBot a ^ N) / N)
      atTop (𝓝 (Real.log (transferEigenvalueTop a))) := by
  set lt := transferEigenvalueTop a with hlt_def
  set lb := transferEigenvalueBot a with hlb_def
  have hlt : 0 < lt := transferEigenvalueTop_pos a
  set r := lb / lt with hr_def
  have hr0 : 0 ≤ r := (transferEigenvalue_ratio_pos ha).le
  have hr1 : r < 1 := transferEigenvalue_ratio_lt_one a
  have hpow : Tendsto (fun N : ℕ => r ^ N) atTop (𝓝 0) :=
    tendsto_transferEigenvalue_ratio_pow ha
  -- `log(1 + rᴺ) → 0`
  have hlog1 : Tendsto (fun N : ℕ => Real.log (1 + r ^ N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 1 + r ^ N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hpow
    have hcomp := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
    simpa [Real.log_one] using hcomp
  -- `log(1 + rᴺ)/N → 0`
  have hdiv : Tendsto (fun N : ℕ => Real.log (1 + r ^ N) / N) atTop (𝓝 0) := by
    have h := hlog1.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, ← div_eq_mul_one_div] using h
  -- eventual decomposition for `N ≥ 1`
  have heq : ∀ᶠ N : ℕ in atTop,
      Real.log (lt ^ N + lb ^ N) / N = Real.log lt + Real.log (1 + r ^ N) / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hltN : 0 < lt ^ N := pow_pos hlt N
    have hfact : lt ^ N + lb ^ N = lt ^ N * (1 + r ^ N) := by
      rw [hr_def, div_pow, mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hltN)]
    rw [hfact, Real.log_mul (ne_of_gt hltN) (by positivity), Real.log_pow,
      add_div, mul_div_cancel_left₀ _ hN0]
  -- assemble
  have hsum : Tendsto (fun N : ℕ => Real.log lt + Real.log (1 + r ^ N) / N)
      atTop (𝓝 (Real.log lt)) := by
    simpa using tendsto_const_nhds.add hdiv
  refine hsum.congr' ?_
  filter_upwards [heq] with N h
  exact h.symm

/-- **Free-energy density from the transfer-matrix trace** (Glimm–Jaffe §17.1):
for `a = β J > 0`,
`(1/N)·log Tr(T(a)ᴺ) → log λ₊`.  Since `Z_N = Tr(T(a)ᴺ)` is the cyclic-chain
partition function, the limit is the 1D Ising free-energy density. -/
theorem tendsto_log_trace_pow_div_nat {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (isingTransferMatrix1D a ^ N).trace / N)
      atTop (𝓝 (Real.log (transferEigenvalueTop a))) := by
  refine (tendsto_log_eigenvalueSum_div_nat ha).congr fun N => ?_
  rw [trace_isingTransferMatrix1D_pow]

/-- The dominant-eigenvalue free energy in closed hyperbolic form:
`log λ₊ = log(2·cosh a)`. -/
theorem log_transferEigenvalueTop_eq (a : ℝ) :
    Real.log (transferEigenvalueTop a) = Real.log (2 * Real.cosh a) := by
  rw [transferEigenvalueTop_eq]

end TransferMatrix

end IsingModel
