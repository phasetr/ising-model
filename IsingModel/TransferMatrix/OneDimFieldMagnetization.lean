import IsingModel.TransferMatrix.OneDimField
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Magnetization of the 1D Ising chain in a field (Glimm–Jaffe §17.1)

The free-energy density of the 1D Ising chain in a field is `log λ₊(a, b)`
(`TransferMatrix/OneDimFieldPower.lean`), with `a = β J`, `b = β h` and
`λ₊ = eᵃ cosh b + √D`, `D = e^{2a} sinh²b + e^{-2a}`.  Its derivative with respect
to the field parameter `b` is the **magnetization**

  `m(h) = ∂_b log λ₊ = sinh b / √(sinh²b + e^{-4a})`.

The closed form follows from the factorisation `√D = eᵃ √(sinh²b + e^{-4a})`,
which collapses the logarithmic derivative `(∂_b λ₊)/λ₊` to `sinh b / √(...)`.
The magnetization is an odd, strictly sub-saturated function of the field,
`|m| < 1`, vanishing at `h = 0` — there is no spontaneous magnetization in one
dimension.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), pp. 304–306.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.3.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- The **magnetization** of the 1D Ising chain in a field, in closed form:
`m(a, b) = sinh b / √(sinh²b + e^{-4a})` with `a = β J`, `b = β h`. -/
noncomputable def fieldMagnetization (a b : ℝ) : ℝ :=
  Real.sinh b / Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a)))

/-- The derivative of the discriminant `D(b) = e^{2a} sinh²b + e^{-2a}` in `b` is
`e^{2a} · 2 sinh b cosh b`. -/
theorem hasDerivAt_fieldTransferDiscriminant (a b : ℝ) :
    HasDerivAt (fun b' => fieldTransferDiscriminant a b')
      (Real.exp (2 * a) * (2 * Real.sinh b * Real.cosh b)) b := by
  have hsq : HasDerivAt (fun b' => Real.sinh b' ^ 2)
      (2 * Real.sinh b ^ 1 * Real.cosh b) b := (Real.hasDerivAt_sinh b).pow 2
  have h := (hsq.const_mul (Real.exp (2 * a))).add_const (Real.exp (-(2 * a)))
  simpa only [fieldTransferDiscriminant, pow_one] using h

/-- **Square-root factorisation of the discriminant**:
`√D = eᵃ · √(sinh²b + e^{-4a})`, since `D = e^{2a}(sinh²b + e^{-4a})` and
`√(e^{2a}) = eᵃ`. -/
theorem sqrt_fieldTransferDiscriminant (a b : ℝ) :
    Real.sqrt (fieldTransferDiscriminant a b)
      = Real.exp a * Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) := by
  have hmul : Real.exp (2 * a) * Real.exp (-(4 * a)) = Real.exp (-(2 * a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hfac : fieldTransferDiscriminant a b
      = Real.exp (2 * a) * (Real.sinh b ^ 2 + Real.exp (-(4 * a))) := by
    rw [fieldTransferDiscriminant, mul_add, hmul]
  rw [hfac, Real.sqrt_mul (Real.exp_nonneg _),
    show Real.exp (2 * a) = Real.exp a ^ 2 from by rw [pow_two, ← Real.exp_add]; congr 1; ring,
    Real.sqrt_sq (Real.exp_nonneg _)]

/-- **Magnetization as the field-derivative of the free-energy density**
(Glimm–Jaffe §17.1): for all `a, b`,

`d/db [ log λ₊(a, b) ] = fieldMagnetization a b = sinh b / √(sinh²b + e^{-4a})`.

The logarithmic derivative `(∂_b λ₊)/λ₊` collapses via the factorisation
`√D = eᵃ √(sinh²b + e^{-4a})`. -/
theorem hasDerivAt_log_fieldTransferEigenvalueTop (a b : ℝ) :
    HasDerivAt (fun b' => Real.log (fieldTransferEigenvalueTop a b'))
      (fieldMagnetization a b) b := by
  have hDne : fieldTransferDiscriminant a b ≠ 0 := (fieldTransferDiscriminant_pos a b).ne'
  have hsqrt : HasDerivAt (fun b' => Real.sqrt (fieldTransferDiscriminant a b'))
      (Real.exp (2 * a) * (2 * Real.sinh b * Real.cosh b)
        / (2 * Real.sqrt (fieldTransferDiscriminant a b))) b :=
    (hasDerivAt_fieldTransferDiscriminant a b).sqrt hDne
  have hcosh : HasDerivAt (fun b' => Real.exp a * Real.cosh b')
      (Real.exp a * Real.sinh b) b := (Real.hasDerivAt_cosh b).const_mul _
  have hlam : HasDerivAt (fun b' => fieldTransferEigenvalueTop a b')
      (Real.exp a * Real.sinh b
        + Real.exp (2 * a) * (2 * Real.sinh b * Real.cosh b)
          / (2 * Real.sqrt (fieldTransferDiscriminant a b))) b := hcosh.add hsqrt
  have hpos := fieldTransferEigenvalueTop_pos a b
  have hlog := hlam.log hpos.ne'
  convert hlog using 1
  -- goal: fieldMagnetization a b = (numerator) / λ₊
  have hQpos : 0 < Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) :=
    Real.sqrt_pos.mpr (by positivity)
  have hea : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have he2 : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  have hden : Real.exp a * Real.cosh b
      + Real.exp a * Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) ≠ 0 := by
    have := Real.cosh_pos b
    positivity
  rw [fieldMagnetization, fieldTransferEigenvalueTop, sqrt_fieldTransferDiscriminant, he2]
  field_simp
  ring

/-- The magnetization vanishes at zero field, `m(a, 0) = 0` — no spontaneous
magnetization in one dimension. -/
@[simp] theorem fieldMagnetization_zero (a : ℝ) : fieldMagnetization a 0 = 0 := by
  rw [fieldMagnetization, Real.sinh_zero, zero_div]

/-- The magnetization is strictly sub-saturated, `|m| < 1`, since
`√(sinh²b + e^{-4a}) > |sinh b|` (the field gap `e^{-4a} > 0`). -/
theorem abs_fieldMagnetization_lt_one (a b : ℝ) : |fieldMagnetization a b| < 1 := by
  have hQpos : 0 < Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) :=
    Real.sqrt_pos.mpr (by positivity)
  have hgt : |Real.sinh b| < Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    have : 0 < Real.exp (-(4 * a)) := Real.exp_pos _
    nlinarith
  rw [fieldMagnetization, abs_div, abs_of_pos hQpos, div_lt_one hQpos]
  exact hgt

end TransferMatrix

end IsingModel
