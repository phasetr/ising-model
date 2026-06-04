import IsingModel.TransferMatrix.OneDimFieldMagnetization

/-!
# Susceptibility of the 1D Ising chain in a field (Glimm–Jaffe §17.1)

The magnetization of the 1D Ising chain in a field is
`m(a, b) = sinh b / √(sinh²b + e^{-4a})` (`TransferMatrix/OneDimFieldMagnetization.lean`),
with `a = β J`, `b = β h`.  Its derivative with respect to the field parameter
`b` is the (dimensionless) **susceptibility**

  `χ = ∂_b m = cosh b · e^{-4a} / (sinh²b + e^{-4a})^{3/2}`,

a strictly positive, bell-shaped function of the field.  The physical
susceptibility is `∂_h m = β · χ`; at zero field it takes the closed value
`χ(a, 0) = e^{2a}`, so `∂_h m|₀ = β e^{2a}` — the high-field-gap enhancement of
the zero-field susceptibility of the 1D chain.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1 (transfer matrix), pp. 304–306.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.3.
-/

namespace IsingModel

namespace TransferMatrix

/-- The **susceptibility** of the 1D Ising chain in a field, the field-derivative
of the magnetization, in closed form:
`χ(a, b) = cosh b · e^{-4a} / ((sinh²b + e^{-4a}) · √(sinh²b + e^{-4a}))`
(`= cosh b · e^{-4a} / (sinh²b + e^{-4a})^{3/2}`), with `a = β J`, `b = β h`. -/
noncomputable def fieldSusceptibility (a b : ℝ) : ℝ :=
  Real.cosh b * Real.exp (-(4 * a))
    / ((Real.sinh b ^ 2 + Real.exp (-(4 * a)))
        * Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))))

/-- The susceptibility is strictly positive. -/
theorem fieldSusceptibility_pos (a b : ℝ) : 0 < fieldSusceptibility a b := by
  rw [fieldSusceptibility]
  have hX : 0 < Real.sinh b ^ 2 + Real.exp (-(4 * a)) := by positivity
  have hsX : 0 < Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) := Real.sqrt_pos.mpr hX
  have hnum : 0 < Real.cosh b * Real.exp (-(4 * a)) :=
    mul_pos (Real.cosh_pos b) (Real.exp_pos _)
  positivity

/-- **Susceptibility as the field-derivative of the magnetization**
(Glimm–Jaffe §17.1): for all `a, b`,

`d/db [ fieldMagnetization a b ] = fieldSusceptibility a b`.

Differentiating `m = sinh b / √(sinh²b + e^{-4a})` by the quotient rule and using
`(√X)² = X`, `X − sinh²b = e^{-4a}` collapses the derivative to the closed
form. -/
theorem hasDerivAt_fieldMagnetization (a b : ℝ) :
    HasDerivAt (fun b' => fieldMagnetization a b') (fieldSusceptibility a b) b := by
  have hX : 0 < Real.sinh b ^ 2 + Real.exp (-(4 * a)) := by positivity
  have hXne : Real.sinh b ^ 2 + Real.exp (-(4 * a)) ≠ 0 := hX.ne'
  -- derivative of X(b') = sinh b'^2 + e^{-4a}
  have hXderiv : HasDerivAt (fun b' => Real.sinh b' ^ 2 + Real.exp (-(4 * a)))
      (2 * Real.sinh b * Real.cosh b) b := by
    have hsq : HasDerivAt (fun b' => Real.sinh b' ^ 2)
        (2 * Real.sinh b ^ 1 * Real.cosh b) b := (Real.hasDerivAt_sinh b).pow 2
    simpa only [pow_one] using hsq.add_const (Real.exp (-(4 * a)))
  -- derivative of √X
  have hQ : HasDerivAt (fun b' => Real.sqrt (Real.sinh b' ^ 2 + Real.exp (-(4 * a))))
      (2 * Real.sinh b * Real.cosh b
        / (2 * Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))))) b :=
    hXderiv.sqrt hXne
  have hsX : 0 < Real.sqrt (Real.sinh b ^ 2 + Real.exp (-(4 * a))) := Real.sqrt_pos.mpr hX
  -- quotient rule for m = sinh / √X
  have hm := (Real.hasDerivAt_sinh b).div hQ hsX.ne'
  convert hm using 1
  -- close the algebraic identity
  set X := Real.sinh b ^ 2 + Real.exp (-(4 * a)) with hXdef
  set q := Real.sqrt X with hqdef
  have hq2 : q ^ 2 = X := Real.sq_sqrt hX.le
  have he4 : Real.exp (-(4 * a)) = q ^ 2 - Real.sinh b ^ 2 := by rw [hq2, hXdef]; ring
  rw [fieldSusceptibility, ← hXdef, ← hqdef, he4, ← hq2]
  field_simp

/-- **Physical susceptibility** `∂_h m = β · χ` (Glimm–Jaffe §17.1): for fixed
`a = β J`, the derivative of the magnetization in the physical field `h` (with
`b = β h`) is `β` times the field-parameter susceptibility. -/
theorem hasDerivAt_fieldMagnetization_field (a β h : ℝ) :
    HasDerivAt (fun h' => fieldMagnetization a (β * h'))
      (fieldSusceptibility a (β * h) * β) h := by
  have hf : HasDerivAt (fun h' => β * h') β h := by
    simpa using (hasDerivAt_id h).const_mul β
  exact (hasDerivAt_fieldMagnetization a (β * h)).comp h hf

/-- The zero-field susceptibility is `χ(a, 0) = e^{2a}`, so the physical zero-field
susceptibility is `∂_h m|₀ = β e^{2a}` — the gap-enhanced susceptibility of the
1D Ising chain. -/
theorem fieldSusceptibility_zero (a : ℝ) : fieldSusceptibility a 0 = Real.exp (2 * a) := by
  have hEpos : 0 < Real.exp (-(2 * a)) := Real.exp_pos _
  have hE : Real.exp (-(4 * a)) = Real.exp (-(2 * a)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hsqrt : Real.sqrt (Real.sinh 0 ^ 2 + Real.exp (-(4 * a))) = Real.exp (-(2 * a)) := by
    rw [Real.sinh_zero, show (0 : ℝ) ^ 2 = 0 from by norm_num, zero_add, hE,
      Real.sqrt_sq hEpos.le]
  have hinv : (Real.exp (-(2 * a)))⁻¹ = Real.exp (2 * a) := by
    rw [← Real.exp_neg, neg_neg]
  rw [fieldSusceptibility, Real.cosh_zero, hsqrt, Real.sinh_zero,
    show (0 : ℝ) ^ 2 = 0 from by norm_num, zero_add, one_mul, hE, ← hinv]
  rw [pow_two]
  field_simp

end TransferMatrix

end IsingModel
