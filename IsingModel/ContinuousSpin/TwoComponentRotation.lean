import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The (4.3.2) rotation is measure-preserving (GJ Theorem 4.7.1)

The per-site duplicate-variable rotation of Glimm–Jaffe §4.7, given by the
formulas (4.3.2) applied to the two-component pair `(t, q)` and its duplicate
`(t', q')`:
`α = (t+t')/√2`, `β = (t−t')/√2`, `γ = (q+q')/√2`, `δ = (q'−q)/√2`.
This is the *block* `√2`-rotation that mixes the two copies coordinate by
coordinate (the `t`-pair into `(α, β)` and the `q`-pair into `(γ, δ)`); it is the
rotation for which the doubled field is `√2·(h¹·α + h²·γ)` and the difference
observables expand with non-negative coefficients, as required by the
duplicate-variable proof of (4.7.6)–(4.7.8).  (It is *not* the Hadamard rotation
`phi4Alpha, …` of §4.3, which mixes all four coordinates; that rotation realises
the doubled potential of the scalar `φ⁴` theory.)

All entries are `0` or `±√2/2`, with orthonormal rows, so the map is an
orthogonal automorphism of `ℝ⁴ = (Fin 4 → ℝ)` and is measure-preserving;
applied at every site it gives the measure-preserving change of variables on the
doubled configuration space `(ι → Fin 4 → ℝ)`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, (4.3.2), p. 59; §4.7, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory Matrix

/-- The §4.7 block `√2`-rotation matrix on `ℝ⁴` (coordinates `t, q, t', q'`), with
output rows `(α, β, γ, δ) = ((t+t')/√2, (t−t')/√2, (q+q')/√2, (q'−q)/√2)`.  Every
entry is `0` or `±√2/2`. -/
noncomputable def rotMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2, 0],
    ![Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2), 0],
    ![0, Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2],
    ![0, -(Real.sqrt 2 / 2), 0, Real.sqrt 2 / 2]]

/-- The defining product `√2/2 · √2/2 = 1/2`. -/
theorem sqrt2_half_mul_self : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- The rotation matrix is orthogonal: `M·Mᵀ = 1`. -/
theorem rotMatrix_mul_transpose : rotMatrix * rotMatrixᵀ = 1 := by
  have hc := sqrt2_half_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    nlinarith [hc]

/-- The determinant of the rotation matrix squares to `1`. -/
theorem rotMatrix_det_sq : rotMatrix.det ^ 2 = 1 := by
  have h := congrArg Matrix.det rotMatrix_mul_transpose
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  nlinarith [h]

/-- The determinant of the rotation matrix is nonzero. -/
theorem rotMatrix_det_ne_zero : rotMatrix.det ≠ 0 := by
  intro h
  have := rotMatrix_det_sq
  rw [h] at this
  norm_num at this

/-- The absolute value of the determinant of the rotation matrix is `1`. -/
theorem abs_rotMatrix_det : |rotMatrix.det| = 1 := by
  have h := rotMatrix_det_sq
  have : |rotMatrix.det| ^ 2 = 1 := by rw [← abs_pow, h, abs_one]
  nlinarith [abs_nonneg rotMatrix.det, this]

/-- The (4.3.2) rotation as a linear automorphism of `ℝ⁴ = (Fin 4 → ℝ)`. -/
noncomputable def rotLin : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := Matrix.toLin' rotMatrix

/-- The determinant of the rotation linear map equals that of the matrix. -/
theorem rotLin_det : LinearMap.det rotLin = rotMatrix.det := LinearMap.det_toLin' rotMatrix

/-- **The single-site (4.3.2) rotation is measure-preserving** on `ℝ⁴`. -/
theorem measurePreserving_rotLin :
    MeasurePreserving rotLin (volume : Measure (Fin 4 → ℝ)) volume := by
  refine ⟨(LinearMap.continuous_of_finiteDimensional rotLin).measurable, ?_⟩
  have hne : LinearMap.det rotLin ≠ 0 := by rw [rotLin_det]; exact rotMatrix_det_ne_zero
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne]
  have : |(LinearMap.det rotLin)⁻¹| = 1 := by
    rw [abs_inv, rotLin_det, abs_rotMatrix_det, inv_one]
  rw [this, ENNReal.ofReal_one, one_smul]

/-- **The site-wise (4.3.2) rotation is measure-preserving** on the doubled
configuration space `(ι → Fin 4 → ℝ)`. -/
theorem measurePreserving_rotLinPi {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun (cfg : ι → Fin 4 → ℝ) (i : ι) => rotLin (cfg i))
      (volume : Measure (ι → Fin 4 → ℝ)) volume :=
  volume_preserving_pi (fun _ => measurePreserving_rotLin)

end IsingModel.ContinuousSpin
