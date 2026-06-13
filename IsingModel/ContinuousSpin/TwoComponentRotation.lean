import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The (4.3.2) rotation is measure-preserving (GJ Theorem 4.7.1)

The per-site rotation `(t, q, t', q') ↦ (α, β, γ, δ)` of Glimm–Jaffe (4.3.2) — in
the project's convention (`phi4Alpha`, `phi4Beta`, `phi4Gamma`, `twoCompDelta`),
`α = (t+q+t'+q')/2`, `β = (t+q−t'−q')/2`, `γ = (t−q+t'−q')/2`,
`δ = −(t−q−t'+q')/2` — is an orthogonal linear map of `ℝ⁴ = (Fin 4 → ℝ)` (all
entries `±1/2`, with orthonormal rows), so it is measure-preserving.  Applied at
every site it gives the measure-preserving change of variables on the doubled
configuration space `(ι → Fin 4 → ℝ)` used by the duplicate-variable proof of the
second/third inequalities (4.7.6)–(4.7.8); this is the rotation entering
`twoCompPotential_double_eq`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, (4.3.2), p. 59; §4.7, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory Matrix

/-- The (4.3.2) rotation matrix on `ℝ⁴` (coordinates `t, q, t', q'`), with output
rows `(α, β, γ, δ) = (phi4Alpha, phi4Beta, phi4Gamma, twoCompDelta)`.  Every entry
is `±1/2`. -/
noncomputable def rotMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1 / 2, 1 / 2, 1 / 2, 1 / 2],
    ![1 / 2, 1 / 2, -(1 / 2), -(1 / 2)],
    ![1 / 2, -(1 / 2), 1 / 2, -(1 / 2)],
    ![-(1 / 2), 1 / 2, 1 / 2, -(1 / 2)]]

/-- The rotation matrix is orthogonal: `M·Mᵀ = 1`. -/
theorem rotMatrix_mul_transpose : rotMatrix * rotMatrixᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;> norm_num

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
