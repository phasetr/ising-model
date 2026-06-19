import IsingModel.TransferMatrix.TwoSiteFreeLayerSpectralWindow
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum

/-!
# Two-site interacting layer spectral data

This file constructs the explicit orthogonal diagonalization of the first
*interacting* transverse-edge layer transfer matrix.  The layer is
`S = Fin 2` with internal graph `completeGraph (Fin 2)` (a single transverse
edge) and identity longitudinal transition.  Unlike the free two-site layer,
the transverse edge means the Walsh tensor basis no longer diagonalizes the
matrix; the even-spin sector mixes the two constant/antidiagonal modes through
a square-root rotation.

The results are finite explicit linear algebra.  This file only packages the
spectral data; the open-boundary decay discharge is left to a later step.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## Scalar data of the even sector -/

/-- Top-left even-sector diagonal entry `e^{3a} + e^{-a}`. -/
noncomputable def twoSiteK2EvenA (a : ℝ) : ℝ := Real.exp (3 * a) + Real.exp (-a)

/-- Lower even-sector diagonal entry `e^{a} + e^{-3a}`. -/
noncomputable def twoSiteK2EvenB (a : ℝ) : ℝ := Real.exp a + Real.exp (-(3 * a))

/-- Even-sector diagonal gap `A - B`. -/
noncomputable def twoSiteK2Delta (a : ℝ) : ℝ := twoSiteK2EvenA a - twoSiteK2EvenB a

/-- Even-sector discriminant radius `√(Δ² + 16)`. -/
noncomputable def twoSiteK2Rad (a : ℝ) : ℝ := Real.sqrt ((twoSiteK2Delta a) ^ 2 + 16)

/-- The discriminant radius is strictly positive. -/
theorem twoSiteK2Rad_pos (a : ℝ) : 0 < twoSiteK2Rad a := by
  rw [twoSiteK2Rad]
  apply Real.sqrt_pos.mpr
  positivity

/-- The discriminant radius squares to `Δ² + 16`. -/
theorem twoSiteK2Rad_sq (a : ℝ) : (twoSiteK2Rad a) ^ 2 = (twoSiteK2Delta a) ^ 2 + 16 := by
  rw [twoSiteK2Rad, Real.sq_sqrt (by positivity)]

/-- The discriminant radius is at least the absolute gap, so `rad + Δ ≥ 0`. -/
theorem twoSiteK2_rad_add_delta_nonneg (a : ℝ) :
    0 ≤ twoSiteK2Rad a + twoSiteK2Delta a := by
  have hrad := twoSiteK2Rad_pos a
  nlinarith [twoSiteK2Rad_sq a, sq_nonneg (twoSiteK2Delta a)]

/-- The discriminant radius dominates the gap, so `rad - Δ ≥ 0`. -/
theorem twoSiteK2_rad_sub_delta_nonneg (a : ℝ) :
    0 ≤ twoSiteK2Rad a - twoSiteK2Delta a := by
  have hrad := twoSiteK2Rad_pos a
  nlinarith [twoSiteK2Rad_sq a, sq_nonneg (twoSiteK2Delta a)]

/-! ## Even-sector rotation -/

/-- Even-sector rotation cosine `√((rad + Δ)/(2 rad))`. -/
noncomputable def twoSiteK2RotC (a : ℝ) : ℝ :=
  Real.sqrt ((twoSiteK2Rad a + twoSiteK2Delta a) / (2 * twoSiteK2Rad a))

/-- Even-sector rotation sine `√((rad - Δ)/(2 rad))`. -/
noncomputable def twoSiteK2RotS (a : ℝ) : ℝ :=
  Real.sqrt ((twoSiteK2Rad a - twoSiteK2Delta a) / (2 * twoSiteK2Rad a))

/-- The rotation cosine is nonnegative. -/
theorem twoSiteK2RotC_nonneg (a : ℝ) : 0 ≤ twoSiteK2RotC a := Real.sqrt_nonneg _

/-- The rotation sine is nonnegative. -/
theorem twoSiteK2RotS_nonneg (a : ℝ) : 0 ≤ twoSiteK2RotS a := Real.sqrt_nonneg _

/-- The squared rotation cosine. -/
theorem twoSiteK2RotC_sq (a : ℝ) :
    (twoSiteK2RotC a) ^ 2 = (twoSiteK2Rad a + twoSiteK2Delta a) / (2 * twoSiteK2Rad a) := by
  rw [twoSiteK2RotC, Real.sq_sqrt]
  exact div_nonneg (twoSiteK2_rad_add_delta_nonneg a) (by positivity [twoSiteK2Rad_pos a])

/-- The squared rotation sine. -/
theorem twoSiteK2RotS_sq (a : ℝ) :
    (twoSiteK2RotS a) ^ 2 = (twoSiteK2Rad a - twoSiteK2Delta a) / (2 * twoSiteK2Rad a) := by
  rw [twoSiteK2RotS, Real.sq_sqrt]
  exact div_nonneg (twoSiteK2_rad_sub_delta_nonneg a) (by positivity [twoSiteK2Rad_pos a])

/-- The rotation is a unit vector: `c² + s² = 1`. -/
theorem twoSiteK2RotC_sq_add_RotS_sq (a : ℝ) :
    (twoSiteK2RotC a) ^ 2 + (twoSiteK2RotS a) ^ 2 = 1 := by
  have hrad := twoSiteK2Rad_pos a
  rw [twoSiteK2RotC_sq, twoSiteK2RotS_sq]
  field_simp
  ring

/-- The rotation cross term `c · s = 2 / rad`. -/
theorem twoSiteK2RotC_mul_RotS (a : ℝ) :
    twoSiteK2RotC a * twoSiteK2RotS a = 2 / twoSiteK2Rad a := by
  have hrad := twoSiteK2Rad_pos a
  rw [twoSiteK2RotC, twoSiteK2RotS, ← Real.sqrt_mul (by positivity [twoSiteK2_rad_add_delta_nonneg a])]
  rw [show (twoSiteK2Rad a + twoSiteK2Delta a) / (2 * twoSiteK2Rad a) *
        ((twoSiteK2Rad a - twoSiteK2Delta a) / (2 * twoSiteK2Rad a))
      = ((twoSiteK2Rad a) ^ 2 - (twoSiteK2Delta a) ^ 2) / (4 * (twoSiteK2Rad a) ^ 2) from by
    ring]
  rw [twoSiteK2Rad_sq]
  rw [show ((twoSiteK2Delta a) ^ 2 + 16 - (twoSiteK2Delta a) ^ 2) = (16 : ℝ) from by ring]
  rw [show (16 : ℝ) / (4 * ((twoSiteK2Delta a) ^ 2 + 16)) = (2 / twoSiteK2Rad a) ^ 2 from by
    rw [div_pow, ← twoSiteK2Rad_sq]; ring]
  exact Real.sqrt_sq (by positivity [hrad])

/-! ## The interacting transfer matrix -/

/-- The balanced interacting two-site (`K2`) transfer matrix indexed by spin
pairs `Fin 2 × Fin 2`, with `a = βJ`.  The internal transverse edge contributes
the half-weight diagonal factors and the identity longitudinal transition
contributes the cross factor. -/
noncomputable def twoSiteInteractingTransferMatrix (a : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun σ τ =>
    Real.exp
      ((a / 2) * (spin1D σ.1 * spin1D σ.2 + spin1D τ.1 * spin1D τ.2)
        + a * (spin1D σ.1 * spin1D τ.1 + spin1D σ.2 * spin1D τ.2))

/-- The internal weight of the complete two-site graph at zero field reduces to
the single transverse-edge spin product. -/
theorem layerInternalWeight_completeGraph_fin2 (p : IsingParams ℝ) (hp : p.h = 0)
    (ω : LayerState (Fin 2)) :
    layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p ω =
      Real.exp (p.β * p.J * (Spin.sign ℝ (ω 0) * Spin.sign ℝ (ω 1))) := by
  rw [layerInternalWeight, hp]
  rw [show ((SimpleGraph.completeGraph (Fin 2)).edgeFinset) = {s(0, 1)} from by decide]
  simp [edgeSpin]

/-- At zero field the balanced complete two-site layer matrix is the reindexed
interacting transfer matrix. -/
theorem layerSymmetricTransferMatrix_fin2_complete_eq_reindex_twoSiteInteracting
    (p : IsingParams ℝ) (hp : p.h = 0) :
    layerSymmetricTransferMatrix
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)
        (layerTransitionWeight (layerIdentityTransitionPairs (Fin 2)) p) =
      (Matrix.reindex layerStateFin2EquivFin2Prod.symm layerStateFin2EquivFin2Prod.symm)
        (twoSiteInteractingTransferMatrix (p.β * p.J)) := by
  ext ω η
  rw [Matrix.reindex_apply]
  rw [layerSymmetricTransferMatrix, layerInternalWeight_completeGraph_fin2 p hp,
    layerInternalWeight_completeGraph_fin2 p hp]
  rw [← Real.exp_half, ← Real.exp_half]
  rw [layerTransitionWeight]
  rw [show ((layerIdentityTransitionPairs (Fin 2)) : Finset (Fin 2 × Fin 2))
        = {(0, 0), (1, 1)} from by decide]
  rw [← Real.exp_add, ← Real.exp_add]
  rw [twoSiteInteractingTransferMatrix]
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    layerStateFin2EquivFin2Prod, Equiv.coe_fn_mk, spin1D_spinEquivFin2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  congr 1
  ring

end TransferMatrix

end IsingModel
