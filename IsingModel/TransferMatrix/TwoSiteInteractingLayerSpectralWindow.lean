import IsingModel.TransferMatrix.TwoSiteInteractingLayerSpectralData
import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum

/-!
# Two-site interacting layer simple spectrum and spectral window

This file analyzes the explicit interacting `K2` diagonalization of
`TwoSiteInteractingLayerSpectralData` to supply the structural inputs of the
open-boundary simple-parity decay route.  The layer is `S = Fin 2` with internal
graph `completeGraph (Fin 2)` (one transverse edge) and identity longitudinal
transition, the genuinely interacting layer the free Walsh route cannot handle.

The four eigenvalues are strictly ordered
`top > flipOdd > swapOdd > evenBot > 0` for `0 < βJ` (using the determinant
relation `top · evenBot = flipOdd · swapOdd`), so the spectral data has a simple
spectrum.  The dominant `top` rotation column `(c, s, s, c)/√2` is strictly
positive (`c, s > 0`), hence signed-positive.  The subdominant decay parameter
is `theta = flipOdd / top` (not `tanh`), with `theta < 1`, and every non-top
eigenvalue is bounded by `theta · top` in absolute value.

These finite inputs feed the columnwise-simple-eigenspace boundary-window
consumer once the remaining open boundary-window cap estimate is supplied (a
later step: the interacting balanced boundary vector is not constant, so the
cap argument differs from the one-site/free cases).  This file does not yet
prove the open-slab decay bound, a closed-form decay rate, a thermodynamic
limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## Odd-sector eigenvalues and the spectral window parameter -/

/-- The flip-odd eigenvalue `e^{3a} - e^{-a}`. -/
noncomputable def twoSiteK2FlipOdd (a : ℝ) : ℝ := Real.exp (3 * a) - Real.exp (-a)

/-- The swap-odd eigenvalue `e^{a} - e^{-3a}`. -/
noncomputable def twoSiteK2SwapOdd (a : ℝ) : ℝ := Real.exp a - Real.exp (-(3 * a))

/-- The subdominant decay parameter `flipOdd / top`. -/
noncomputable def twoSiteInteractingTheta (a : ℝ) : ℝ :=
  twoSiteK2FlipOdd a / twoSiteK2Top a

/-! ## Eigenvalue positivity and ordering -/

/-- The dominant eigenvalue is positive. -/
theorem twoSiteK2Top_pos (a : ℝ) : 0 < twoSiteK2Top a := by
  rw [twoSiteK2Top, twoSiteK2EvenA, twoSiteK2EvenB]
  have := twoSiteK2Rad_pos a
  have := Real.exp_pos (3 * a); have := Real.exp_pos (-a)
  have := Real.exp_pos a; have := Real.exp_pos (-(3 * a))
  linarith

/-- The swap-odd eigenvalue is positive for `0 < a`. -/
theorem twoSiteK2SwapOdd_pos {a : ℝ} (ha : 0 < a) : 0 < twoSiteK2SwapOdd a := by
  rw [twoSiteK2SwapOdd]
  have : Real.exp (-(3 * a)) < Real.exp a := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- The flip-odd eigenvalue equals `e^{2a}` times the swap-odd eigenvalue. -/
theorem twoSiteK2FlipOdd_eq (a : ℝ) :
    twoSiteK2FlipOdd a = Real.exp (2 * a) * twoSiteK2SwapOdd a := by
  rw [twoSiteK2FlipOdd, twoSiteK2SwapOdd, mul_sub, ← Real.exp_add, ← Real.exp_add,
    show (2 * a + a : ℝ) = 3 * a from by ring,
    show (2 * a + -(3 * a) : ℝ) = -a from by ring]

/-- The flip-odd eigenvalue is strictly larger than the swap-odd eigenvalue. -/
theorem twoSiteK2FlipOdd_gt_SwapOdd {a : ℝ} (ha : 0 < a) :
    twoSiteK2FlipOdd a > twoSiteK2SwapOdd a := by
  rw [twoSiteK2FlipOdd_eq]
  have h1 : 1 < Real.exp (2 * a) := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  nlinarith [twoSiteK2SwapOdd_pos ha, h1]

/-- The flip-odd eigenvalue is positive for `0 < a`. -/
theorem twoSiteK2FlipOdd_pos {a : ℝ} (ha : 0 < a) : 0 < twoSiteK2FlipOdd a :=
  lt_trans (twoSiteK2SwapOdd_pos ha) (twoSiteK2FlipOdd_gt_SwapOdd ha)

/-- The dominant eigenvalue strictly dominates the flip-odd eigenvalue. -/
theorem twoSiteK2Top_gt_FlipOdd (a : ℝ) : twoSiteK2Top a > twoSiteK2FlipOdd a := by
  rw [twoSiteK2Top, twoSiteK2EvenA, twoSiteK2EvenB, twoSiteK2FlipOdd]
  have hrd := twoSiteK2_rad_sub_delta_nonneg a
  rw [twoSiteK2Delta, twoSiteK2EvenA, twoSiteK2EvenB] at hrd
  have := Real.exp_pos (-a); have := Real.exp_pos a; have := Real.exp_pos (-(3 * a))
  linarith

/-- Determinant relation: `top · evenBot = flipOdd · swapOdd`. -/
theorem twoSiteK2_det (a : ℝ) :
    twoSiteK2Top a * twoSiteK2EvenBot a = twoSiteK2FlipOdd a * twoSiteK2SwapOdd a := by
  have e1 : Real.exp (3 * a) * Real.exp (-(3 * a)) = 1 := by rw [← Real.exp_add]; norm_num
  have e2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; norm_num
  rw [twoSiteK2Top, twoSiteK2EvenBot, twoSiteK2EvenA, twoSiteK2EvenB, twoSiteK2FlipOdd,
    twoSiteK2SwapOdd]
  have hr := twoSiteK2Rad_sq a
  rw [twoSiteK2Delta, twoSiteK2EvenA, twoSiteK2EvenB] at hr
  nlinarith [hr, e1, e2]

/-- The subdominant eigenvalue is positive for `0 < a`. -/
theorem twoSiteK2EvenBot_pos {a : ℝ} (ha : 0 < a) : 0 < twoSiteK2EvenBot a := by
  have hd := twoSiteK2_det a
  nlinarith [hd, twoSiteK2Top_pos a, twoSiteK2FlipOdd_pos ha, twoSiteK2SwapOdd_pos ha]

/-- The swap-odd eigenvalue strictly dominates the subdominant eigenvalue. -/
theorem twoSiteK2SwapOdd_gt_EvenBot {a : ℝ} (ha : 0 < a) :
    twoSiteK2SwapOdd a > twoSiteK2EvenBot a := by
  have hd := twoSiteK2_det a
  nlinarith [hd, twoSiteK2Top_pos a, twoSiteK2SwapOdd_pos ha, twoSiteK2Top_gt_FlipOdd a,
    twoSiteK2FlipOdd_pos ha]

/-! ## Simple spectrum -/

/-- The interacting transfer-matrix spectral data has a simple spectrum for
`0 < a`: the four eigenvalues are strictly ordered, hence distinct. -/
theorem twoSiteInteractingTransferOrthogonalSpectralData_simpleSpectrum {a : ℝ}
    (ha : 0 < a) :
    (twoSiteInteractingTransferOrthogonalSpectralData a).SimpleSpectrum := by
  have h12 := twoSiteK2Top_gt_FlipOdd a
  have h23 := twoSiteK2FlipOdd_gt_SwapOdd ha
  have h34 := twoSiteK2SwapOdd_gt_EvenBot ha
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [twoSiteInteractingTransferOrthogonalSpectralData,
      twoSiteInteractingTransferEigenvalue, twoSiteK2FlipOdd, twoSiteK2SwapOdd] <;>
    linarith

/-- The physical interacting two-site layer spectral data has a simple spectrum
for `0 < βJ`. -/
theorem twoSiteInteractingLayerOrthogonalSpectralData_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).SimpleSpectrum := by
  have hbase := twoSiteInteractingTransferOrthogonalSpectralData_simpleSpectrum hβJ
  intro i j hij
  apply layerStateFin2EquivFin2Prod.injective
  apply hbase
  simpa [twoSiteInteractingLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex]
    using hij

/-! ## Signed-positive dominant column -/

/-- The even-sector rotation cosine is positive. -/
theorem twoSiteK2RotC_pos (a : ℝ) : 0 < twoSiteK2RotC a := by
  rw [twoSiteK2RotC]
  refine Real.sqrt_pos.mpr (div_pos ?_ ?_)
  · have hr := twoSiteK2Rad_sq a; have hp := twoSiteK2Rad_pos a
    nlinarith [hr, hp, sq_nonneg (twoSiteK2Rad a + twoSiteK2Delta a)]
  · have := twoSiteK2Rad_pos a; linarith

/-- The even-sector rotation sine is positive. -/
theorem twoSiteK2RotS_pos (a : ℝ) : 0 < twoSiteK2RotS a := by
  rw [twoSiteK2RotS]
  refine Real.sqrt_pos.mpr (div_pos ?_ ?_)
  · have hr := twoSiteK2Rad_sq a; have hp := twoSiteK2Rad_pos a
    nlinarith [hr, hp, sq_nonneg (twoSiteK2Rad a - twoSiteK2Delta a)]
  · have := twoSiteK2Rad_pos a; linarith

/-- The dominant `(0,0)` rotation column of the interacting transfer matrix is
signed-positive with sign `1`. -/
noncomputable def twoSiteInteractingTransferOrthogonalSpectralData_top_signedPositiveColumn
    (a : ℝ) :
    (twoSiteInteractingTransferOrthogonalSpectralData a).SignedPositiveColumn (0, 0) where
  sign := 1
  sign_mul_self := by norm_num
  positive := by
    intro ω
    have hc := twoSiteK2RotC_pos a; have hs := twoSiteK2RotS_pos a
    have h2 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    simp only [one_mul, twoSiteInteractingTransferOrthogonalSpectralData,
      twoSiteInteractingChangeOfBasis, Matrix.of_apply, ↓reduceIte, spin1D]
    fin_cases ω <;> norm_num <;> nlinarith [hc, hs, h2]

/-- The explicit top index of the physical interacting two-site layer. -/
def twoSiteInteractingLayerTop : LayerState (Fin 2) :=
  layerStateFin2EquivFin2Prod.symm (0, 0)

/-- The dominant column of the physical interacting two-site layer is
signed-positive with sign `1`. -/
noncomputable def twoSiteInteractingLayerOrthogonalSpectralData_top_signedPositiveColumn
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).SignedPositiveColumn
      twoSiteInteractingLayerTop where
  sign := 1
  sign_mul_self := by norm_num
  positive := by
    intro ω
    have hbase : 0 < (twoSiteInteractingTransferOrthogonalSpectralData
        (p.β * p.J)).changeOfBasis (layerStateFin2EquivFin2Prod ω) (0, 0) := by
      have h :=
        (twoSiteInteractingTransferOrthogonalSpectralData_top_signedPositiveColumn
          (p.β * p.J)).positive (layerStateFin2EquivFin2Prod ω)
      simpa only [twoSiteInteractingTransferOrthogonalSpectralData_top_signedPositiveColumn,
        one_mul] using h
    simpa [twoSiteInteractingLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
      twoSiteInteractingLayerTop] using hbase

/-! ## Spectral window parameter -/

/-- The decay parameter is nonnegative for `0 < a`. -/
theorem twoSiteInteractingTheta_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ twoSiteInteractingTheta a :=
  div_nonneg (twoSiteK2FlipOdd_pos ha).le (twoSiteK2Top_pos a).le

/-- The decay parameter is strictly below `1`. -/
theorem twoSiteInteractingTheta_lt_one (a : ℝ) :
    twoSiteInteractingTheta a < 1 :=
  (div_lt_one (twoSiteK2Top_pos a)).mpr (twoSiteK2Top_gt_FlipOdd a)

/-- `theta · top = flipOdd`. -/
theorem twoSiteInteractingTheta_mul_top (a : ℝ) :
    twoSiteInteractingTheta a * twoSiteK2Top a = twoSiteK2FlipOdd a := by
  rw [twoSiteInteractingTheta, div_mul_cancel₀ _ (ne_of_gt (twoSiteK2Top_pos a))]

/-- The layer eigenvalue at the top index is the dominant eigenvalue. -/
theorem twoSiteInteractingLayerOrthogonalSpectralData_top_eigenvalue
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).eigenvalue
        twoSiteInteractingLayerTop = twoSiteK2Top (p.β * p.J) := by
  simp [twoSiteInteractingLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex,
    twoSiteInteractingTransferOrthogonalSpectralData, twoSiteInteractingTransferEigenvalue,
    twoSiteInteractingLayerTop]

/-- The interacting transfer-matrix spectral window: every non-top eigenvalue is
bounded in absolute value by `theta` times the dominant eigenvalue. -/
theorem twoSiteInteractingTransferOrthogonalSpectralData_subdominant_abs_le {a : ℝ}
    (ha : 0 < a) :
    ∀ i, i ≠ (0, 0) →
      |(twoSiteInteractingTransferOrthogonalSpectralData a).eigenvalue i| ≤
        twoSiteInteractingTheta a *
          (twoSiteInteractingTransferOrthogonalSpectralData a).eigenvalue (0, 0) := by
  have hmt := twoSiteInteractingTheta_mul_top a
  have hfp := twoSiteK2FlipOdd_pos ha
  have hsp := twoSiteK2SwapOdd_pos ha
  have hep := twoSiteK2EvenBot_pos ha
  have hfs := twoSiteK2FlipOdd_gt_SwapOdd ha
  have hse := twoSiteK2SwapOdd_gt_EvenBot ha
  intro i hi
  fin_cases i <;>
    simp_all [twoSiteInteractingTransferOrthogonalSpectralData,
      twoSiteInteractingTransferEigenvalue, twoSiteK2FlipOdd, twoSiteK2SwapOdd] <;>
    rw [abs_of_pos (by linarith)] <;> linarith

/-- The physical layer spectral window with decay parameter
`theta = flipOdd / top`. -/
theorem twoSiteInteractingLayerSpectralWindow_theta
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) :
    ∀ i, i ≠ twoSiteInteractingLayerTop →
      |(twoSiteInteractingLayerOrthogonalSpectralData p hp).eigenvalue i| ≤
        twoSiteInteractingTheta (p.β * p.J) *
          (twoSiteInteractingLayerOrthogonalSpectralData p hp).eigenvalue
            twoSiteInteractingLayerTop := by
  rw [twoSiteInteractingLayerOrthogonalSpectralData_top_eigenvalue p hp]
  have hbase :=
    twoSiteInteractingTransferOrthogonalSpectralData_subdominant_abs_le hβJ
  intro i hi
  have hne : layerStateFin2EquivFin2Prod i ≠ (0, 0) := by
    intro h
    apply hi
    rw [twoSiteInteractingLayerTop, ← h, Equiv.symm_apply_apply]
  simpa [twoSiteInteractingLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex]
    using hbase (layerStateFin2EquivFin2Prod i) hne

end TransferMatrix

end IsingModel
