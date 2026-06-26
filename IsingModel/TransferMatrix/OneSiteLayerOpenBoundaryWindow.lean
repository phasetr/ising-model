import IsingModel.TransferMatrix.OneSiteLayerSpectralWindow
import IsingModel.TransferMatrix.LayerOpenBoundaryWindowSimple
import IsingModel.RealTanhAux
import IsingModel.TransferMatrix.LayerOpenSimpleSpectrum

/-!
# One-site open boundary-window discharge

This file gives the first concrete discharge of the simple-spectrum
open-boundary boundary-window stack for an actual transfer matrix.  The
one-site transverse layer (`S = PUnit`, internal graph `⊥`, identity
longitudinal transition) is the genuine 2×2 one-dimensional Ising transfer
matrix.  Its two eigenvalues `transferEigenvalueTop` and
`transferEigenvalueBot = tanh(βJ) · transferEigenvalueTop` are distinct, so the
spectral data has a simple spectrum.  Combined with the constant balanced open
boundary vector (whose only nonzero spectral coordinate is the top Hadamard
column), this discharges the `SimpleSpectrum`/`SignedPositiveColumn`/
boundary-window inputs of the explicit open-boundary simple-parity consumer and
yields an unconditional finite one-site open-slab same-transverse-site
correlation bound with decay parameter `tanh (βJ)`.

The sharp coefficient-one form of the same one-site open-slab inequality
already exists as the `S = PUnit` specialization of
`correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh_clean`; this
file instead contributes the first concrete witness that the abstract
simple-spectrum boundary-window discharge of PR #4057 fires on a real
longitudinal transfer matrix.

These results are finite.  They do not prove an interacting transverse-layer
spectral window, a thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## Simple spectrum of the one-dimensional transfer matrix -/

/-- The explicit 2×2 one-dimensional transfer-matrix spectral data has a simple
spectrum: its two eigenvalues `transferEigenvalueTop` and
`transferEigenvalueBot` are distinct. -/
theorem isingTransferMatrix1DOrthogonalSpectralData_simpleSpectrum (a : ℝ) :
    (isingTransferMatrix1DOrthogonalSpectralData a).SimpleSpectrum := by
  have hne : transferEigenvalueBot a ≠ transferEigenvalueTop a :=
    ne_of_lt (transferEigenvalueBot_lt_top a)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [isingTransferMatrix1DOrthogonalSpectralData]

/-- The one-site physical layer spectral data has a simple spectrum. -/
theorem oneSiteLayerOrthogonalSpectralData_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (oneSiteLayerOrthogonalSpectralData p hp).SimpleSpectrum := by
  have hbase := isingTransferMatrix1DOrthogonalSpectralData_simpleSpectrum (p.β * p.J)
  intro i j hij
  apply layerStatePUnitEquivFin2.injective
  apply hbase
  simpa [oneSiteLayerOrthogonalSpectralData, RealOrthogonalSpectralData.reindex]
    using hij

/-! ## Signed-positive top column -/

/-- The explicit top index of the one-site layer spectral data. -/
def oneSiteLayerTop : LayerState (PUnit.{1}) :=
  layerStatePUnitEquivFin2.symm 0

/-- The one-site layer top Hadamard column equals the constant `1 / √2`. -/
theorem oneSiteLayerOrthogonalSpectralData_top_column
    (p : IsingParams ℝ) (hp : p.h = 0) (ω : LayerState (PUnit.{1})) :
    (oneSiteLayerOrthogonalSpectralData p hp).changeOfBasis ω oneSiteLayerTop =
      1 / Real.sqrt 2 := by
  simp only [oneSiteLayerOrthogonalSpectralData, oneSiteLayerTop,
    RealOrthogonalSpectralData.reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [isingTransferMatrix1DOrthogonalSpectralData_top_column]

/-- The one-site layer top column is signed-positive with sign `1`. -/
noncomputable def oneSiteLayerOrthogonalSpectralData_top_signedPositiveColumn
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (oneSiteLayerOrthogonalSpectralData p hp).SignedPositiveColumn
      oneSiteLayerTop where
  sign := 1
  sign_mul_self := by norm_num
  positive := by
    intro ω
    simp only [one_mul]
    rw [oneSiteLayerOrthogonalSpectralData_top_column p hp ω]
    positivity

/-! ## Vanishing off-top boundary coordinate and unit cap -/

/-- Every non-top boundary coordinate of the constant balanced open boundary
vector vanishes, because the off-top Hadamard column sums to zero over the two
one-site layer states. -/
theorem oneSiteLayerOrthogonalSpectralData_boundaryCoordinates_nonTop_zero
    (p : IsingParams ℝ) (hp : p.h = 0)
    {i : LayerState (PUnit.{1})} (hi : i ≠ oneSiteLayerTop) :
    (oneSiteLayerOrthogonalSpectralData p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)) i = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, layerStatePUnitEquivFin2 i = k := ⟨_, rfl⟩
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by
      intro h0
      apply hi
      rw [oneSiteLayerTop, ← h0, ← hk, Equiv.symm_apply_apply]
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with h | h
    · exact absurd h hk0
    · exact h
  rw [RealOrthogonalSpectralData.boundaryCoordinates]
  rw [← Equiv.sum_comp layerStatePUnitEquivFin2.symm
    (fun ω => layerOpenBalancedBoundaryVector
        (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p) ω *
      (oneSiteLayerOrthogonalSpectralData p hp).changeOfBasis ω i)]
  have hval : ∀ m : Fin 2,
      layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)
          (layerStatePUnitEquivFin2.symm m) *
        (oneSiteLayerOrthogonalSpectralData p hp).changeOfBasis
          (layerStatePUnitEquivFin2.symm m) i =
        (isingTransferMatrix1DOrthogonalSpectralData (p.β * p.J)).changeOfBasis m k := by
    intro m
    rw [layerOpenBalancedBoundaryVector,
      layerInternalWeight_punit_bot_h_zero p hp, Real.sqrt_one, one_mul]
    simp only [oneSiteLayerOrthogonalSpectralData,
      RealOrthogonalSpectralData.reindex, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply, hk]
  rw [Fin.sum_univ_two, hval 0, hval 1, hk1]
  simp [isingTransferMatrix1DOrthogonalSpectralData, normalizedHadamardMatrix,
    hadamardMatrix]

/-- The off-top boundary-coordinate mass of the one-site layer vanishes. -/
theorem oneSiteLayerOrthogonalSpectralData_boundaryCoordinateRestSq_zero
    (p : IsingParams ℝ) (hp : p.h = 0) :
    (oneSiteLayerOrthogonalSpectralData p hp).boundaryCoordinateRestSq
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)) oneSiteLayerTop = 0 := by
  unfold RealOrthogonalSpectralData.boundaryCoordinateRestSq
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi_ne : i ≠ oneSiteLayerTop := Finset.ne_of_mem_erase hi
  rw [oneSiteLayerOrthogonalSpectralData_boundaryCoordinates_nonTop_zero p hp hi_ne]
  ring

/-- The one-site open boundary-window cap equals `1`. -/
theorem oneSiteLayerBoundarySpectralWindowCap_eq_one
    (p : IsingParams ℝ) (hp : p.h = 0) :
    layerOpenBoundarySpectralWindowCap
        (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)
        (oneSiteLayerOrthogonalSpectralData p hp) oneSiteLayerTop = 1 := by
  have hzero := oneSiteLayerOrthogonalSpectralData_boundaryCoordinateRestSq_zero p hp
  simp only [layerOpenBoundarySpectralWindowCap,
    RealOrthogonalSpectralData.boundarySpectralWindowCap,
    RealOrthogonalSpectralData.boundarySpectralWindowThreshold]
  rw [if_pos hzero]
  norm_num

/-! ## Concrete simple-spectrum open-boundary discharge -/

/-- First concrete discharge of the simple-spectrum open-boundary boundary-window
consumer: the one-site open-slab same-transverse-site correlation obeys the
finite spectral bound with decay parameter `tanh (βJ)`.  All structural inputs
(`SimpleSpectrum`, signed positivity, unit boundary-window cap, and the
`tanh (βJ)` spectral window) are discharged concretely for `0 < βJ`. -/
theorem correlation_oneSiteLayerOpenSlabGraph_abs_le_of_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
        (layerOpenSlabGraph (S := PUnit.{1}) (⊥ : SimpleGraph (PUnit.{1}))
          (layerIdentityTransitionPairs (PUnit.{1})) (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) PUnit.unit,
          Prod.mk (layerOpenRightIndex left sep right) PUnit.unit} :
            Finset (LayerOpenSlabSite (left + sep + right) (PUnit.{1})))|
      ≤
        ((oneSiteLayerOrthogonalSpectralData p hp).boundaryMarkedSpectralPrefactor
            (layerSpinAt PUnit.unit)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)) /
          (oneSiteLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p))
            oneSiteLayerTop (Real.tanh (p.β * p.J))) *
          Real.tanh (p.β * p.J) ^ sep := by
  have htanh_nonneg : 0 ≤ Real.tanh (p.β * p.J) := real_tanh_nonneg hβJ.le
  have htanh_lt_cap :
      Real.tanh (p.β * p.J) <
        layerOpenBoundarySpectralWindowCap
          (layerInternalWeight (⊥ : SimpleGraph (PUnit.{1})) p)
          (oneSiteLayerOrthogonalSpectralData p hp) oneSiteLayerTop := by
    rw [oneSiteLayerBoundarySpectralWindowCap_eq_one p hp]
    exact Real.tanh_lt_one (p.β * p.J)
  exact
    correlation_layerOpenSlabGraph_abs_le_of_signedPositiveSimpleParity_boundaryWindow
      (⊥ : SimpleGraph (PUnit.{1})) (layerIdentityTransitionPairs (PUnit.{1}))
      p hp PUnit.unit
      (oneSiteLayerOrthogonalSpectralData p hp) oneSiteLayerTop
      (Real.tanh (p.β * p.J)) htanh_nonneg htanh_lt_cap
      (oneSiteLayerSpectralWindow_tanh.{0, 0} p hp (le_of_lt hβJ))
      ((oneSiteLayerOrthogonalSpectralData p hp).columnSimpleEigenspaces_of_simpleSpectrum
        (oneSiteLayerOrthogonalSpectralData_simpleSpectrum p hp))
      (oneSiteLayerOrthogonalSpectralData_top_signedPositiveColumn p hp)
      left sep right hsep

end TransferMatrix

end IsingModel
