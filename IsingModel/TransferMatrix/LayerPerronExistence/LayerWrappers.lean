import IsingModel.TransferMatrix.LayerPerronExistence.OrthogonalSpectralData

/-!
# Layer wrappers for signed-positive columns (GJ §17.1)

Layer-state specialisations of the `RealOrthogonalSpectralData` signed-positive
column API to the balanced layer transfer matrix: the maximal signed-positive
column, its canonical subdominant ratio, and the absolute-value, simplicity and
strict-ratio bounds it induces for the Hermitian balanced layer transfer matrix.
Part of the `LayerPerronExistence` signed-positive dominant column split.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Layer wrappers for signed-positive columns -/

/-- The maximal column of the Hermitian spectral data for a positive balanced
layer transfer matrix has a signed-positive orientation. -/
noncomputable def layerSymmetricTransfer_signedPositiveColumn_maxEigenIndex
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) :
    let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
    E.SignedPositiveColumn E.maxEigenIndex := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  exact E.signedPositiveColumn_maxEigenIndex
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- The canonical finite subdominant ratio attached to the maximal
signed-positive column of the Hermitian spectral data for the balanced layer
transfer matrix. -/
noncomputable def layerSymmetricTransfer_subdominantRatio_maxEigenIndex
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) : ℝ := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  exact E.subdominantRatio_maxEigenIndex
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- The canonical finite subdominant ratio for the Hermitian balanced layer
transfer matrix is strictly smaller than one. -/
theorem layerSymmetricTransfer_subdominantRatio_maxEigenIndex_lt_one
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hk_symm : ∀ ω η, k ω η = k η ω) :
    layerSymmetricTransfer_subdominantRatio_maxEigenIndex u k hu hk_pos hk_symm < 1 := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  let E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm
  simpa [layerSymmetricTransfer_subdominantRatio_maxEigenIndex, E] using
    E.subdominantRatio_maxEigenIndex_lt_one
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)

/-- A signed-positive balanced-layer spectral column bounds every spectral-data
eigenvalue in absolute value. -/
theorem layerSymmetricTransfer_eigenvalue_abs_le_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| ≤ E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_le_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hpos

/-- A signed-positive balanced-layer spectral column spans its eigenspace. -/
theorem layerSymmetricTransfer_signedPositiveColumn_eigenspace_simple
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top)
    {w : LayerState S → ℝ}
    (hw_eig : (layerSymmetricTransferMatrix u k).mulVec w =
      E.eigenvalue top • w) :
    ∃ c : ℝ, w = c • (fun ω => E.changeOfBasis ω top) := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenspace_simple_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos hw_eig

/-- A signed-positive balanced-layer spectral column gives strict absolute
inequality for each different spectral-data column. -/
theorem layerSymmetricTransfer_eigenvalue_abs_lt_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top i : LayerState S) (hi : i ≠ top)
    (hpos : E.SignedPositiveColumn top) :
    |E.eigenvalue i| < E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.eigenvalue_abs_lt_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top i hi hpos

/-- A signed-positive balanced-layer spectral column gives some strict finite
subdominant ratio for all non-top spectral-data eigenvalues. -/
theorem layerSymmetricTransfer_exists_subdominant_abs_ratio_of_signedPositiveColumn
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (hpos : E.SignedPositiveColumn top) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta < 1 ∧
      ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * E.eigenvalue top := by
  letI : Nonempty (LayerState S) := ⟨top⟩
  exact E.exists_subdominant_abs_ratio_of_signedPositiveColumn
    (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos) top hpos

end TransferMatrix

end IsingModel
