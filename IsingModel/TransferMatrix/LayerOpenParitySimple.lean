import IsingModel.TransferMatrix.LayerOpenPhysicalNormWindow

/-!
# Open-boundary parity from simple spectral columns

This file adds a finite structural bridge for the open-boundary transfer-matrix
route.  If a transfer matrix commutes with an involution and each chosen
spectral column spans its eigenspace, then every spectral column is either even
or odd under the involution.  Thus the existing open-boundary flip-parity
consumers can use a columnwise simple-eigenspace input instead of a direct
`ColumnFlipParity` hypothesis.

The results are finite and conditional.  They do not prove a physical
norm-window inequality, construct a parity-adapted basis inside degenerate
eigenspaces, prove an interacting cubic-layer spectral window, pass to a
thermodynamic limit, or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Columnwise simple eigenspaces imply flip parity -/

/-- The selected spectral columns span their corresponding eigenspaces.  This
is a columnwise simple-eigenspace condition for explicit real orthogonal
spectral data. -/
def ColumnSimpleEigenspaces {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) : Prop :=
  ∀ i (w : Ω → ℝ), M.mulVec w = E.eigenvalue i • w →
    ∃ c : ℝ, w = c • fun x => E.changeOfBasis x i

omit [Fintype Ω] [DecidableEq Ω] in
/-- A nonzero real vector that is a scalar multiple of its pullback by an
involution has scalar `1` or `-1`. -/
theorem scalar_eq_one_or_neg_one_of_comp_involutive_smul
    (τ : Ω ≃ Ω) (hτ : ∀ x, τ (τ x) = x)
    {v : Ω → ℝ} (hv : v ≠ 0) {c : ℝ}
    (hc : v ∘ τ = c • v) :
    c = 1 ∨ c = -1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, v x ≠ 0 := by
    by_contra h
    apply hv
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  have hc_apply : ∀ x, v (τ x) = c * v x := by
    intro x
    have h := congr_fun hc x
    simpa [Function.comp, Pi.smul_apply, smul_eq_mul] using h
  have hc_sq : c * c = 1 := by
    have h1 := hc_apply x0
    have h2 := hc_apply (τ x0)
    rw [hτ x0] at h2
    rw [h1] at h2
    have hmul : (c * c) * v x0 = 1 * v x0 := by
      rw [one_mul]
      calc
        (c * c) * v x0 = c * (c * v x0) := by ring
        _ = v x0 := h2.symm
    exact mul_right_cancel₀ hx0 hmul
  have hfactor : (c - 1) * (c + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · left
    linarith
  · right
    linarith

/-- If the matrix commutes with an involution and every selected spectral
column spans its eigenspace, the whole spectral basis has a definite flip
parity. -/
theorem columnFlipParity_of_commuting_involution_columnSimple {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω)
    (hτ : ∀ x, τ (τ x) = x)
    (hcomm : ∀ w : Ω → ℝ, M.mulVec (w ∘ τ) = M.mulVec w ∘ τ)
    (hsimple : E.ColumnSimpleEigenspaces) :
    E.ColumnFlipParity τ := by
  intro i
  let v : Ω → ℝ := fun x => E.changeOfBasis x i
  have hv_eig : M.mulVec v = E.eigenvalue i • v := by
    simpa [v] using E.mulVec_changeOfBasis_column i
  have hcomp_eig : M.mulVec (v ∘ τ) = E.eigenvalue i • (v ∘ τ) := by
    rw [hcomm v, hv_eig]
    ext x
    simp [Function.comp, Pi.smul_apply, smul_eq_mul]
  rcases hsimple i (v ∘ τ) hcomp_eig with ⟨c, hc⟩
  have hv_ne : v ≠ 0 := by
    simpa [v] using E.changeOfBasis_column_ne_zero i
  have hc_sign :
      c = 1 ∨ c = -1 :=
    scalar_eq_one_or_neg_one_of_comp_involutive_smul τ hτ hv_ne hc
  have hc_apply : ∀ x, E.changeOfBasis (τ x) i =
      c * E.changeOfBasis x i := by
    intro x
    have h := congr_fun hc x
    simpa [v, Function.comp, Pi.smul_apply, smul_eq_mul] using h
  rcases hc_sign with hc_one | hc_neg
  · left
    intro x
    simpa [hc_one] using hc_apply x
  · right
    intro x
    simpa [hc_neg] using hc_apply x

end RealOrthogonalSpectralData

/-! ## Layer specializations -/

/-- For a balanced layer transfer matrix, zero-field flip invariance plus
columnwise simple eigenspaces gives a flip-parity-adapted spectral basis. -/
theorem layerSymmetricTransfer_columnFlipParity_of_columnSimple
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hsimple : E.ColumnSimpleEigenspaces) :
    E.ColumnFlipParity (layerStateFlipEquiv S) :=
  E.columnFlipParity_of_commuting_involution_columnSimple
    (layerStateFlipEquiv S) (layerStateFlipEquiv_involutive S)
    (layerSymmetricTransferMatrix_mulVec_comp_equiv
      u k (layerStateFlipEquiv S) hu_flip hk_flip)
    hsimple

/-! ## Open-boundary consumers with simple-column parity input -/

/-- Open spin-observable min-gap certificate with flip-parity cancellation
derived from columnwise simple eigenspaces, canonical max-index ratio, and
norm-window denominator control. -/
noncomputable def
    layerOpenMinGapCert_of_maxEigenIndexSimpleParityCanonicalRatioBoundaryNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (hratio_norm :
      E.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)
        < layerOpenBoundaryNormWindowCap u E E.maxEigenIndex)
    (hsimple : E.ColumnSimpleEigenspaces) :
    LayerOpenMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerOpenMinGapCert_of_maxEigenIndexFlipParityCanonicalRatioBoundaryNormWindow
    u k x hu hk_pos hu_flip hk_flip E hratio_norm
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple
      u k hu_flip hk_flip E hsimple)

/-- Physical zero-field open spin-observable min-gap certificate with
flip-parity cancellation derived from columnwise simple eigenspaces, canonical
max-index ratio, and the physical norm-window denominator. -/
noncomputable def
    layerOpenMinGapCert_of_layerMaxEigenIndexSimpleParityCanonicalRatioPhysicalNormWindow
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenPhysicalBoundaryNormWindowCap
            H transitionPairs p spec spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces) :
    LayerOpenMinSpectralGapCertificate
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) :=
  layerOpenMinGapCert_of_layerMaxEigenIndexFlipParityCanonicalRatioPhysicalNormWindow
    H transitionPairs p hp x spec hratio_phys
    (layerSymmetricTransfer_columnFlipParity_of_columnSimple
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerInternalWeight_flip_of_h_zero H p hp)
      (layerTransitionWeight_flip_flip transitionPairs p) spec hsimple)

/-- Project-level finite open-slab same-transverse-site correlation decay with
the canonical max-index subdominant ratio, the physical norm-window
denominator, and flip parity derived from columnwise simple eigenspaces. -/
theorem
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          layerOpenPhysicalBoundaryNormWindowCap
            H transitionPairs p spec spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight H p)
                  (layerTransitionWeight transitionPairs p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_canonicalRatioPhysicalNormWindow
      H transitionPairs p hp x spec hratio_phys
      (layerSymmetricTransfer_columnFlipParity_of_columnSimple
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerInternalWeight_flip_of_h_zero H p hp)
        (layerTransitionWeight_flip_flip transitionPairs p) spec hsimple)
      left sep right hsep

/-- Cubic transverse open slabs inherit the simple-parity physical norm-window
consumer from the generic physical open-slab theorem. -/
theorem
    correlation_cubicLayerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0)
    (x : CubicLayerSite d R)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight (cubicLayerGraph d R) p)
        (layerTransitionWeight (cubicLayerTransitionPairs d R) p)))
    (hratio_phys :
      spec.subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
            (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))
        <
          cubicLayerOpenPhysicalBoundaryNormWindowCap
            d R p spec spec.maxEigenIndex)
    (hsimple : spec.ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (cubicLayerOpenSlabGraph d R (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R)))|
      ≤
        (spec.boundaryMarkedSpectralPrefactor (layerSpinAt x)
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p))
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (cubicLayerGraph d R) p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector
                (layerInternalWeight (cubicLayerGraph d R) p))
              spec.maxEigenIndex
              (spec.subdominantRatio_maxEigenIndex
                (layerSymmetricTransferMatrix_entrywisePositive
                  (layerInternalWeight (cubicLayerGraph d R) p)
                  (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
                  (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _)))) *
          (spec.subdominantRatio_maxEigenIndex
            (layerSymmetricTransferMatrix_entrywisePositive
              (layerInternalWeight (cubicLayerGraph d R) p)
              (layerTransitionWeight (cubicLayerTransitionPairs d R) p)
              (fun _ => Real.exp_pos _) (fun _ _ => Real.exp_pos _))) ^ sep := by
  rw [cubicLayerOpenSlabGraph]
  exact
    correlation_layerOpenSlabGraph_same_transverse_abs_le_of_physicalNormWindow_simpleParity
      (S := CubicLayerSite d R) (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p hp x spec
      (by simpa [cubicLayerOpenPhysicalBoundaryNormWindowCap] using hratio_phys)
      hsimple left sep right hsep

end TransferMatrix

end IsingModel
