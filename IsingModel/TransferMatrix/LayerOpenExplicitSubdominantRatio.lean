import IsingModel.TransferMatrix.LayerOpenFiniteTransverseHermitian
import IsingModel.TransferMatrix.CubicLayerOpenBoxTransport

/-!
# Explicit subdominant ratio for open-slab spectral decay

The canonical decay ratio `RealOrthogonalSpectralData.subdominantRatio_maxEigenIndex`
used by `LayerOpenFiniteTransverseHermitian` is obtained by `Classical.choose`, so
a quantitative eigenvalue estimate `∀ i ≠ top, |λ_i| ≤ θ·λ_top` does **not**
directly bound the chosen ratio.  This file introduces the *explicit* subdominant
absolute ratio — the genuine finite maximum of `|λ_i| / λ_top` over the
non-maximal spectral indices — for which such an estimate gives a clean upper
bound `subdominantAbsRatio_maxEigenIndex ≤ θ`.

This is the entry point for the transverse-volume-uniform high-temperature
spectral window: a later Dobrushin/Perron-gap estimate supplying the hypothesis
`∀ i ≠ top, |λ_i| ≤ θ(β,J,d)·λ_top` (with `θ` independent of the transverse box
radius) will bound the explicit ratio uniformly, and these consumers then yield a
transverse-volume-uniform decay rate.

The results are finite and conditional on the boundary-window gap and the parity
input.  They do not construct the window uniformly, prove a thermodynamic limit,
or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

namespace RealOrthogonalSpectralData

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The **explicit subdominant absolute ratio** at the maximal eigenvalue: the
finite maximum of `|λ_i| / λ_top` over the non-maximal spectral indices (`0` when
the matrix has a single eigenvalue index). -/
noncomputable def subdominantAbsRatio_maxEigenIndex [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (_hM : MatrixEntrywisePositive M) : ℝ :=
  if h : (Finset.univ.erase E.maxEigenIndex).Nonempty then
    (Finset.univ.erase E.maxEigenIndex).sup' h
      (fun i => |E.eigenvalue i| / E.eigenvalue E.maxEigenIndex)
  else 0

/-- The explicit subdominant absolute ratio is nonnegative. -/
theorem subdominantAbsRatio_maxEigenIndex_nonneg [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M) :
    0 ≤ E.subdominantAbsRatio_maxEigenIndex hM := by
  rw [subdominantAbsRatio_maxEigenIndex]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have htop_pos : 0 < E.eigenvalue E.maxEigenIndex := E.eigenvalue_pos_maxEigenIndex hM
    refine le_trans (div_nonneg (abs_nonneg (E.eigenvalue i)) htop_pos.le) ?_
    exact Finset.le_sup' (fun i => |E.eigenvalue i| / E.eigenvalue E.maxEigenIndex) hi
  · exact le_rfl

/-- The defining property of the explicit subdominant absolute ratio: it bounds
every non-maximal eigenvalue in absolute value, scaled by the maximal
eigenvalue. -/
theorem eigenvalue_abs_le_subdominantAbsRatio_maxEigenIndex [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) (i : Ω) (hi : i ≠ E.maxEigenIndex) :
    |E.eigenvalue i| ≤ E.subdominantAbsRatio_maxEigenIndex hM * E.eigenvalue E.maxEigenIndex := by
  have htop_pos : 0 < E.eigenvalue E.maxEigenIndex := E.eigenvalue_pos_maxEigenIndex hM
  have himem : i ∈ Finset.univ.erase E.maxEigenIndex := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have hne : (Finset.univ.erase E.maxEigenIndex).Nonempty := ⟨i, himem⟩
  rw [subdominantAbsRatio_maxEigenIndex, dif_pos hne]
  rw [← div_le_iff₀ htop_pos]
  exact Finset.le_sup' (fun i => |E.eigenvalue i| / E.eigenvalue E.maxEigenIndex) himem

/-- The explicit subdominant absolute ratio is strictly below one. -/
theorem subdominantAbsRatio_maxEigenIndex_lt_one [Nonempty Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (hM : MatrixEntrywisePositive M) :
    E.subdominantAbsRatio_maxEigenIndex hM < 1 := by
  have htop_pos : 0 < E.eigenvalue E.maxEigenIndex := E.eigenvalue_pos_maxEigenIndex hM
  rw [subdominantAbsRatio_maxEigenIndex]
  split_ifs with h
  · rw [Finset.sup'_lt_iff]
    intro i hi
    have hi_ne : i ≠ E.maxEigenIndex := (Finset.mem_erase.mp hi).1
    exact (div_lt_one htop_pos).mpr (E.eigenvalue_abs_lt_maxEigenIndex hM i hi_ne)
  · exact zero_lt_one

/-- A quantitative eigenvalue estimate `∀ i ≠ top, |λ_i| ≤ θ·λ_top` (with
`0 ≤ θ`) bounds the explicit subdominant absolute ratio by `θ`.  The
nonnegativity of `θ` is needed for the single-eigenvalue-index case, where the
ratio is `0` and the estimate is vacuous.  This is the hook for a
transverse-volume-uniform Dobrushin/Perron-gap estimate. -/
theorem subdominantAbsRatio_maxEigenIndex_le_of_eigenvalue_abs_le [Nonempty Ω]
    {M : Matrix Ω Ω ℝ} (E : RealOrthogonalSpectralData M)
    (hM : MatrixEntrywisePositive M) {theta : ℝ} (htheta_nonneg : 0 ≤ theta)
    (hbound : ∀ i, i ≠ E.maxEigenIndex →
      |E.eigenvalue i| ≤ theta * E.eigenvalue E.maxEigenIndex) :
    E.subdominantAbsRatio_maxEigenIndex hM ≤ theta := by
  have htop_pos : 0 < E.eigenvalue E.maxEigenIndex := E.eigenvalue_pos_maxEigenIndex hM
  rw [subdominantAbsRatio_maxEigenIndex]
  split_ifs with h
  · rw [Finset.sup'_le_iff]
    intro i hi
    have hi_ne : i ≠ E.maxEigenIndex := (Finset.mem_erase.mp hi).1
    rw [div_le_iff₀ htop_pos]
    exact hbound i hi_ne
  · exact htheta_nonneg

end RealOrthogonalSpectralData

/-! ## Explicit-ratio open-slab decay consumers -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The explicit subdominant absolute ratio of the generic Hermitian layer
spectral data for an arbitrary finite transverse layer. -/
noncomputable def finiteTransverseHermitianExplicitRatio
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) : ℝ :=
  (finiteTransverseHermitianData H transitionPairs p hk_symm).subdominantAbsRatio_maxEigenIndex
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-- The explicit subdominant absolute ratio is strictly below one. -/
theorem finiteTransverseHermitianExplicitRatio_lt_one
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm < 1 :=
  (finiteTransverseHermitianData H transitionPairs p
    hk_symm).subdominantAbsRatio_maxEigenIndex_lt_one
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-- The explicit subdominant absolute ratio is nonnegative. -/
theorem finiteTransverseHermitianExplicitRatio_nonneg
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω) :
    0 ≤ finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm :=
  (finiteTransverseHermitianData H transitionPairs p
    hk_symm).subdominantAbsRatio_maxEigenIndex_nonneg
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)

/-- Finite open-slab decay with the **explicit** subdominant absolute ratio as
decay parameter.  Unlike the canonical-ratio consumer, the decay parameter here
is controlled directly by any quantitative eigenvalue estimate via
`subdominantAbsRatio_maxEigenIndex_le_of_eigenvalue_abs_le`. -/
theorem correlation_layerOpenSlabGraph_abs_le_of_hermitianExplicitRatioSimpleParityWindow
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    (hwindow :
      finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight H p)
          (finiteTransverseHermitianData H transitionPairs p hk_symm)
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
    (hsimple :
      (finiteTransverseHermitianData H transitionPairs p hk_symm).ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        ((finiteTransverseHermitianData H transitionPairs p hk_symm).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
          (finiteTransverseHermitianData H transitionPairs p
              hk_symm).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
            (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex
            (finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm)) *
          finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm ^ sep :=
  correlation_layerOpenSlabGraph_abs_le_of_maxEigenIndexSimpleParity_boundaryWindow
    H transitionPairs p hp x
    (finiteTransverseHermitianData H transitionPairs p hk_symm)
    (finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm)
    (finiteTransverseHermitianExplicitRatio_nonneg H transitionPairs p hk_symm)
    hwindow
    (fun i hi =>
      (finiteTransverseHermitianData H transitionPairs p
        hk_symm).eigenvalue_abs_le_subdominantAbsRatio_maxEigenIndex
        (finiteTransverseHermitian_entrywisePositive H transitionPairs p) i hi)
    hsimple left sep right hsep

/-! ## Cubic transverse layer explicit-ratio decay on the ambient box -/

/-- The explicit subdominant absolute ratio for the cubic transverse layer, with
the transition-weight symmetry discharged. -/
noncomputable def cubicLayerHermitianExplicitRatio (d R : ℕ) (p : IsingParams ℝ) : ℝ :=
  finiteTransverseHermitianExplicitRatio (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p)

/-- The cubic explicit subdominant absolute ratio is strictly below one. -/
theorem cubicLayerHermitianExplicitRatio_lt_one (d R : ℕ) (p : IsingParams ℝ) :
    cubicLayerHermitianExplicitRatio d R p < 1 :=
  finiteTransverseHermitianExplicitRatio_lt_one (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p)

/-- **Finite cubic open-box decay on the ambient lattice with the explicit
subdominant ratio.**  The explicit-ratio open-slab decay, specialized to the
cubic transverse layer and transported onto the induced finite volume of the
ambient `latticeGraph (d+1)` on the cubic open box.  The decay parameter
`cubicLayerHermitianExplicitRatio` is controlled directly by any quantitative
eigenvalue estimate, so this is the consumer a transverse-volume-uniform
high-temperature estimate will feed. -/
theorem
    correlation_cubicLayerOpenBox_abs_le_of_hermitianExplicitRatioSimpleParityWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (hwindow :
      cubicLayerHermitianExplicitRatio d R p <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight (cubicLayerGraph d R) p)
          (cubicLayerHermitianData d R p) (cubicLayerHermitianData d R p).maxEigenIndex)
    (hsimple : (cubicLayerHermitianData d R p).ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (Ambient.inducedGraph (latticeGraph (d + 1))
          (cubicLayerOpenBox d R (left + sep + right))) p
        (cubicLayerOpenBoxTwoPoint d R x left sep right)|
      ≤
        ((cubicLayerHermitianData d R p).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p)) /
          (cubicLayerHermitianData d R p).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (cubicLayerHermitianData d R p).maxEigenIndex
            (cubicLayerHermitianExplicitRatio d R p)) *
          cubicLayerHermitianExplicitRatio d R p ^ sep := by
  rw [cubicLayerOpenBoxTwoPoint,
    abs_correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab]
  exact correlation_layerOpenSlabGraph_abs_le_of_hermitianExplicitRatioSimpleParityWindow
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp x
    (cubicLayerTransitionWeight_symm d R p) hwindow hsimple left sep right hsep

end TransferMatrix

end IsingModel
