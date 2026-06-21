import IsingModel.TransferMatrix.LayerQuadraticFormGap
import IsingModel.TransferMatrix.LayerQuadraticFormDeflation
import IsingModel.TransferMatrix.LayerQuadraticFormDeflationEntries

/-!
# Top-deflated Gershgorin spectral gap for the layer transfer matrix (GJ §17.1, P5)

The all-vector Gershgorin envelope `max|diag| + offMass` of the balanced layer transfer matrix
`M a b = √(u a)·k a b·√(u b)` is an *upper* bound on its spectral radius `= λ_max`, so it can never
give a subdominant ratio `θ < 1`: that route is circular (cf.
`LayerIdentityTransitionProjective`). The non-circular route deflates the maximal eigenpair first:
the **top-deflated** matrix `M − λ_max·w wᵀ` (with `w` the Perron column) has the maximal eigenvalue
removed, so *its* Gershgorin envelope can be strictly below `λ_max`. This file packages that route
for the arbitrary-finite-layer and cubic transfer matrices, mirroring the quadratic-form-gap
wrappers of `LayerQuadraticFormGap` but via the top-deflated Gershgorin reduction
(`subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le`).

The eventual transverse-volume-uniform high-temperature bound (the remaining P5 core math) will
discharge the deflated-Gershgorin hypothesis `maxAbsDiag(M_def) + offMass(M_def) ≤ θ·λ_max` with a
`θ(βJ) < 1` independent of the transverse box radius.

* `layerSymmetricTransferMatrix_transpose_self` — the balanced layer transfer matrix is symmetric.
* `finiteTransverseHermitianExplicitRatio_le_of_topDeflatedGershgorin` — finite-layer deflation gap.
* `cubicLayerHermitianExplicitRatio_le_of_topDeflatedGershgorin` — cubic specialization.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The balanced layer transfer matrix is symmetric**: `Mᵀ = M` when the transition weight `k` is
symmetric, since `M a b = √(u a)·k a b·√(u b)` is invariant under swapping `a` and `b`. This is the
symmetry input of the top-deflated Gershgorin gap (the real form of its Hermitian property). -/
theorem layerSymmetricTransferMatrix_transpose_self
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ a b, k a b = k b a) :
    (layerSymmetricTransferMatrix u k)ᵀ = layerSymmetricTransferMatrix u k := by
  ext a b
  simp only [Matrix.transpose_apply, layerSymmetricTransferMatrix]
  rw [hk b a]; ring

/-- **Explicit deflated entry of the balanced layer transfer matrix**: the top-deflation subtracts
`λ_top·w_i·w_j` (with `w` the Perron column) from the entry `√(u i)·k i j·√(u j)`. -/
theorem layerSymmetricTransfer_topDeflation_apply {u : Ω → ℝ} {k : Ω → Ω → ℝ}
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k)) (top i j : Ω) :
    E.matrixTopDeflation top i j =
      Real.sqrt (u i) * k i j * Real.sqrt (u j)
        - E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top) := by
  rw [E.matrixTopDeflation_apply]; rfl

/-- **Explicit deflated diagonal of the balanced layer transfer matrix**: `√(u i)·k i i·√(u i)`
minus the Perron-column contribution `λ_top·w_i²`. At high temperature the diagonal `√(u i)·k i i·
√(u i)` is close to `λ_top·w_i²`, making the deflated diagonal small — the mechanism behind the
uniform spectral gap. -/
theorem layerSymmetricTransfer_topDeflation_diag {u : Ω → ℝ} {k : Ω → Ω → ℝ}
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k)) (top i : Ω) :
    E.matrixTopDeflation top i i =
      Real.sqrt (u i) * k i i * Real.sqrt (u i)
        - E.eigenvalue top * (E.changeOfBasis i top) ^ 2 := by
  rw [E.matrixTopDeflation_diag]; rfl

/-- **Explicit deflated off-diagonal absolute row sum of the balanced layer transfer matrix**, in
terms of the layer weights and the Perron column. This is the quantity the uniform high-temperature
bound must control. -/
theorem layerSymmetricTransfer_topDeflation_offDiagAbsRowSum {u : Ω → ℝ} {k : Ω → Ω → ℝ}
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k)) (top i : Ω) :
    matrixOffDiagAbsRowSum (E.matrixTopDeflation top) i =
      ∑ j ∈ Finset.univ.erase i,
        |Real.sqrt (u i) * k i j * Real.sqrt (u j)
          - E.eigenvalue top * (E.changeOfBasis i top * E.changeOfBasis j top)| := by
  rw [E.matrixTopDeflation_offDiagAbsRowSum]
  rfl

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Finite-layer top-deflated Gershgorin gap**: the explicit subdominant ratio of the generic
Hermitian layer spectral data is at most `θ` whenever the top-deflated transfer matrix has
Gershgorin envelope at most `θ·λ_max`. Unlike the all-vector envelope, the deflated matrix has the
maximal eigenvalue removed, so this hypothesis is non-circular. -/
theorem finiteTransverseHermitianExplicitRatio_le_of_topDeflatedGershgorin
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ)
    (hk_symm : ∀ ω η,
      layerTransitionWeight transitionPairs p ω η =
        layerTransitionWeight transitionPairs p η ω)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hgersh :
      matrixMaxAbsDiag ((finiteTransverseHermitianData H transitionPairs p hk_symm).matrixTopDeflation
          (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum
            ((finiteTransverseHermitianData H transitionPairs p hk_symm).matrixTopDeflation
              (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex)
        ≤ theta * (finiteTransverseHermitianData H transitionPairs p hk_symm).eigenvalue
            (finiteTransverseHermitianData H transitionPairs p hk_symm).maxEigenIndex) :
    finiteTransverseHermitianExplicitRatio H transitionPairs p hk_symm ≤ theta :=
  (finiteTransverseHermitianData H transitionPairs p
    hk_symm).subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le
    (finiteTransverseHermitian_entrywisePositive H transitionPairs p)
    (layerSymmetricTransferMatrix_transpose_self _ _ hk_symm) htheta hgersh

/-- **Cubic specialization of the top-deflated Gershgorin gap**: the cubic explicit subdominant
ratio is at most `θ` from a top-deflated Gershgorin envelope of size `θ·λ_max`. The eventual
high-temperature, transverse-volume-uniform bound discharges this hypothesis. -/
theorem cubicLayerHermitianExplicitRatio_le_of_topDeflatedGershgorin
    (d R : ℕ) (p : IsingParams ℝ) {theta : ℝ} (htheta : 0 ≤ theta)
    (hgersh :
      matrixMaxAbsDiag ((cubicLayerHermitianData d R p).matrixTopDeflation
          (cubicLayerHermitianData d R p).maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum ((cubicLayerHermitianData d R p).matrixTopDeflation
            (cubicLayerHermitianData d R p).maxEigenIndex)
        ≤ theta * (cubicLayerHermitianData d R p).eigenvalue
            (cubicLayerHermitianData d R p).maxEigenIndex) :
    cubicLayerHermitianExplicitRatio d R p ≤ theta :=
  finiteTransverseHermitianExplicitRatio_le_of_topDeflatedGershgorin (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p) htheta hgersh

end TransferMatrix

end IsingModel
