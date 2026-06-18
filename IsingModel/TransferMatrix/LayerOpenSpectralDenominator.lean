import IsingModel.TransferMatrix.LayerOpenSpectral

/-!
# Open-boundary spectral denominator bridge

This file supplies the denominator lower bound required by the open-boundary
spectral certificate constructor from explicit orthogonal spectral data.  It
keeps the Perron--Frobenius and positivity inputs conditional: the caller
provides the dominant channel, the subdominant absolute bound, and positivity
of the resulting boundary prefactor.

The results are finite and conditional.  They do not prove a physical
interacting spectral window, a Perron--Frobenius theorem, a thermodynamic limit,
or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Open denominator in boundary-vector spectral form -/

/-- The open matrix partition is the constant-one marked matrix-product
numerator with all separation placed in the left block. -/
theorem layerOpenMatrixPartition_eq_matrixProductOne
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenMatrixPartition u k n =
      layerOpenTwoPointMatrixProductNumerator u k (fun _ => (1 : ℝ)) n 0 0 := by
  unfold layerOpenMatrixPartition layerOpenTwoPointMatrixProductNumerator
  simp

/-- The open matrix partition is the balanced boundary-vector power product for
the symmetric transfer matrix. -/
theorem layerOpenMatrixPartition_eq_balancedBoundaryPower
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a) (n : ℕ) :
    layerOpenMatrixPartition u k n =
      RealOrthogonalSpectralData.boundaryPowerProduct
        (layerSymmetricTransferMatrix u k)
        (layerOpenBalancedBoundaryVector u)
        (layerOpenBalancedBoundaryVector u) n := by
  rw [layerOpenMatrixPartition_eq_matrixProductOne]
  rw [layerOpenTwoPointMatrixProductNumerator_eq_balancedBoundaryMarkedProduct
    u k (fun _ => (1 : ℝ)) hu n 0 0]
  rfl

/-- The open matrix partition in explicit boundary-vector spectral
coordinates. -/
theorem layerOpenMatrixPartition_eq_boundarySpectralSum
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (n : ℕ) :
    layerOpenMatrixPartition u k n =
      ∑ i,
        (E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i) ^ 2 *
          E.eigenvalue i ^ n := by
  rw [layerOpenMatrixPartition_eq_balancedBoundaryPower u k hu n]
  rw [E.boundaryPowerProduct_eq_spectralSum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Boundary-vector orthogonal spectral dominance gives the denominator lower
bound for the finite open matrix partition. -/
theorem layerOpenMatrixPartition_lower_of_orthogonalBoundaryDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (n : ℕ) :
    E.boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector u) top theta * scale ^ n ≤
      layerOpenMatrixPartition u k n := by
  rw [layerOpenMatrixPartition_eq_boundarySpectralSum u k hu E n]
  exact E.boundary_partition_lower_of_dominant_bounds
    (layerOpenBalancedBoundaryVector u) top scale theta scale_pos theta_nonneg
    theta_le_one dominant_eigenvalue subdominant_abs_le n

/-! ## Certificate constructor -/

/-- Constructor for an open min-gap certificate from boundary-vector orthogonal
spectral numerator bounds and the matching spectral denominator lower bound. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos :
      0 < E.boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector u) top theta)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix f top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinSpectralGapCertificate_of_matrixPartition_orthogonalBoundaryDominantBounds
    u k f hu E top scale theta
    (E.boundarySpectralPartitionPrefactor
      (layerOpenBalancedBoundaryVector u) top theta)
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
    (fun {n} =>
      layerOpenMatrixPartition_lower_of_orthogonalBoundaryDominantBounds
        u k hu E top scale theta scale_pos theta_nonneg
        (le_of_lt theta_lt_one) dominant_eigenvalue subdominant_abs_le n)
    (E.eigenvalue_abs_le_scale_of_dominant_bounds top scale theta scale_pos
      (le_of_lt theta_lt_one) dominant_eigenvalue subdominant_abs_le)
    subdominant_abs_le central_dominant_channel_zero

end TransferMatrix

end IsingModel
