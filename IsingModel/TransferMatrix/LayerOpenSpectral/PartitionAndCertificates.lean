import IsingModel.TransferMatrix.LayerOpenSpectral.NumeratorIdentities
import IsingModel.TransferMatrix.LayerOpenSpectral.SpectralForm

/-!
# Open partition matrix form and min-gap certificate constructors

The boundary-vector matrix-power form of the open partition, together with the
open min-gap certificate constructors packaging finite denominator and numerator
estimates.

This is a build-speed split child of `LayerOpenSpectral`; see that umbrella
module for the mathematical overview and references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Boundary-vector matrix-power form -/

/-- The finite open partition written as the boundary-vector matrix-power sum
`∑ a b, u a * (T^n) a b`, where `T = layerTransferMatrix u k`. -/
def layerOpenMatrixPartition (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ a : Ω, ∑ b : Ω, u a * (layerTransferMatrix u k ^ n) a b

/-- The open transfer partition is the boundary-vector matrix-power sum. -/
theorem layerOpenTransferPartition_eq_matrixPartition
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenTransferPartition u k n = layerOpenMatrixPartition u k n := by
  unfold layerOpenTransferPartition layerOpenMatrixPartition
  calc
    ∑ c : Fin (n + 1) → Ω,
        u (c 0) * pathWeight (layerTransferMatrix u k) c
        =
        ∑ c : Fin (n + 1) → Ω, ∑ a : Ω, ∑ b : Ω,
          u a *
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_eq_single (c 0)]
          · rw [Finset.sum_eq_single (c (Fin.last n))]
            · simp
            · intro b _ hb
              simp [hb.symm]
            · intro h
              exact absurd (Finset.mem_univ (c (Fin.last n))) h
          · intro a _ ha
            simp [ha.symm]
          · intro h
            exact absurd (Finset.mem_univ (c 0)) h
    _ =
        ∑ a : Ω, ∑ b : Ω, ∑ c : Fin (n + 1) → Ω,
          u a *
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
        ∑ a : Ω, ∑ b : Ω,
          u a * ∑ c : Fin (n + 1) → Ω,
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
    _ =
        ∑ a : Ω, ∑ b : Ω, u a * (layerTransferMatrix u k ^ n) a b := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [pow_apply_eq_sum]

/-- The open Gibbs partition is the boundary-vector matrix-power sum. -/
theorem layerOpenPartition_eq_matrixPartition
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenPartition u k n = layerOpenMatrixPartition u k n := by
  rw [layerOpenPartition_eq_transfer, layerOpenTransferPartition_eq_matrixPartition]

/-! ## Certificate constructors -/

/-- Constructor for an open min-gap certificate from explicit open transfer
bounds.  This is the open-boundary analogue of the cyclic trace-bound
constructors: it packages already-proved finite open denominator and numerator
estimates into the certificate consumed by open slab correlation bounds. -/
def layerOpenMinSpectralGapCertificate_of_transferBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenTransferPartition u k n)
    (marked_abs_le : ∀ left sep right : ℕ,
      |layerOpenTransferTwoPointNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for an open min-gap certificate whose denominator estimate is
proved in boundary-vector matrix-power form.  The marked numerator remains the
open-path numerator used by `LayerOpenMinSpectralGapCertificate`; later spectral
files can refine that input by proving a matrix-power or spectral-basis formula
for the marked open path. -/
def layerOpenMinSpectralGapCertificate_of_matrixPartitionBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenMatrixPartition u k n)
    (marked_abs_le : ∀ left sep right : ℕ,
      |layerOpenTransferTwoPointNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f := by
  refine
    layerOpenMinSpectralGapCertificate_of_transferBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ marked_abs_le
  intro n
  rw [layerOpenTransferPartition_eq_matrixPartition]
  exact partition_lower_matrix

/-- Constructor for an open min-gap certificate whose denominator estimate is
proved in boundary-vector matrix-power form and whose marked numerator estimate
is proved in the expanded four-endpoint matrix-power form. -/
def layerOpenMinSpectralGapCertificate_of_matrixPartition_matrixPowerNumeratorBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenMatrixPartition u k n)
    (marked_abs_le_matrixPower : ∀ left sep right : ℕ,
      |layerOpenTwoPointMatrixPowerNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f := by
  refine
    layerOpenMinSpectralGapCertificate_of_matrixPartitionBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos partition_lower_matrix ?_
  intro left sep right
  rw [← layerOpenTwoPointMatrixPowerNumerator_eq_transferTwoPointNumerator
    u k f left sep right]
  exact marked_abs_le_matrixPower left sep right

/-- Constructor for an open min-gap certificate whose denominator estimate is
proved in boundary-vector matrix-power form and whose marked numerator estimate
is proved in boundary-vector matrix-product form. -/
def layerOpenMinSpectralGapCertificate_of_matrixPartition_matrixProductNumeratorBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenMatrixPartition u k n)
    (marked_abs_le_matrixProduct : ∀ left sep right : ℕ,
      |layerOpenTwoPointMatrixProductNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f := by
  refine
    layerOpenMinSpectralGapCertificate_of_matrixPartitionBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos partition_lower_matrix ?_
  intro left sep right
  rw [← layerOpenTwoPointMatrixProductNumerator_eq_transferTwoPointNumerator
    u k f left sep right]
  exact marked_abs_le_matrixProduct left sep right

/-- Constructor for an open min-gap certificate from boundary-vector orthogonal
spectral numerator bounds and a matrix-partition denominator lower bound. -/
noncomputable def
    layerOpenMinSpectralGapCertificate_of_matrixPartition_orthogonalBoundaryDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenMatrixPartition u k n)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix f top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenMinSpectralGapCertificate u k f :=
  layerOpenMinSpectralGapCertificate_of_matrixPartition_matrixProductNumeratorBounds
    u k f scale theta
    (E.boundaryMarkedSpectralPrefactor f
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u))
    partitionPrefactor scale_pos theta_nonneg theta_lt_one
    (E.boundaryMarkedSpectralPrefactor_nonneg f
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u))
    partitionPrefactor_pos partition_lower_matrix
    (fun left sep right =>
      layerOpenTwoPointMatrixProductNumerator_abs_le_boundarySpectralPrefactor
        u k f hu E top scale theta scale_pos theta_nonneg
        eigenvalue_abs_le_scale subdominant_abs_le
        central_dominant_channel_zero left sep right)

end TransferMatrix

end IsingModel
