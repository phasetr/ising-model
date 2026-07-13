import IsingModel.TransferMatrix.LayerSpectral.SpectralGap

/-!
# Balanced spectral-gap certificates (GJ §17.1)

Spectral-gap certificates stated on the balanced layer transfer matrix
(`LayerBalancedSpectralGapCertificate` and min-variants), their constructors
from trace bounds and orthogonal spectral data, and the induced two-point
decay bounds.  Part of the `LayerSpectral` finite spectral scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Balanced spectral-gap certificates -/

/-- A finite spectral-gap certificate stated on the balanced layer transfer
matrix.

This is the form expected from later symmetric spectral input for
`layerSymmetricTransferMatrix u k`.  The certificate is finite and algebraic:
it records bounds on the balanced partition trace and balanced marked trace,
but does not assert a Perron--Frobenius theorem or construct the bounds. -/
structure LayerBalancedSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the balanced cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N
  /-- Exponential upper bound on the balanced marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerSymmetricTransferCorrelationTrace u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- Transport a balanced trace certificate to the ordinary transfer-matrix
certificate using the diagonal similarity `T = D⁻¹ S D`. -/
def LayerBalancedSpectralGapCertificate.toLayerSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerBalancedSpectralGapCertificate u k f)
    (hu : ∀ a, 0 < u a) :
    LayerSpectralGapCertificate u k f := by
  refine
    { scale := h.scale
      theta := h.theta
      prefactor := h.prefactor
      partitionPrefactor := h.partitionPrefactor
      scale_pos := h.scale_pos
      theta_nonneg := h.theta_nonneg
      theta_lt_one := h.theta_lt_one
      prefactor_nonneg := h.prefactor_nonneg
      partitionPrefactor_pos := h.partitionPrefactor_pos
      partition_lower := ?_
      marked_abs_le := ?_ }
  · intro N hN
    rw [layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace u k hu]
    exact h.partition_lower hN
  · intro a b ha hb
    rw [layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
      u k f hu]
    exact h.marked_abs_le ha hb

/-- A balanced finite spectral-gap certificate with the two-arc cyclic
marked-trace estimate `theta ^ min a b`.

This is weaker than a one-sided separation estimate but requires only the
dominant-dominant marked channel to vanish.  It is the natural finite cyclic
bound before taking a thermodynamic limit or imposing an arc-ordering. -/
structure LayerBalancedMinSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
  /-- The positive dominant transfer scale. -/
  scale : ℝ
  /-- The nonnegative subdominant ratio. -/
  theta : ℝ
  /-- The numerator prefactor. -/
  prefactor : ℝ
  /-- The denominator prefactor in the partition lower bound. -/
  partitionPrefactor : ℝ
  /-- Positivity of the dominant transfer scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the subdominant ratio. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict spectral-gap ratio bound. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the partition prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Lower bound on the balanced cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N
  /-- Two-arc upper bound on the balanced marked two-insertion trace. -/
  marked_abs_le_min : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerSymmetricTransferCorrelationTrace u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ min a b

/-- Constructor for an ordinary spectral-gap certificate from explicit
transfer-trace bounds. -/
def layerSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerTransferCorrelation_matrixElement u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f where
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

/-- Constructor for a balanced spectral-gap certificate from explicit balanced
trace bounds. -/
def layerBalancedSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerBalancedSpectralGapCertificate u k f where
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

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit balanced trace bounds. -/
def layerBalancedMinSpectralGapCertificate_of_traceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le_min : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ min a b) :
    LayerBalancedMinSpectralGapCertificate u k f where
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
  marked_abs_le_min := marked_abs_le_min

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data and explicit spectral-basis bounds.

The hypotheses are deliberately stated as finite spectral-basis inequalities:
this does not assert Perron--Frobenius existence, identify a spectral radius, or
derive the one-sided cyclic marked-trace decay automatically. -/
def layerBalancedSpectralGapCertificate_of_orthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_spectral : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ ∑ i, E.eigenvalue i ^ N)
    (marked_abs_le_spectral : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerBalancedSpectralGapCertificate u k f := by
  refine
    layerBalancedSpectralGapCertificate_of_traceBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ ?_
  · intro N hN
    rw [layerSymmetricTransferPartitionTrace,
      RealOrthogonalSpectralData.trace_pow_eq_sum E N]
    exact partition_lower_spectral hN
  · intro a b ha hb
    rw [layerSymmetricTransferCorrelationTrace,
      RealOrthogonalSpectralData.marked_trace_eq_sum E f a b]
    exact marked_abs_le_spectral ha hb

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data, a chosen dominant spectral index, finite spectral
dominance, and one-sided marked-column cancellation.

This proves the partition and marked-trace bounds from component spectral
hypotheses.  It does not assert the existence of a Perron--Frobenius eigenvector,
identify the spectral radius, or derive the cancellation hypothesis from the
observable. -/
noncomputable def layerBalancedSpectralGapCertificate_of_orthogonalSpectralDominance
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (eigenvalue_nonnegative : ∀ i, 0 ≤ E.eigenvalue i)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0) :
    LayerBalancedSpectralGapCertificate u k f :=
  layerBalancedSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f) 1
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f) one_pos
    (fun hN => by
      simpa using
        RealOrthogonalSpectralData.partition_sum_lower_of_eigenvalue_nonnegative
          E top scale dominant_eigenvalue eigenvalue_nonnegative hN)
    (fun ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor
        E f top scale theta scale_pos theta_nonneg eigenvalue_abs_le_scale
        subdominant_abs_le dominant_markedColumn_zero ha)

/-- Constructor for a balanced spectral-gap certificate from explicit
orthogonal spectral data, a chosen dominant spectral index, a subdominant
absolute spectral bound, and one-sided marked-column cancellation.

The partition prefactor is the finite-cardinality bound
`1 - (Fintype.card Ω - 1) * theta`, so this constructor also assumes that this
quantity is positive.  This remains a conditional finite spectral-basis bound:
it does not prove Perron--Frobenius existence, spectral-radius maximality, or
the cancellation hypothesis. -/
noncomputable def layerBalancedSpectralGapCertificate_of_orthogonalDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0) :
    LayerBalancedSpectralGapCertificate u k f :=
  layerBalancedSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f)
    (finiteSpectralPartitionPrefactor Ω theta)
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f)
    (finiteSpectralPartitionPrefactor_pos Ω partitionPrefactor_small)
    (fun hN =>
      RealOrthogonalSpectralData.partition_lower_of_dominant_bounds
        E top scale theta scale_pos theta_nonneg theta_lt_one.le
        dominant_eigenvalue subdominant_abs_le hN)
    (fun ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor
        E f top scale theta scale_pos theta_nonneg
        (RealOrthogonalSpectralData.eigenvalue_abs_le_scale_of_dominant_bounds
          E top scale theta scale_pos theta_lt_one.le dominant_eigenvalue
          subdominant_abs_le)
        subdominant_abs_le dominant_markedColumn_zero ha)

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit orthogonal spectral data and explicit spectral-basis bounds. -/
def layerBalancedMinSpectralGapCertificate_of_orthogonalSpectralData
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_spectral : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ ∑ i, E.eigenvalue i ^ N)
    (marked_abs_le_min_spectral : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        ≤ prefactor * scale ^ (a + b) * theta ^ min a b) :
    LayerBalancedMinSpectralGapCertificate u k f := by
  refine
    layerBalancedMinSpectralGapCertificate_of_traceBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ ?_
  · intro N hN
    rw [layerSymmetricTransferPartitionTrace,
      RealOrthogonalSpectralData.trace_pow_eq_sum E N]
    exact partition_lower_spectral hN
  · intro a b ha hb
    rw [layerSymmetricTransferCorrelationTrace,
      RealOrthogonalSpectralData.marked_trace_eq_sum E f a b]
    exact marked_abs_le_min_spectral ha hb

/-- Constructor for a balanced min-separation spectral-gap certificate from
explicit orthogonal spectral data, a chosen dominant spectral index, a
subdominant absolute spectral bound, and dominant-dominant marked-channel
cancellation. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalSpectralData u k f E
    scale theta (E.markedSpectralPrefactor f)
    (finiteSpectralPartitionPrefactor Ω theta)
    scale_pos theta_nonneg theta_lt_one
    (E.markedSpectralPrefactor_nonneg f)
    (finiteSpectralPartitionPrefactor_pos Ω partitionPrefactor_small)
    (fun hN =>
      RealOrthogonalSpectralData.partition_lower_of_dominant_bounds
        E top scale theta scale_pos theta_nonneg theta_lt_one.le
        dominant_eigenvalue subdominant_abs_le hN)
    (fun _ha _hb =>
      RealOrthogonalSpectralData.marked_sum_abs_le_spectralPrefactor_min
        E f top scale theta scale_pos theta_nonneg theta_lt_one.le
        (RealOrthogonalSpectralData.eigenvalue_abs_le_scale_of_dominant_bounds
          E top scale theta scale_pos theta_lt_one.le dominant_eigenvalue
          subdominant_abs_le)
        subdominant_abs_le dominant_markedDiagonal_zero)

/-- Spin-observable constructor for a balanced min-separation spectral-gap
certificate from explicit orthogonal spectral data.  It replaces the
dominant-diagonal marked-channel cancellation hypothesis by flip-evenness of
the chosen dominant spectral column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_vector_flip_even : ∀ ω : LayerState S,
      E.changeOfBasis (layerStateFlipEquiv S ω) top = E.changeOfBasis ω top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds
    u k (layerSpinAt x) E top scale theta scale_pos theta_nonneg theta_lt_one
    partitionPrefactor_small dominant_eigenvalue subdominant_abs_le
    (E.markedMatrix_layerSpinAt_diagonal_zero_of_flip_even x top
      dominant_vector_flip_even)

/-- Constructor for a balanced min-separation spectral-gap certificate using
the Hermitian spectral theorem data attached to the balanced transfer matrix. -/
noncomputable def layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hk : ∀ a b, k a b = k b a)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_markedDiagonal_zero :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).markedMatrix f top top = 0) :
    LayerBalancedMinSpectralGapCertificate u k f :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds u k f
    (layerSymmetricTransferOrthogonalSpectralData u k hk) top scale theta
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_markedDiagonal_zero

/-- Spin-observable constructor for a balanced min-separation spectral-gap
certificate using the Hermitian spectral theorem data attached to the balanced
transfer matrix.  The marked-channel cancellation is supplied by flip-evenness
of the chosen dominant spectral column. -/
noncomputable def
    layerBalancedMinSpectralGapCertificate_of_layerHermitianDominantBounds_flipEvenSpin
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hk : ∀ a b, k a b = k b a)
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_small :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (dominant_eigenvalue :
      (layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk).eigenvalue i|
        ≤ theta * scale)
    (dominant_vector_flip_even : ∀ ω : LayerState S,
      (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis
          (layerStateFlipEquiv S ω) top =
        (layerSymmetricTransferOrthogonalSpectralData u k hk).changeOfBasis
          ω top) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) :=
  layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x (layerSymmetricTransferOrthogonalSpectralData u k hk) top scale theta
    scale_pos theta_nonneg theta_lt_one partitionPrefactor_small
    dominant_eigenvalue subdominant_abs_le dominant_vector_flip_even

/-- Constructor for an ordinary spectral-gap certificate from explicit balanced
trace bounds, transported across the diagonal similarity. -/
def layerSpectralGapCertificate_of_balancedTraceBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {N : ℕ}, 0 < N →
      partitionPrefactor * scale ^ N ≤ layerSymmetricTransferPartitionTrace u k N)
    (marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
      |layerSymmetricTransferCorrelationTrace u k f a b|
        ≤ prefactor * scale ^ (a + b) * theta ^ a) :
    LayerSpectralGapCertificate u k f :=
  (layerBalancedSpectralGapCertificate_of_traceBounds u k f scale theta prefactor
    partitionPrefactor scale_pos theta_nonneg theta_lt_one prefactor_nonneg
    partitionPrefactor_pos partition_lower marked_abs_le).toLayerSpectralGapCertificate hu

/-- A balanced finite spectral-gap certificate gives exponential decay of the
normalised cyclic layer two-point trace ratio. -/
theorem layerTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerTwoPoint_abs_le_of_spectralGapCertificate
        (h.toLayerSpectralGapCertificate hu) hb)

/-- Spin-observable wrapper for the balanced spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_balancedSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a :=
  by
    simpa using
      (layerSpinTwoPoint_abs_le_of_spectralGapCertificate u k x
        (h.toLayerSpectralGapCertificate hu) hb)

/-- A balanced min-separation spectral-gap certificate gives the two-arc cyclic
decay bound for the normalised layer two-point trace ratio. -/
theorem layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hN : 0 < a + b := Nat.add_pos_left ha b
  have hscaleN : 0 < h.scale ^ (a + b) := pow_pos h.scale_pos (a + b)
  have hθmin : 0 ≤ h.theta ^ min a b := pow_nonneg h.theta_nonneg _
  have hlower_pos : 0 < h.partitionPrefactor * h.scale ^ (a + b) :=
    mul_pos h.partitionPrefactor_pos hscaleN
  have hden_lower : h.partitionPrefactor * h.scale ^ (a + b)
      ≤ layerTransferPartitionTrace u k (a + b) := by
    rw [layerTransferPartitionTrace_eq_layerSymmetricTransferPartitionTrace u k hu]
    exact h.partition_lower hN
  have hden_pos : 0 < layerTransferPartitionTrace u k (a + b) :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked : |layerTransferCorrelation_matrixElement u k f a b|
      ≤ h.prefactor * h.scale ^ (a + b) * h.theta ^ min a b := by
    rw [layerTransferCorrelation_matrixElement_eq_layerSymmetricTransferCorrelationTrace
      u k f hu]
    exact h.marked_abs_le_min ha hb
  rw [layerTwoPoint_eq_trace_ratio, abs_div, abs_of_pos hden_pos]
  calc
    |layerTransferCorrelation_matrixElement u k f a b| /
        layerTransferPartitionTrace u k (a + b)
        = |layerTransferCorrelation_matrixElement u k f a b|
          * (layerTransferPartitionTrace u k (a + b))⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (h.prefactor * h.scale ^ (a + b) * h.theta ^ min a b)
          * (h.partitionPrefactor * h.scale ^ (a + b))⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg h.prefactor_nonneg hscaleN.le) hθmin)
    _ = (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b := by
            field_simp [(ne_of_gt h.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- If the marked separation is no longer than the complementary arc, the
two-arc min-separation bound becomes the usual one-sided separation bound. -/
theorem layerTwoPoint_abs_le_left_of_balancedMinSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) (hab : a ≤ b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  simpa [Nat.min_eq_left hab] using
    (layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
      (u := u) (k := k) (f := f) hu h (a := a) (b := b) hb)

/-- Spin-observable wrapper for the balanced min-separation certificate bound. -/
theorem layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (hu : ∀ a, 0 < u a)
    (h : LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ min a b :=
  by
    simpa using
      (layerTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate
        (u := u) (k := k) (f := layerSpinAt x) hu h (a := a) (b := b) hb)


end TransferMatrix

end IsingModel
