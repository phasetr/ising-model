import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay.Numerator
import IsingModel.TransferMatrix.LayerOpenSlabGraph
import IsingModel.TransferMatrix.LayerOpenSpectral
import IsingModel.TransferMatrix.LayerOpenSpectralDenominator

/-!
# Finite open layer-slab two-marked spectral decay: min-gap certificate and correlation

This is the certificate child of
`IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay`.  It packages the
open two-marked min-gap certificate, the normalised two-point decay bound, the
certificate constructor from orthogonal boundary-dominance bounds, and the
project-level cross-transverse-site correlation equate lemma and decay theorem.

See the umbrella module `LayerOpenTwoMarkedSpectralDecay` for the overview and
references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Two-marked open certificate -/

/-- A finite open-boundary two-marked min-gap certificate.  It is the two-mark
analogue of `LayerOpenMinSpectralGapCertificate`: the partition lower bound is
mark-agnostic, while the numerator estimate now carries two distinct marks `f`
(left cut) and `g` (right cut). -/
structure LayerOpenTwoMarkedMinSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ) where
  /-- The reference exponential scale. -/
  scale : ℝ
  /-- The decay rate. -/
  theta : ℝ
  /-- Numerator prefactor. -/
  prefactor : ℝ
  /-- Denominator prefactor. -/
  partitionPrefactor : ℝ
  /-- Positivity of the reference scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the decay rate. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict contraction of the decay rate. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the denominator prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Uniform lower bound on the open partition sum. -/
  partition_lower :
    ∀ {n : ℕ}, partitionPrefactor * scale ^ n ≤ layerOpenTransferPartition u k n
  /-- Uniform two-insertion numerator estimate with open boundary buffers. -/
  marked_abs_le :
    ∀ left sep right : ℕ,
      |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep

/-- The normalised open finite layer two-marked two-point function. -/
noncomputable def layerOpenTwoMarkedTwoPoint
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right
    / layerOpenPartition u k (left + sep + right)

omit [DecidableEq Ω] in
/-- A finite open-boundary two-marked min-gap certificate gives the normalised
open two-marked two-point decay bound. -/
theorem layerOpenTwoMarkedTwoPoint_abs_le_of_cert
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f g : Ω → ℝ}
    (cert : LayerOpenTwoMarkedMinSpectralGapCertificate u k f g)
    (left sep right : ℕ) :
    |layerOpenTwoMarkedTwoPoint u k f g left sep right| ≤
      (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ sep := by
  let n := left + sep + right
  have hscaleN : 0 < cert.scale ^ n := pow_pos cert.scale_pos n
  have hθ : 0 ≤ cert.theta ^ sep := pow_nonneg cert.theta_nonneg sep
  have hlower_pos : 0 < cert.partitionPrefactor * cert.scale ^ n :=
    mul_pos cert.partitionPrefactor_pos hscaleN
  have hden_lower : cert.partitionPrefactor * cert.scale ^ n
      ≤ layerOpenPartition u k n := by
    rw [layerOpenPartition_eq_transfer]
    exact cert.partition_lower
  have hden_pos : 0 < layerOpenPartition u k n :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked :
      |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
        ≤ cert.prefactor * cert.scale ^ n * cert.theta ^ sep :=
    cert.marked_abs_le left sep right
  rw [layerOpenTwoMarkedTwoPoint, abs_div, abs_of_pos hden_pos]
  calc
    |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
        / layerOpenPartition u k n
        = |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
          * (layerOpenPartition u k n)⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (cert.prefactor * cert.scale ^ n * cert.theta ^ sep)
          * (cert.partitionPrefactor * cert.scale ^ n)⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg cert.prefactor_nonneg hscaleN.le) hθ)
    _ = (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ sep := by
            field_simp [(ne_of_gt cert.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- Constructor for an open two-marked min-gap certificate from boundary-vector
orthogonal spectral numerator bounds and the matching spectral denominator
lower bound.  The denominator infrastructure is shared with the single-mark
route; only the two-marked numerator estimate is specific. -/
noncomputable def
    layerOpenTwoMarkedMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
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
        E.markedMatrix g top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenTwoMarkedMinSpectralGapCertificate u k f g where
  scale := scale
  theta := theta
  prefactor :=
    E.boundaryTwoMarkedSpectralPrefactor f g
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
  partitionPrefactor :=
    E.boundarySpectralPartitionPrefactor (layerOpenBalancedBoundaryVector u) top theta
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg :=
    E.boundaryTwoMarkedSpectralPrefactor_nonneg f g
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := fun {n} => by
    rw [layerOpenTransferPartition_eq_matrixPartition]
    exact layerOpenMatrixPartition_lower_of_orthogonalBoundaryDominantBounds
      u k hu E top scale theta scale_pos theta_nonneg (le_of_lt theta_lt_one)
      dominant_eigenvalue subdominant_abs_le n
  marked_abs_le := fun left sep right => by
    rw [← layerOpenTwoMarkedMatrixProductNumerator_eq_transferTwoPointNumerator
      u k f g left sep right]
    exact layerOpenTwoMarkedMatrixProductNumerator_abs_le_boundaryTwoMarkedSpectralPrefactor
      u k f g hu E top scale theta scale_pos theta_nonneg
      (E.eigenvalue_abs_le_scale_of_dominant_bounds top scale theta scale_pos
        (le_of_lt theta_lt_one) dominant_eigenvalue subdominant_abs_le)
      subdominant_abs_le central_dominant_channel_zero left sep right

/-! ## Cross-transverse-site correlation equate lemma -/

/-- The normalised cross-transverse-site two-point function on the concrete open
layer slab.  The first mark is `layerSpinAt x` (left endpoint) and the second is
`layerSpinAt y` (right endpoint). -/
noncomputable def layerOpenSlabSpinTwoMarkedTwoPoint {S : Type*}
    [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x y : S) (left sep right : ℕ) : ℝ :=
  layerOpenTwoMarkedTwoPoint u k (layerSpinAt x) (layerSpinAt y) left sep right

/-- The project-level cross-transverse-site two-point correlation on the finite
open-slab graph is the concrete open layer two-marked two-point function.  The
two sites `(left, x)` and `(left+sep, y)` are distinct because their layer
coordinates differ when `0 < sep`, so the genuine two-element observable expands
to the product of the two spin signs. -/
theorem correlation_layerOpenSlabGraph_two_transverse_eq_layerOpenSlabSpinTwoMarkedTwoPoint
    {S : Type*} [DecidableEq S] [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) (x y : S) (left sep right : ℕ) (hsep : 0 < sep) :
    correlation (layerOpenSlabGraph (S := S) H E (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) y} :
            Finset (LayerOpenSlabSite (left + sep + right) S)) =
      layerOpenSlabSpinTwoMarkedTwoPoint
        (layerInternalWeight H p) (layerTransitionWeight E p) x y
        left sep right := by
  let n := left + sep + right
  have hsite :
      (Prod.mk (layerOpenLeftIndex left sep right) x :
          LayerOpenSlabSite n S) ≠
        Prod.mk (layerOpenRightIndex left sep right) y := by
    intro h
    have hv := congr_arg (fun ix : LayerOpenSlabSite n S => ix.1.val) h
    simp [layerOpenLeftIndex, layerOpenRightIndex] at hv
    omega
  unfold correlation gibbsExpectation
  rw [partitionFunction_layerOpenSlabGraph_eq_isingLayerOpenSlabPartition
    (S := S) H E p]
  unfold isingLayerOpenSlabPartition
  have hsum :
      (∑ σ : Config (LayerOpenSlabSite n S),
          spinProduct
              ({Prod.mk (layerOpenLeftIndex left sep right) x,
                Prod.mk (layerOpenRightIndex left sep right) y} :
                Finset (LayerOpenSlabSite n S)) σ *
            boltzmannWeight (layerOpenSlabGraph (S := S) H E n) p σ)
        =
        ∑ σ : Config (LayerOpenSlabSite n S),
          Spin.sign ℝ (σ (layerOpenLeftIndex left sep right, x))
            * Spin.sign ℝ (σ (layerOpenRightIndex left sep right, y))
            * layerOpenStackWeight
              (layerInternalWeight H p) (layerTransitionWeight E p)
              ((layerOpenSlabConfigEquiv (S := S) n) σ) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [boltzmannWeight_layerOpenSlabGraph_eq_layerOpenStackWeight
      (S := S) H E p σ]
    simp [spinProduct, Spin.sign, hsite, mul_assoc]
  rw [hsum]
  unfold layerOpenSlabSpinTwoMarkedTwoPoint layerOpenTwoMarkedTwoPoint
    layerOpenTwoMarkedTransferTwoPointNumerator layerSpinAt
  rw [div_eq_mul_inv,
    mul_comm (∑ c : Fin (n + 1) → LayerState S,
      Spin.sign ℝ (c (layerOpenLeftIndex left sep right) x) *
        Spin.sign ℝ (c (layerOpenRightIndex left sep right) y) *
        (layerInternalWeight H p (c 0) *
          pathWeight (layerTransferMatrix (layerInternalWeight H p)
            (layerTransitionWeight E p)) c))]
  congr 1
  refine Fintype.sum_equiv (layerOpenSlabConfigEquiv (S := S) n)
    (fun σ : Config (LayerOpenSlabSite n S) =>
      Spin.sign ℝ (σ (layerOpenLeftIndex left sep right, x)) *
        Spin.sign ℝ (σ (layerOpenRightIndex left sep right, y)) *
        layerOpenStackWeight (layerInternalWeight H p) (layerTransitionWeight E p)
          ((layerOpenSlabConfigEquiv (S := S) n) σ))
    (fun c : Fin (n + 1) → LayerState S =>
      Spin.sign ℝ (c (layerOpenLeftIndex left sep right) x) *
        Spin.sign ℝ (c (layerOpenRightIndex left sep right) y) *
        (layerInternalWeight H p (c 0) *
          pathWeight (layerTransferMatrix (layerInternalWeight H p)
            (layerTransitionWeight E p)) c))
    (fun _ => rfl)

/-! ## Cross-transverse-site general-layer decay theorem -/

/-- Orthogonal boundary-dominance hypotheses give project-level finite open-slab
*cross*-transverse-site correlation decay, with the denominator lower bound
discharged by the spectral denominator bridge.  This is the two-mark analogue of
`correlation_layerOpenSlabGraph_same_transverse_abs_le_of_boundarySpectralDenominator`;
the same-site case is the `x = y` specialisation. -/
theorem
    correlation_layerOpenSlabGraph_two_transverse_abs_le_of_boundarySpectralDenominator
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x y : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos :
      0 < spec.boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta)
    (dominant_eigenvalue : spec.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt y) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) y} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryTwoMarkedSpectralPrefactor (layerSpinAt x) (layerSpinAt y)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta) *
          theta ^ sep := by
  let cert :
      LayerOpenTwoMarkedMinSpectralGapCertificate
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerSpinAt x) (layerSpinAt y) :=
    layerOpenTwoMarkedMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) (layerSpinAt y) (fun _ => Real.exp_pos _) spec top scale theta
      scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
      dominant_eigenvalue subdominant_abs_le central_dominant_channel_zero
  rw [correlation_layerOpenSlabGraph_two_transverse_eq_layerOpenSlabSpinTwoMarkedTwoPoint
    (S := S) H transitionPairs p x y left sep right hsep]
  exact layerOpenTwoMarkedTwoPoint_abs_le_of_cert cert left sep right

end TransferMatrix

end IsingModel
