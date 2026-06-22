import IsingModel.TransferMatrix.LayerPerronSpinDecay
import IsingModel.TransferMatrix.LayerQuadraticFormGap
import IsingModel.TransferMatrix.LayerQuadraticFormDeflation

/-!
# Quantitative Perron–Frobenius finite-volume spin two-point decay (GJ §17.1)

The Perron–Frobenius finite-volume spin two-point decay (`layerSpinTwoPoint_abs_le_perron`) is
stated with the *opaque* subdominant ratio
`RealOrthogonalSpectralData.subdominantRatio_maxEigenIndex`, an
existential `Classical.choose` witness that only satisfies `θ < 1`. That witness cannot consume the
**quantitative** high-temperature gap estimates, which all bound the *explicit* maximum ratio
`subdominantAbsRatio_maxEigenIndex` (the finite maximum of `|λ_i|/λ_top` over the non-dominant
spectral indices).

This file bridges the two. The balanced certificate constructor accepts an arbitrary `θ` together
with a per-eigenvalue bound `∀ i ≠ top, |λ_i| ≤ θ·λ_top`, so the entire Perron–Frobenius
spectral-gap decay can be re-expressed with **any** quantitative subdominant bound `θ`:

* `layerSpinPerronGapCertificate` / `layerSpinTwoPoint_abs_le_perron_of_eigenvalue_abs_le` — the
  generic quantitative form: supply any `θ` with `(card − 1)·θ < 1` bounding every non-dominant
  eigenvalue, and obtain geometric decay at rate `θ`. Every high-temperature route below factors
  through this.
* `layerSpinPerronExplicitRatioCertificate` / `layerSpinTwoPoint_abs_le_perron_explicitRatio` — the
  decay stated with the explicit ratio `subdominantAbsRatio_maxEigenIndex`, the canonical
  quantitatively-boundable rate.
* `layerSpinPerronQuadraticFormGapCertificate` /
  `layerSpinTwoPoint_abs_le_perron_of_quadraticForm_gap` — discharge the rate from a quadratic-form
  gap `|⟨v, Mv⟩| ≤ θ·λ_top·‖v‖²` on the top-orthogonal subspace.
* `layerSpinPerronTopDeflatedGershgorinCertificate` /
  `layerSpinTwoPoint_abs_le_perron_of_topDeflatedGershgorin` — discharge the rate from the
  top-deflated Gershgorin envelope `maxAbsDiag(M_def) + offMass(M_def) ≤ θ·λ_top`, the
  circularity-free high-temperature mechanism of GJ §17.1.

All spectral inputs (dominant column, strict gap, flip-even marked-channel cancellation) remain
discharged by Perron–Frobenius; only the now-quantitative rate `θ` and the finite prefactor
smallness `(card(LayerState S) − 1)·θ < 1` are explicit.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The generic quantitative Perron–Frobenius spin certificate** (GJ §17.1): for an
entrywise-positive, symmetric, globally-spin-flip-invariant balanced layer transfer kernel, any rate
`θ ∈ [0, 1)` that bounds every non-dominant eigenvalue in absolute value, `|λ_i| ≤ θ·λ_top`, and
satisfies the finite prefactor smallness `(card(LayerState S) − 1)·θ < 1` yields the balanced
min-separation spectral-gap certificate for the layer spin observable. The dominant column,
positivity of `λ_top`, and the flip-even marked-channel cancellation are supplied by
Perron–Frobenius. -/
noncomputable def layerSpinPerronGapCertificate
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hbound : ∀ i,
        i ≠ (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  set E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm with hE
  have hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  have hpos := E.signedPositiveColumn_maxEigenIndex hM
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E E.maxEigenIndex (E.eigenvalue E.maxEigenIndex) theta
    (E.eigenvalue_pos_of_signedPositiveColumn hM E.maxEigenIndex hpos)
    htheta_nonneg htheta_lt_one hprefactor rfl hbound
    (layerSymmetricTransfer_signedPositiveColumn_flip_even
      u k hu hk_pos hu_flip hk_flip E E.maxEigenIndex hpos)

/-- **The generic quantitative Perron–Frobenius spin two-point decay** (GJ §17.1): under the
hypotheses of `layerSpinPerronGapCertificate`, the layer spin two-point function decays
geometrically at the supplied rate `θ` in the marked separation `min a b`. -/
theorem layerSpinTwoPoint_abs_le_perron_of_eigenvalue_abs_le
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hbound : ∀ i,
        i ≠ (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex →
      |(layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue i|
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    let c := layerSpinPerronGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hbound
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (c.prefactor / c.partitionPrefactor) * c.theta ^ min a b :=
  layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate u k x hu
    (layerSpinPerronGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hbound) hb

/-- **The explicit-ratio Perron–Frobenius spin certificate** (GJ §17.1): the balanced certificate
with rate the explicit subdominant absolute ratio `subdominantAbsRatio_maxEigenIndex`. The
per-eigenvalue bound is the defining property of that ratio; only the finite prefactor smallness
`(card(LayerState S) − 1)·θ < 1` (with `θ` the explicit ratio) remains explicit. -/
noncomputable def layerSpinPerronExplicitRatioCertificate
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hprefactor :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).subdominantAbsRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  set E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm with hE
  have hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  exact layerSpinPerronGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
    (E.subdominantAbsRatio_maxEigenIndex hM)
    (E.subdominantAbsRatio_maxEigenIndex_nonneg hM)
    (E.subdominantAbsRatio_maxEigenIndex_lt_one hM) hprefactor
    (fun i hi => E.eigenvalue_abs_le_subdominantAbsRatio_maxEigenIndex hM i hi)

/-- **The explicit-ratio Perron–Frobenius spin two-point decay** (GJ §17.1): geometric decay at the
explicit subdominant absolute ratio, the canonical quantitatively-boundable rate. -/
theorem layerSpinTwoPoint_abs_le_perron_explicitRatio
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hprefactor :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).subdominantAbsRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    let c := layerSpinPerronExplicitRatioCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      hprefactor
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (c.prefactor / c.partitionPrefactor) * c.theta ^ min a b :=
  layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate u k x hu
    (layerSpinPerronExplicitRatioCertificate u k x hu hk_pos hk_symm hu_flip hk_flip hprefactor) hb

/-- **The quadratic-form-gap Perron–Frobenius spin certificate** (GJ §17.1): the balanced
certificate with rate `θ` discharged from a quadratic-form gap `|⟨v, Mv⟩| ≤ θ·λ_top·‖v‖²` on the
subspace orthogonal to the dominant spectral column. The gap bounds the explicit subdominant ratio
by `θ`, hence every non-dominant eigenvalue by `θ·λ_top`. -/
noncomputable def layerSpinPerronQuadraticFormGapCertificate
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hgap : ∀ v : LayerState S → ℝ,
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).spectralCoord v
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex = 0 →
      |matrixQuadraticForm (layerSymmetricTransferMatrix u k) v|
        ≤ (theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
          * vectorSqNorm v) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  set E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm with hE
  have hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  have hpos := E.signedPositiveColumn_maxEigenIndex hM
  have hroute := E.subdominantAbsRatio_maxEigenIndex_le_of_quadraticForm_gap hM htheta_nonneg hgap
  refine layerSpinPerronGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
    theta htheta_nonneg htheta_lt_one hprefactor (fun i hi => ?_)
  calc |E.eigenvalue i|
      ≤ E.subdominantAbsRatio_maxEigenIndex hM * E.eigenvalue E.maxEigenIndex :=
        E.eigenvalue_abs_le_subdominantAbsRatio_maxEigenIndex hM i hi
    _ ≤ theta * E.eigenvalue E.maxEigenIndex :=
        mul_le_mul_of_nonneg_right hroute
          (E.eigenvalue_pos_of_signedPositiveColumn hM E.maxEigenIndex hpos).le

/-- **The quadratic-form-gap Perron–Frobenius spin two-point decay** (GJ §17.1): geometric decay at
rate `θ`, with `θ` discharged from a top-orthogonal quadratic-form gap. -/
theorem layerSpinTwoPoint_abs_le_perron_of_quadraticForm_gap
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hgap : ∀ v : LayerState S → ℝ,
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).spectralCoord v
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex = 0 →
      |matrixQuadraticForm (layerSymmetricTransferMatrix u k) v|
        ≤ (theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
          * vectorSqNorm v)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    let c := layerSpinPerronQuadraticFormGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hgap
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (c.prefactor / c.partitionPrefactor) * c.theta ^ min a b :=
  layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate u k x hu
    (layerSpinPerronQuadraticFormGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hgap) hb

/-- **The top-deflated-Gershgorin Perron–Frobenius spin certificate** (GJ §17.1): the balanced
certificate with rate `θ` discharged from the top-deflated Gershgorin envelope
`maxAbsDiag(M_def) + offMass(M_def) ≤ θ·λ_top`. Deflating the dominant eigenvalue breaks the
circularity, so this envelope can lie strictly below `λ_top` — the high-temperature mechanism. -/
noncomputable def layerSpinPerronTopDeflatedGershgorinCertificate
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hgersh :
      matrixMaxAbsDiag
            ((layerSymmetricTransferOrthogonalSpectralData u k hk_symm).matrixTopDeflation
              (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum
            ((layerSymmetricTransferOrthogonalSpectralData u k hk_symm).matrixTopDeflation
              (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  set E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm with hE
  have hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  have hpos := E.signedPositiveColumn_maxEigenIndex hM
  have hroute := E.subdominantAbsRatio_maxEigenIndex_le_of_topDeflatedGershgorin_le hM
    (layerSymmetricTransferMatrix_transpose u k hk_symm) htheta_nonneg hgersh
  refine layerSpinPerronGapCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
    theta htheta_nonneg htheta_lt_one hprefactor (fun i hi => ?_)
  calc |E.eigenvalue i|
      ≤ E.subdominantAbsRatio_maxEigenIndex hM * E.eigenvalue E.maxEigenIndex :=
        E.eigenvalue_abs_le_subdominantAbsRatio_maxEigenIndex hM i hi
    _ ≤ theta * E.eigenvalue E.maxEigenIndex :=
        mul_le_mul_of_nonneg_right hroute
          (E.eigenvalue_pos_of_signedPositiveColumn hM E.maxEigenIndex hpos).le

/-- **The top-deflated-Gershgorin Perron–Frobenius spin two-point decay** (GJ §17.1): geometric
decay at rate `θ`, with `θ` discharged from the circularity-free top-deflated Gershgorin
envelope. -/
theorem layerSpinTwoPoint_abs_le_perron_of_topDeflatedGershgorin
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_lt_one : theta < 1)
    (hprefactor : (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) * theta) < 1)
    (hgersh :
      matrixMaxAbsDiag
            ((layerSymmetricTransferOrthogonalSpectralData u k hk_symm).matrixTopDeflation
              (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
          + matrixMaxOffDiagAbsRowSum
            ((layerSymmetricTransferOrthogonalSpectralData u k hk_symm).matrixTopDeflation
              (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
        ≤ theta * (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).eigenvalue
            (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).maxEigenIndex)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    let c := layerSpinPerronTopDeflatedGershgorinCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hgersh
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (c.prefactor / c.partitionPrefactor) * c.theta ^ min a b :=
  layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate u k x hu
    (layerSpinPerronTopDeflatedGershgorinCertificate u k x hu hk_pos hk_symm hu_flip hk_flip
      theta htheta_nonneg htheta_lt_one hprefactor hgersh) hb

end TransferMatrix

end IsingModel
