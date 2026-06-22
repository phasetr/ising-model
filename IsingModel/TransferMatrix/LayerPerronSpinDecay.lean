import IsingModel.TransferMatrix.LayerPerronExistence
import IsingModel.TransferMatrix.LayerSpectral

/-!
# Perron–Frobenius finite-volume spin two-point decay (GJ §17.1)

The Perron–Frobenius theorem for the balanced layer transfer matrix is now available
unconditionally: the entrywise-positive symmetric transfer matrix has a signed-positive dominant
spectral column (`signedPositiveColumn_maxEigenIndex`), giving a strictly positive simple dominant
eigenvalue and a strict spectral gap (`subdominantRatio_maxEigenIndex_lt_one`). This file wires that
Perron–Frobenius input all the way through to the **finite-volume spin two-point decay**: under
global spin-flip invariance of the weights (the physical Ising symmetry, which discharges the
marked-channel cancellation via flip-even-ness of the Perron column), the only remaining
quantitative hypothesis is the finite prefactor smallness `(card(LayerState S) − 1)·θ < 1`, where
`θ` is the Perron subdominant ratio. Under that single condition the layer spin two-point function
decays geometrically, `|⟨σ_x σ_x⟩^{(a,b)}| ≤ C·θ^{min a b}`.

This is the unconditional (modulo the finite prefactor) finite-volume realization of the
transfer-matrix spectral-gap decay; the transverse-volume-uniform prefactor condition is the
remaining (separately tracked) input.

* `layerSpinPerronCertificate` — the balanced min-separation spectral-gap certificate for the layer
  spin observable, all spectral hypotheses from Perron–Frobenius, modulo `(card − 1)·θ < 1`.
* `layerSpinTwoPoint_abs_le_perron` — the resulting finite-volume spin two-point decay bound.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The Perron–Frobenius spin spectral-gap certificate** (GJ §17.1): for an entrywise-positive,
symmetric, globally-spin-flip-invariant balanced layer transfer kernel, the balanced min-separation
spectral-gap certificate for the layer spin observable `layerSpinAt x` is constructed with **every
spectral hypothesis discharged by Perron–Frobenius** — the dominant signed-positive column, the
strictly positive simple dominant eigenvalue, the strict gap `θ < 1`, and the flip-even
marked-channel cancellation. The only remaining quantitative input is the finite prefactor smallness
`(card(LayerState S) − 1)·θ < 1`. -/
noncomputable def layerSpinPerronCertificate
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hprefactor :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1) :
    LayerBalancedMinSpectralGapCertificate u k (layerSpinAt x) := by
  letI : Nonempty (LayerState S) := ⟨default⟩
  set E := layerSymmetricTransferOrthogonalSpectralData u k hk_symm with hE
  have hM := layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos
  have hpos := E.signedPositiveColumn_maxEigenIndex hM
  exact layerBalancedMinSpectralGapCertificate_of_orthogonalDominantBounds_flipEvenSpin
    u k x E E.maxEigenIndex (E.eigenvalue E.maxEigenIndex)
    (E.subdominantRatio_maxEigenIndex hM)
    (E.eigenvalue_pos_of_signedPositiveColumn hM E.maxEigenIndex hpos)
    (E.subdominantRatio_maxEigenIndex_nonneg hM)
    (E.subdominantRatio_maxEigenIndex_lt_one hM)
    hprefactor rfl
    (fun i hi => E.eigenvalue_abs_le_subdominantRatio_maxEigenIndex hM i hi)
    (layerSymmetricTransfer_signedPositiveColumn_flip_even
      u k hu hk_pos hu_flip hk_flip E E.maxEigenIndex hpos)

/-- **Perron–Frobenius finite-volume spin two-point decay** (GJ §17.1): for an entrywise-positive,
symmetric, globally-spin-flip-invariant balanced layer transfer kernel satisfying the finite
prefactor smallness `(card(LayerState S) − 1)·θ < 1` (with `θ` the Perron subdominant ratio), the
layer spin two-point function decays geometrically in the marked separation `min a b`. All spectral
inputs are discharged by Perron–Frobenius; only the prefactor smallness remains explicit. -/
theorem layerSpinTwoPoint_abs_le_perron
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ) (x : S)
    (hu : ∀ ω, 0 < u ω) (hk_pos : ∀ ω η, 0 < k ω η) (hk_symm : ∀ ω η, k ω η = k η ω)
    (hu_flip : ∀ ω, u (layerStateFlipEquiv S ω) = u ω)
    (hk_flip : ∀ ω η,
      k (layerStateFlipEquiv S ω) (layerStateFlipEquiv S η) = k ω η)
    (hprefactor :
      (((Fintype.card (LayerState S) - 1 : ℕ) : ℝ) *
        (layerSymmetricTransferOrthogonalSpectralData u k hk_symm).subdominantRatio_maxEigenIndex
          (layerSymmetricTransferMatrix_entrywisePositive u k hu hk_pos)) < 1)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    let c := layerSpinPerronCertificate u k x hu hk_pos hk_symm hu_flip hk_flip hprefactor
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (c.prefactor / c.partitionPrefactor) * c.theta ^ min a b :=
  layerSpinTwoPoint_abs_le_min_of_balancedMinSpectralGapCertificate u k x hu
    (layerSpinPerronCertificate u k x hu hk_pos hk_symm hu_flip hk_flip hprefactor) hb

end TransferMatrix

end IsingModel
