import IsingModel.TransferMatrix.LayerSpectral.FlipParity

/-!
# Spectral-gap certificates (GJ §17.1)

Finite spectral-gap certificates (`LayerSpectralGapCertificate`) packaging a
positive scale, a subdominant ratio `theta < 1`, a partition-trace lower bound
and a marked-trace upper bound, together with the resulting two-point decay
bounds.  Part of the `LayerSpectral` finite spectral scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Spectral-gap certificates -/

/-- A finite spectral-gap certificate for a layer transfer matrix.

This is not a Perron--Frobenius theorem.  It packages the data that a later
spectral proof may provide: a positive scale `lambda`, a subdominant ratio
`theta < 1`, a lower bound on the partition trace, and an upper bound on the
marked two-insertion trace. -/
structure LayerSpectralGapCertificate
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
  /-- Lower bound on the cyclic partition trace. -/
  partition_lower : ∀ {N : ℕ}, 0 < N →
    partitionPrefactor * scale ^ N ≤ layerTransferPartitionTrace u k N
  /-- Exponential upper bound on the marked two-insertion trace. -/
  marked_abs_le : ∀ {a b : ℕ}, 0 < a → 0 < b →
    |layerTransferCorrelation_matrixElement u k f a b|
      ≤ prefactor * scale ^ (a + b) * theta ^ a

/-- The denominator in a spectral-gap certificate is positive. -/
theorem layerTransferPartitionTrace_pos_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f) {N : ℕ} (hN : 0 < N) :
    0 < layerTransferPartitionTrace u k N := by
  exact lt_of_lt_of_le (mul_pos h.partitionPrefactor_pos (pow_pos h.scale_pos N))
    (h.partition_lower hN)

/-- A finite spectral-gap certificate gives exponential decay of the normalised
cyclic layer two-point trace ratio in the marked separation `a`. -/
theorem layerTwoPoint_abs_le_of_spectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (h : LayerSpectralGapCertificate u k f)
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerTwoPoint u k f (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hN : 0 < a + b := Nat.add_pos_left ha b
  have hscaleN : 0 < h.scale ^ (a + b) := pow_pos h.scale_pos (a + b)
  have hθa : 0 ≤ h.theta ^ a := pow_nonneg h.theta_nonneg a
  have hlower_pos : 0 < h.partitionPrefactor * h.scale ^ (a + b) :=
    mul_pos h.partitionPrefactor_pos hscaleN
  have hden_lower := h.partition_lower hN
  have hden_pos : 0 < layerTransferPartitionTrace u k (a + b) :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked := h.marked_abs_le ha hb
  rw [layerTwoPoint_eq_trace_ratio, abs_div, abs_of_pos hden_pos]
  calc
    |layerTransferCorrelation_matrixElement u k f a b| /
        layerTransferPartitionTrace u k (a + b)
        = |layerTransferCorrelation_matrixElement u k f a b|
          * (layerTransferPartitionTrace u k (a + b))⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (h.prefactor * h.scale ^ (a + b) * h.theta ^ a)
          * (h.partitionPrefactor * h.scale ^ (a + b))⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg h.prefactor_nonneg hscaleN.le) hθa)
    _ = (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
            field_simp [(ne_of_gt h.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- Spin-observable wrapper for the spectral-gap certificate bound. -/
theorem layerSpinTwoPoint_abs_le_of_spectralGapCertificate
    {S : Type*} [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x : S)
    (h : LayerSpectralGapCertificate u k (layerSpinAt x))
    {a b : ℕ} [NeZero a] (hb : 0 < b) :
    |layerSpinTwoPoint u k x (a := a) (b := b) hb|
      ≤ (h.prefactor / h.partitionPrefactor) * h.theta ^ a := by
  exact layerTwoPoint_abs_le_of_spectralGapCertificate h hb


end TransferMatrix

end IsingModel
