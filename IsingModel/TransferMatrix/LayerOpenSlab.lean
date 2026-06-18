import IsingModel.TransferMatrix.LayerGibbs
import Mathlib.Tactic

/-!
# Finite open layer slabs (GJ Section 17.1)

This file records the free-boundary analogue of the cyclic layer Gibbs sums.
An open stack with `n + 1` layers has `n` transfer steps and no wrap-around edge.
The weight is the left boundary layer weight times the open path weight for the
same layer transfer matrix used in the periodic theory.

The file deliberately packages the open-boundary decay estimate as a finite
certificate input.  It does not prove a physical interacting spectral window,
an infinite-volume limit, or the final hyperplane decay estimate.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Open layer stacks -/

/-- The left endpoint index in an open layer path with
`left + sep + right` transfer steps. -/
def layerOpenLeftIndex (left sep right : ℕ) : Fin (left + sep + right + 1) :=
  ⟨left, by omega⟩

/-- The right marked index in an open layer path with
`left + sep + right` transfer steps. -/
def layerOpenRightIndex (left sep right : ℕ) : Fin (left + sep + right + 1) :=
  ⟨left + sep, by omega⟩

/-- The open layer-stack weight over `n` transfer steps.  The first factor is
the left endpoint one-layer weight; the remaining factors are the open path
weight of the layer transfer matrix `T a b = u b * k a b`. -/
def layerOpenStackWeight (u : Ω → ℝ) (k : Ω → Ω → ℝ) {n : ℕ}
    (c : Fin (n + 1) → Ω) : ℝ :=
  u (c 0) * pathWeight (layerTransferMatrix u k) c

omit [Fintype Ω] [DecidableEq Ω] in
/-- Product-expanded form of the open layer-stack weight. -/
theorem layerOpenStackWeight_eq_prod
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) {n : ℕ} (c : Fin (n + 1) → Ω) :
    layerOpenStackWeight u k c =
      u (c 0) * ∏ i : Fin n, u (c i.succ) * k (c i.castSucc) (c i.succ) := by
  rfl

/-- The open finite layer partition sum over `n + 1` layers. -/
def layerOpenPartition (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ c : Fin (n + 1) → Ω, layerOpenStackWeight u k c

/-- The same open finite layer partition, named as a transfer-matrix open-path
sum to make the boundary condition explicit. -/
def layerOpenTransferPartition (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ c : Fin (n + 1) → Ω, u (c 0) * pathWeight (layerTransferMatrix u k) c

omit [DecidableEq Ω] in
/-- The open partition sum is the transfer-matrix open-path sum. -/
theorem layerOpenPartition_eq_transfer
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenPartition u k n = layerOpenTransferPartition u k n := by
  rfl

/-! ## Two marked layers -/

/-- The open stack weight with two insertions separated by `sep` transfer steps,
with `left` transfer steps before the first insertion and `right` after the
second insertion. -/
def layerOpenMarkedStackWeight
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) (c : Fin (left + sep + right + 1) → Ω) : ℝ :=
  f (c (layerOpenLeftIndex left sep right))
    * f (c (layerOpenRightIndex left sep right))
    * layerOpenStackWeight u k c

/-- The unnormalised open two-point numerator. -/
def layerOpenTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ c : Fin (left + sep + right + 1) → Ω,
    layerOpenMarkedStackWeight u k f left sep right c

/-- The same open two-point numerator, named as a transfer-matrix open-path
sum. -/
def layerOpenTransferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ c : Fin (left + sep + right + 1) → Ω,
    f (c (layerOpenLeftIndex left sep right))
      * f (c (layerOpenRightIndex left sep right))
      * (u (c 0) * pathWeight (layerTransferMatrix u k) c)

omit [DecidableEq Ω] in
/-- The open two-point numerator is the transfer-matrix open-path numerator. -/
theorem layerOpenTwoPointNumerator_eq_transfer
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoPointNumerator u k f left sep right =
      layerOpenTransferTwoPointNumerator u k f left sep right := by
  rfl

/-- The normalised open finite layer two-point function. -/
noncomputable def layerOpenTwoPoint
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  layerOpenTwoPointNumerator u k f left sep right
    / layerOpenPartition u k (left + sep + right)

/-! ## Conditional open-boundary spectral certificate -/

/-- A finite open-boundary min-gap certificate.  The certificate is deliberately
an input: later files can construct it from boundary-vector spectral estimates
or physical high-temperature windows. -/
structure LayerOpenMinSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ) where
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
      |layerOpenTransferTwoPointNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep

omit [DecidableEq Ω] in
/-- A finite open-boundary min-gap certificate gives the normalised open
two-point decay bound. -/
theorem layerOpenTwoPoint_abs_le_of_openMinSpectralGapCertificate
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f : Ω → ℝ}
    (cert : LayerOpenMinSpectralGapCertificate u k f)
    (left sep right : ℕ) :
    |layerOpenTwoPoint u k f left sep right| ≤
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
  have hmarked : |layerOpenTwoPointNumerator u k f left sep right|
      ≤ cert.prefactor * cert.scale ^ n * cert.theta ^ sep := by
    rw [layerOpenTwoPointNumerator_eq_transfer]
    exact cert.marked_abs_le left sep right
  rw [layerOpenTwoPoint, abs_div, abs_of_pos hden_pos]
  calc
    |layerOpenTwoPointNumerator u k f left sep right| / layerOpenPartition u k n
        = |layerOpenTwoPointNumerator u k f left sep right|
          * (layerOpenPartition u k n)⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (cert.prefactor * cert.scale ^ n * cert.theta ^ sep)
          * (cert.partitionPrefactor * cert.scale ^ n)⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg cert.prefactor_nonneg hscaleN.le) hθ)
    _ = (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ sep := by
            field_simp [(ne_of_gt cert.partitionPrefactor_pos), (ne_of_gt hscaleN)]

end TransferMatrix

end IsingModel
