import IsingModel.HLSConvolutionSharp.RadialRegionBounds

/-!
# Sharp HLS convolution (3/3): constant reduction and the sharp decay bound

Structural split (3/3) of `HLSConvolutionSharp`.  This child holds the two base-shift
bounds `rpow_neg_half_le` / `rpow_pos_two_mul_le`, the real-valued near- and far-region
constant reductions, and the headline sharp distance-dependent Hardy--Littlewood--Sobolev
convolution bound `hls_conv_sharp_decay`.  It builds on the region bounds in the sibling
`...RadialRegionBounds`, which in turn rests on `...ShellSumsIntegralComparison`.  See the
`HLSConvolutionSharp` facade module for the full contents overview.
-/

namespace IsingModel

open scoped ENNReal
open Ambient

/-- **Base-shift bound, nonpositive exponent.**  If `(1+D)/2 ≤ 1+k` and `D ≥ 0`,
then for `α ≥ 0`,  `(1+k)^{−α} ≤ 2^α·(1+D)^{−α}`.

This relates the near-region radius `1+k = 1+K` (with `K = D/2`) to the decay
distance `1+D`: since the exponent is nonpositive the function is antitone, and
`((1+D)/2)^{−α} = 2^α·(1+D)^{−α}`. -/
theorem rpow_neg_half_le {α : ℝ} (hαnn : 0 ≤ α) {k D : ℝ} (hD : 0 ≤ D)
    (hlow : (1 + D) / 2 ≤ 1 + k) :
    (1 + k) ^ (-α) ≤ (2 : ℝ) ^ α * (1 + D) ^ (-α) := by
  have hDpos : (0 : ℝ) < 1 + D := by linarith
  have h1 : (1 + k) ^ (-α) ≤ ((1 + D) / 2) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlow (by linarith)
  have h2 : ((1 + D) / 2) ^ (-α) = (2 : ℝ) ^ α * (1 + D) ^ (-α) := by
    rw [Real.div_rpow hDpos.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg hDpos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv, mul_comm]
  rwa [h2] at h1

/-- **Base-shift bound, nonnegative exponent.**  If `k+2 ≤ 2·(1+D)` and `k,D ≥ 0`,
then for `β ≥ 0`,  `(k+2)^β ≤ 2^β·(1+D)^β`.

This bounds the near-region ball radius `K+2` by `2·(1+D)`, used with the
positive exponent `β = d−α`. -/
theorem rpow_pos_two_mul_le {β : ℝ} (hβ : 0 ≤ β) {k D : ℝ} (hk : 0 ≤ k) (hD : 0 ≤ D)
    (hhigh : k + 2 ≤ 2 * (1 + D)) :
    (k + 2) ^ β ≤ (2 : ℝ) ^ β * (1 + D) ^ β := by
  have h1 : (k + 2) ^ β ≤ (2 * (1 + D)) ^ β :=
    Real.rpow_le_rpow (by linarith) hhigh hβ
  rwa [Real.mul_rpow (by norm_num) (by linarith)] at h1

/-- **Near-region constant reduction (real).**  Under `d/2 < α < d`, the near-region
value `(1+k)^{−α}·(2^d·((k+2)^{d−α}/(d−α)+1))` (with `k = K = D/2`) is dominated by
`C_near·(1+D)^{d−2α}` with the explicit positive constant
`C_near = 2^α·2^d·2^{d−α}/(d−α) + 2^d·2^α`.

The dominant term uses both base shifts and the exponent identity
`(1+D)^{−α}·(1+D)^{d−α} = (1+D)^{d−2α}`; the trailing `+1` term uses
`(1+D)^{−α} ≤ (1+D)^{d−2α}` (`−α ≤ d−2α` since `α ≤ d`, base `≥ 1`). -/
theorem near_real_decay_le {d : ℕ} {α : ℝ} (hαnn : 0 ≤ α) (hα : α < (d : ℝ))
    {k D : ℝ} (hk : 0 ≤ k) (hD : 0 ≤ D)
    (hlow : (1 + D) / 2 ≤ 1 + k) (hhigh : k + 2 ≤ 2 * (1 + D)) :
    (1 + k) ^ (-α) * ((2 : ℝ) ^ d * ((k + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1))
      ≤ ((2 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) - α) / ((d : ℝ) - α)
          + (2 : ℝ) ^ d * (2 : ℝ) ^ α) * (1 + D) ^ ((d : ℝ) - 2 * α) := by
  have hDpos : (0 : ℝ) < 1 + D := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - α := by linarith
  have hne : ((d : ℝ) - α) ≠ 0 := ne_of_gt hd1
  have hk1 : (1 + k) ^ (-α) ≤ (2 : ℝ) ^ α * (1 + D) ^ (-α) := rpow_neg_half_le hαnn hD hlow
  have hk2 : (k + 2) ^ ((d : ℝ) - α) ≤ (2 : ℝ) ^ ((d : ℝ) - α) * (1 + D) ^ ((d : ℝ) - α) :=
    rpow_pos_two_mul_le (by linarith) hk hD hhigh
  have e2 : (1 + D) ^ (-α) * (1 + D) ^ ((d : ℝ) - α) = (1 + D) ^ ((d : ℝ) - 2 * α) := by
    rw [← Real.rpow_add hDpos]; congr 1; ring
  have e4 : (1 + D) ^ (-α) ≤ (1 + D) ^ ((d : ℝ) - 2 * α) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsplit : (1 + k) ^ (-α) * ((2 : ℝ) ^ d * ((k + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1))
      = (1 + k) ^ (-α) * (2 : ℝ) ^ d * (k + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α)
        + (1 + k) ^ (-α) * (2 : ℝ) ^ d := by
    field_simp
  have hRHS : ((2 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) - α) / ((d : ℝ) - α)
        + (2 : ℝ) ^ d * (2 : ℝ) ^ α) * (1 + D) ^ ((d : ℝ) - 2 * α)
      = (2 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) - α) * (1 + D) ^ ((d : ℝ) - 2 * α)
          / ((d : ℝ) - α)
        + (2 : ℝ) ^ d * (2 : ℝ) ^ α * (1 + D) ^ ((d : ℝ) - 2 * α) := by
    field_simp
  rw [hsplit, hRHS]
  apply add_le_add
  · rw [show (2 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) - α) * (1 + D) ^ ((d : ℝ) - 2 * α)
          = (2 : ℝ) ^ α * (1 + D) ^ (-α) * (2 : ℝ) ^ d
              * ((2 : ℝ) ^ ((d : ℝ) - α) * (1 + D) ^ ((d : ℝ) - α)) by rw [← e2]; ring]
    gcongr
  · have ht2 : (1 + k) ^ (-α) ≤ (2 : ℝ) ^ α * (1 + D) ^ ((d : ℝ) - 2 * α) :=
      hk1.trans (mul_le_mul_of_nonneg_left e4 (by positivity))
    calc (1 + k) ^ (-α) * (2 : ℝ) ^ d
        ≤ ((2 : ℝ) ^ α * (1 + D) ^ ((d : ℝ) - 2 * α)) * (2 : ℝ) ^ d := by gcongr
      _ = (2 : ℝ) ^ d * (2 : ℝ) ^ α * (1 + D) ^ ((d : ℝ) - 2 * α) := by ring

/-- **Far-region constant reduction (real).**  Under `d/2 < α`, the far-region value
`3^α·(2^d·(k+1)^{d−2α}/(2α−d))` (with `k = K = D/2`) is dominated by
`C_far·(1+D)^{d−2α}` with the explicit positive constant
`C_far = 3^α·2^d·2^{2α−d}/(2α−d)`.

Since `d−2α < 0` and `(1+D)/2 ≤ k+1`, the base shift gives
`(k+1)^{d−2α} ≤ 2^{2α−d}·(1+D)^{d−2α}` (`rpow_neg_half_le` with exponent `2α−d`). -/
theorem far_real_decay_le {d : ℕ} {α : ℝ} (hα2 : (d : ℝ) < 2 * α) {k D : ℝ}
    (hD : 0 ≤ D) (hlow : (1 + D) / 2 ≤ 1 + k) :
    (3 : ℝ) ^ α * ((2 : ℝ) ^ d * (k + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)))
      ≤ ((3 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ (2 * α - (d : ℝ)) / (2 * α - (d : ℝ)))
          * (1 + D) ^ ((d : ℝ) - 2 * α) := by
  have hden : (0 : ℝ) < 2 * α - (d : ℝ) := by linarith
  have hαd : (0 : ℝ) ≤ 2 * α - (d : ℝ) := hden.le
  have hshift : (k + 1) ^ ((d : ℝ) - 2 * α)
      ≤ (2 : ℝ) ^ (2 * α - (d : ℝ)) * (1 + D) ^ ((d : ℝ) - 2 * α) := by
    have h := rpow_neg_half_le hαd hD hlow
    rwa [show (1 : ℝ) + k = k + 1 by ring, show -(2 * α - (d : ℝ)) = (d : ℝ) - 2 * α by ring] at h
  rw [show (3 : ℝ) ^ α * ((2 : ℝ) ^ d * (k + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)))
        = (3 : ℝ) ^ α * (2 : ℝ) ^ d * (k + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)) by ring,
    show ((3 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ (2 * α - (d : ℝ)) / (2 * α - (d : ℝ)))
          * (1 + D) ^ ((d : ℝ) - 2 * α)
        = (3 : ℝ) ^ α * (2 : ℝ) ^ d
            * ((2 : ℝ) ^ (2 * α - (d : ℝ)) * (1 + D) ^ ((d : ℝ) - 2 * α)) / (2 * α - (d : ℝ)) by
      ring]
  gcongr

/-- **Sharp distance-dependent Hardy–Littlewood–Sobolev convolution bound on `ℤ^d`.**
For `d/2 < α < d` there is a positive constant `C` such that for all `x y`,
`∑_z (1+|x−z|)^{−α}·(1+|y−z|)^{−α} ≤ C·(1+|x−y|)^{−(2α−d)}`
(everything in `ℝ≥0∞` via `ENNReal.ofReal`).

This is the genuinely hard, non-obstructed analytic core behind the uniform
Lipschitz control of `m⁻^{2α+1}` needed for the true-mass continuity statement
GJ Theorem 17.5.1.  The proof covers `ℤ^d` by the near-`x`, near-`y` and far
regions relative to `D = |x−y|` (`tsum_conv_le_sum_regions`), bounds each region
by a radial sum (`tsum_nearx_region_le`, `tsum_far_region_le`) and reduces each
to the common decay factor `(1+D)^{d−2α}` with explicit constants
(`near_real_decay_le`, `far_real_decay_le`); the witness is `C = 2·C_near + C_far`. -/
theorem hls_conv_sharp_decay {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hαnn : 0 ≤ α) (hα : α < (d : ℝ)) (hα2 : (d : ℝ) < 2 * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin d → ℤ,
      (∑' z : Fin d → ℤ,
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)))
        ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ((1 + (IsingModel.latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - α := by linarith
  have hd2 : (0 : ℝ) < 2 * α - (d : ℝ) := by linarith
  set Cnear : ℝ :=
    (2 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) - α) / ((d : ℝ) - α)
      + (2 : ℝ) ^ d * (2 : ℝ) ^ α with hCnear
  set Cfar : ℝ :=
    (3 : ℝ) ^ α * (2 : ℝ) ^ d * (2 : ℝ) ^ (2 * α - (d : ℝ)) / (2 * α - (d : ℝ)) with hCfar
  have hCnpos : 0 < Cnear := by
    rw [hCnear]; exact add_pos (div_pos (by positivity) hd1) (by positivity)
  have hCfpos : 0 < Cfar := by rw [hCfar]; exact div_pos (by positivity) hd2
  refine ⟨2 * Cnear + Cfar, by linarith, fun x y => ?_⟩
  have hDR : (0 : ℝ) ≤ (IsingModel.latticeDistance d x y : ℝ) := by positivity
  have hKR : (0 : ℝ) ≤ ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) := by positivity
  have hlow : (1 + (IsingModel.latticeDistance d x y : ℝ)) / 2
      ≤ 1 + ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) := by
    have h1 : IsingModel.latticeDistance d x y
        ≤ 1 + 2 * (IsingModel.latticeDistance d x y / 2) := by omega
    have h2 : (IsingModel.latticeDistance d x y : ℝ)
        ≤ 1 + 2 * ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hhigh : ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) + 2
      ≤ 2 * (1 + (IsingModel.latticeDistance d x y : ℝ)) := by
    have h1 : IsingModel.latticeDistance d x y / 2
        ≤ 2 * IsingModel.latticeDistance d x y := by omega
    have h2 : ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ)
        ≤ 2 * (IsingModel.latticeDistance d x y : ℝ) := by exact_mod_cast h1
    linarith
  -- near-x region bound
  have hnx : (∑' z : Fin d → ℤ,
        (if 2 * IsingModel.latticeDistance d x z ≤ IsingModel.latticeDistance d x y then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0))
        ≤ ENNReal.ofReal Cnear *
            ENNReal.ofReal
              ((1 + (IsingModel.latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
    refine (tsum_nearx_region_le hd hαnn hα x y).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCnpos.le]
    apply ENNReal.ofReal_le_ofReal
    rw [neg_sub, hCnear]
    exact near_real_decay_le hαnn hα hKR hDR hlow hhigh
  -- near-y region bound (by symmetry, commuting the factors)
  have hny : (∑' z : Fin d → ℤ,
        (if 2 * IsingModel.latticeDistance d y z ≤ IsingModel.latticeDistance d x y then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0))
        ≤ ENNReal.ofReal Cnear *
            ENNReal.ofReal
              ((1 + (IsingModel.latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
    have h := tsum_nearx_region_le hd hαnn hα y x
    rw [IsingModel.latticeDistance_comm d y x] at h
    refine le_trans (le_of_eq ?_) (h.trans ?_)
    · refine tsum_congr (fun z => ?_)
      by_cases hc : 2 * IsingModel.latticeDistance d y z ≤ IsingModel.latticeDistance d x y
      · rw [if_pos hc, if_pos hc, mul_comm]
      · rw [if_neg hc, if_neg hc]
    · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCnpos.le]
      apply ENNReal.ofReal_le_ofReal
      rw [neg_sub, hCnear]
      exact near_real_decay_le hαnn hα hKR hDR hlow hhigh
  -- far region bound
  have hfar : (∑' z : Fin d → ℤ,
        (if IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d x z ∧
            IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d y z then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0))
        ≤ ENNReal.ofReal Cfar *
            ENNReal.ofReal
              ((1 + (IsingModel.latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
    refine (tsum_far_region_le hd hα2 x y).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCfpos.le]
    apply ENNReal.ofReal_le_ofReal
    rw [neg_sub, hCfar]
    exact far_real_decay_le hα2 hDR hlow
  -- assemble
  refine (tsum_conv_le_sum_regions x y).trans ?_
  refine (add_le_add (add_le_add hnx hny) hfar).trans (le_of_eq ?_)
  rw [← add_mul, ← add_mul,
    ← ENNReal.ofReal_add hCnpos.le hCnpos.le,
    ← ENNReal.ofReal_add (add_nonneg hCnpos.le hCnpos.le) hCfpos.le]
  congr 2
  ring

end IsingModel
