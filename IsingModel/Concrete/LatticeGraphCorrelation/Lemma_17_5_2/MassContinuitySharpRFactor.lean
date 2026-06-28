import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b: the distance (`r`) factor of the sharp profile bound (p.312)

The pure real-analysis `r`-bookkeeping that turns the per-pair sharp β-derivative bound into a
**distance-uniform** constant.  In GJ p.312, after substituting `m⁻^{2α}·dm⁻/dσ ≤ const`, the cross
term carries the factor `(1+(m·r)^α)·(1+r)^{−(2α−d)}/r` (`r = d(x,z) ≥ 1`).  With `m ≤ Mwitness`
(the upper mass bound) and `α ≥ d−1` (so `d−α−1 ≤ 0`), this factor is bounded by `1 + Mwitness^α`,
uniformly in `r`.  The key is `r^α·(1+r)^{−(2α−d)}/r ≤ 1`: writing `(1+r)^{−(2α−d)} ≤ r^{−(2α−d)}`
(base-antitone for the nonpositive exponent) collapses the `r`-powers to `r^{d−α−1} ≤ 1`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **The `r`-power collapse** (GJ p.312): for `d < 2α`, `d ≤ α+1` (i.e. `α ≥ d−1`) and `r ≥ 1`,
`r^α·(1+r)^{−(2α−d)}/r ≤ 1`.  Since `r ≤ 1+r` and `−(2α−d) ≤ 0`, `(1+r)^{−(2α−d)} ≤ r^{−(2α−d)}`;
combining the `rpow` powers gives `r^{α−(2α−d)−1} = r^{d−α−1} ≤ 1` (`r ≥ 1`, `d−α−1 ≤ 0`). -/
theorem sharp_r_factor_le {α d : ℕ} (hαd : d < 2 * α) (hαd1 : d ≤ α + 1)
    {r : ℝ} (hr1 : 1 ≤ r) :
    (r : ℝ) ^ α * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hexp_nonpos : -(2 * (α : ℝ) - (d : ℝ)) ≤ 0 := by
    have : (d : ℝ) < 2 * α := by exact_mod_cast hαd
    linarith
  have hra_nn : 0 ≤ r ^ (α : ℝ) := Real.rpow_nonneg hr0.le _
  have hstep : (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) ≤ r ^ (-(2 * (α : ℝ) - (d : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hr0 (by linarith) hexp_nonpos
  rw [div_eq_mul_inv, ← Real.rpow_natCast r α, ← Real.rpow_neg_one r]
  calc r ^ (α : ℝ) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) * r ^ (-1 : ℝ)
      ≤ r ^ (α : ℝ) * r ^ (-(2 * (α : ℝ) - (d : ℝ))) * r ^ (-1 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0.le _)
        exact mul_le_mul_of_nonneg_left hstep hra_nn
    _ = r ^ ((α : ℝ) + -(2 * (α : ℝ) - (d : ℝ)) + (-1 : ℝ)) := by
        rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
    _ = r ^ ((d : ℝ) - (α : ℝ) - 1) := by congr 1; ring
    _ ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos hr1 ?_
        have : (d : ℝ) ≤ (α : ℝ) + 1 := by exact_mod_cast hαd1
        linarith

/-- **The full cross-term profile factor bound** (GJ p.312): for `d < 2α`, `d ≤ α+1`, `0 ≤ m ≤ Mw`,
`r ≥ 1`, `(1+(m·r)^α)·(1+r)^{−(2α−d)}/r ≤ 1 + Mw^α`.  Splits into the constant part
`(1+r)^{−(2α−d)}/r ≤ 1/r ≤ 1` and the growing part `(m·r)^α·(1+r)^{−(2α−d)}/r ≤
Mw^α·(r^α·(1+r)^{−(2α−d)}/r) ≤ Mw^α` (via `sharp_r_factor_le`). -/
theorem sharp_profile_factor_le {α d : ℕ} (hαd : d < 2 * α) (hαd1 : d ≤ α + 1)
    {m Mw r : ℝ} (hm0 : 0 ≤ m) (hmMw : m ≤ Mw) (hr1 : 1 ≤ r) :
    (1 + (m * r) ^ α) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r ≤ 1 + Mw ^ α := by
  have hr0 : 0 < r := by linarith
  have hMw0 : 0 ≤ Mw := le_trans hm0 hmMw
  have hexp_nonpos : -(2 * (α : ℝ) - (d : ℝ)) ≤ 0 := by
    have : (d : ℝ) < 2 * α := by exact_mod_cast hαd
    linarith
  have hpr1 : (1 : ℝ) ≤ 1 + r := by linarith
  have hpow1 : (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpr1 hexp_nonpos
  have hpow_nn : 0 ≤ (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) := Real.rpow_nonneg (by linarith) _
  have hdist : (1 + (m * r) ^ α) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r
      = (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r
        + (m * r) ^ α * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r := by ring
  rw [hdist]
  have term1 : (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r ≤ 1 := by
    calc (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r ≤ 1 / r :=
          (div_le_div_iff_of_pos_right hr0).mpr hpow1
      _ ≤ 1 := by rw [div_le_one hr0]; exact hr1
  have term2 : (m * r) ^ α * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r ≤ Mw ^ α := by
    have hmr : (m * r) ^ α ≤ Mw ^ α * r ^ α := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hmMw α) (pow_nonneg hr0.le α)
    calc (m * r) ^ α * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r
        ≤ (Mw ^ α * r ^ α) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r :=
          (div_le_div_iff_of_pos_right hr0).mpr
            (mul_le_mul_of_nonneg_right hmr hpow_nn)
      _ = Mw ^ α * ((r : ℝ) ^ α * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r) := by ring
      _ ≤ Mw ^ α * 1 :=
          mul_le_mul_of_nonneg_left (sharp_r_factor_le hαd hαd1 hr1) (pow_nonneg hMw0 α)
      _ = Mw ^ α := mul_one _
  linarith [term1, term2]

/-- **The per-pair sharp power-derivative bound collapses to a distance- and `β`-uniform constant**
(GJ p.312): for `d < 2α`, `d ≤ α+1`, `0 ≤ m ≤ Mw`, `r ≥ 1`, `0 ≤ C`, `0 ≤ J`, the FV per-pair
`(2α+1)`-power derivative bound `(2α+1)·⟨sharp(C)⟩·m^{2α}/r` is bounded by the `m,r`-free constant
`(2α+1)·(J·2(1+Mw^α)e^{Mw}·C·Mw^{2α} + J·4d((1+2^α)e^{Mw}+(1+Mw^α)e^{Mw}/2)·Mw^{2α})`.  The cross
term collapses via `sharp_profile_factor_le` (the `(1+(m·r)^α)(1+r)^{−(2α−d)}/r ≤ 1+Mw^α` factor)
plus `e^m ≤ e^{Mw}`, `m^{2α} ≤ Mw^{2α}`; the incident term via `1/r ≤ 1` and the same
monotonicities. -/
theorem pow_succ_sharp_div_r_le_uniform {α d : ℕ} (hαd : d < 2 * α) (hαd1 : d ≤ α + 1)
    {m Mw r C J : ℝ} (hm0 : 0 ≤ m) (hmMw : m ≤ Mw) (hr1 : 1 ≤ r) (hC0 : 0 ≤ C) (hJ0 : 0 ≤ J) :
    ↑(2 * α + 1) * ((J * (2 * (1 + (m * r) ^ α) * Real.exp m
            * (C * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
            + (1 + m ^ α) * Real.exp m / 2))) * m ^ (2 * α)) / r
      ≤ ↑(2 * α + 1) * (J * (2 * (1 + Mw ^ α) * Real.exp Mw * (C * Mw ^ (2 * α)))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp Mw
            + (1 + Mw ^ α) * Real.exp Mw / 2) * Mw ^ (2 * α))) := by
  have hr0 : 0 < r := by linarith
  have hMw0 : 0 ≤ Mw := le_trans hm0 hmMw
  have hexpm : Real.exp m ≤ Real.exp Mw := Real.exp_le_exp.mpr hmMw
  have hm2α : m ^ (2 * α) ≤ Mw ^ (2 * α) := pow_le_pow_left₀ hm0 hmMw _
  have hmα : m ^ α ≤ Mw ^ α := pow_le_pow_left₀ hm0 hmMw _
  have hcast_nn : (0 : ℝ) ≤ ↑(2 * α + 1) := by positivity
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hcast_nn
  -- reduce to `BIG / r ≤ cross_M + inc_M`.
  have hBIG : (J * (2 * (1 + (m * r) ^ α) * Real.exp m
            * (C * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
            + (1 + m ^ α) * Real.exp m / 2))) * m ^ (2 * α) / r
      = (J * (2 * (1 + (m * r) ^ α) * Real.exp m
            * (C * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ)))))) * m ^ (2 * α) / r
        + (J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
            + (1 + m ^ α) * Real.exp m / 2))) * m ^ (2 * α) / r := by ring
  rw [hBIG]
  refine add_le_add ?_ ?_
  · -- cross term.
    have hrw : (J * (2 * (1 + (m * r) ^ α) * Real.exp m
              * (C * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ)))))) * m ^ (2 * α) / r
        = (J * 2 * C * Real.exp m * m ^ (2 * α))
            * ((1 + (m * r) ^ α) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r) := by ring
    rw [hrw]
    calc (J * 2 * C * Real.exp m * m ^ (2 * α))
            * ((1 + (m * r) ^ α) * (1 + r) ^ (-(2 * (α : ℝ) - (d : ℝ))) / r)
        ≤ (J * 2 * C * Real.exp m * m ^ (2 * α)) * (1 + Mw ^ α) := by
          refine mul_le_mul_of_nonneg_left (sharp_profile_factor_le hαd hαd1 hm0 hmMw hr1) ?_
          positivity
      _ ≤ (J * 2 * C * Real.exp Mw * Mw ^ (2 * α)) * (1 + Mw ^ α) := by
          have h1Mw : (0 : ℝ) ≤ 1 + Mw ^ α := by positivity
          gcongr
      _ = J * (2 * (1 + Mw ^ α) * Real.exp Mw * (C * Mw ^ (2 * α))) := by ring
  · -- incident term.
    have hrw : (J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2))) * m ^ (2 * α) / r
        = (J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2)) * m ^ (2 * α)) * r⁻¹ := by ring
    rw [hrw]
    have hrinv1 : r⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hr1
    have hinc_nn : (0 : ℝ) ≤ J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
        + (1 + m ^ α) * Real.exp m / 2)) * m ^ (2 * α) := by positivity
    calc (J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2)) * m ^ (2 * α)) * r⁻¹
        ≤ (J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2)) * m ^ (2 * α)) * 1 :=
          mul_le_mul_of_nonneg_left hrinv1 hinc_nn
      _ = J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2) * m ^ (2 * α)) := by rw [mul_one]; ring
      _ ≤ J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp Mw
              + (1 + Mw ^ α) * Real.exp Mw / 2) * Mw ^ (2 * α)) := by gcongr

end Ambient
end IsingModel
