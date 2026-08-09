import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointBounds
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PathLowerBound

/-!
# ℤ^d the tanh-power profile bound and its pseudo-mass consequences (§17.5)

Instantiates at `IsingModel.latticeGraph d`, at zero external field, the chain that starts
from the numerical condition that `pseudoMassG α r (-log (β * J * (2 * d)))` is at most
`tanh (β * J) ^ latticeDistance d 0 z` at a site `z` distinct from the origin. That condition
already yields the same lower bound for the pair correlation anchored at the origin along
`Ambient.cubicExhaustion d`, assuming only `0 ≤ J`, `0 < β` and `z ≠ 0` — no positivity of
`r`, no lower bound on `α`, and no high-temperature condition. Adding `0 < r` and the
high-temperature condition that `β * J * (2 * d)` is below one makes that correlation
strictly positive and places the anchored two-point function in `Set.Ioo 0 2`. Adding `1 ≤ α`
on top of those bounds the totalised pseudo-mass of the anchored two-point function, and then
its non-totalised counterpart, by the transferred rate `-log (β * J * (2 * d))`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Tanh-power profile bound implies the cubic pair-correlation profile bound**:
the existing path lower bound
`tanh(βJ) ^ latticeDistance d 0 z ≤ twoPointFunction d ⟨J,0,β⟩ z`
turns the numerical condition
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ latticeDistance d 0 z`
into the cubic-exhaustion correlation lower bound required by the
profile-comparison bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
    {α d : ℕ} {r β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} := by
  have hpow_le_corr :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} := by
    change Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z
    exact twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz
  exact hprofile_tanh.trans hpow_le_corr

/-- **Cubic pair correlation is positive from a tanh-power profile bound**:
under the high-temperature hypothesis, the Lean real-log rate `-log(βJ·2d)` is
nonnegative, so `pseudoMassG` is positive at that rate.  Combining this
positivity with the tanh-power reduction gives positivity of the anchored cubic
pair correlation.

This supplies the lower half of the active-range input used by the
profile-comparison bridge toward GJ §17.5 Lemma 17.5.2.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr)
    (pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
      (α := α) (d := d) (r := r) (β := β) (J := J)
      hJ hβ (z := z) hz hprofile_tanh)

set_option maxHeartbeats 2000000 in
-- The totalized proof splits on active-interval membership and reuses the
-- implicit pseudo-mass comparison, which is heavier than the surrounding wrappers.
/-- **Two-point pseudo-mass extension comparison from a tanh-power profile bound**:
the tanh-power lower-bound reduction supplies the profile comparison whenever
the anchored two-point function is in the active interval.  Outside the active
interval, `pseudoMassExt` is zero, so the high-temperature comparison is
automatic from nonnegativity of the Lean real-log rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  by_cases hcorr : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2
  · rw [pseudoMassExt_of_mem hα hr hcorr]
    exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two
  · rw [pseudoMassExt_of_not_mem hα hr hcorr]
    exact hrate_nonneg

/-- **Two-point active range from a tanh-power profile bound**: the same
tanh-power lower-bound reduction used for the totalized comparison also proves
that the anchored two-point function lies in the pseudo-mass active interval
`(0,2)`.  The lower endpoint comes from positivity of `pseudoMassG` at the
Lean total real-log rate; the upper endpoint uses the universal bound
`twoPointFunction ≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  constructor
  · exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr) hprofile_two
  · exact lt_of_le_of_lt
      (twoPointFunction_le_one d (⟨J, 0, β⟩ : IsingParams ℝ) z) one_lt_two

/-- **Ordinary two-point pseudo-mass comparison from a tanh-power profile bound**:
once the tanh-power profile bound places the anchored two-point function in
`(0,2)`, the implicit pseudo-mass comparison gives the non-totalized
`pseudoMass` bound by the high-temperature rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hcorr :
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 :=
    twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two

end Ambient

end IsingModel
