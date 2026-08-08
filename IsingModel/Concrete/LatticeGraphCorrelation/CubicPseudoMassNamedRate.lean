import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasicIff
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRatePos

/-!
# The named high-temperature comparison for the origin-anchored cubic pseudo-mass

Introduces and eliminates `cubicOriginNamedRateLeHighTemp`, the irreducible proposition
naming the comparison of the origin-anchored cubic pseudo-mass with the high-temperature
rate `-log(βJ·2d)`. Under `0 ≤ J`, `0 < β` and `βJ·2d < 1`, that comparison follows — in the
plain inequality form and in the named form alike — from the anchored cubic pair correlation
lying in `(0,2)` together with a `pseudoMassG` lower bound on it, and the same assumptions
turn the named form into a validating exponential-decay rate at an arbitrary target
exhaustion. Unfolding the named form back to the inequality, and strict positivity of the
pseudo-mass from that `(0,2)` membership, require none of those assumptions.
-/

namespace IsingModel
namespace Ambient

/-- **Anchored cubic named-rate comparison from a cubic profile lower bound**:
if the anchored cubic pair correlation lies in the active pseudo-mass interval
and dominates `pseudoMassG` at the transferred high-temperature rate, then the
named anchored cubic pseudo-mass is no larger than that rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d)) := by
  exact (cubicOriginPseudoMassFromParamsAtPair_le_iff hα hr β J z
      (-Real.log (β * J * ↑(2 * d)))).2
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Named anchored cubic rate comparison from cubic profile inputs**:
active-range membership and the cubic profile lower bound prove the lightweight
named high-temperature comparison proposition.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginNamedRateLeHighTemp_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    cubicOriginNamedRateLeHighTemp hα hr β J z := by
  rw [cubicOriginNamedRateLeHighTemp]
  exact cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
    hα hr hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Anchored cubic named pseudo-mass is positive from cubic active range**:
active-range membership of the anchored cubic pair correlation gives strict
positivity of the named concrete pseudo-mass.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]
  exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) 0 z hcorr_cubic

/-- The irreducible named comparison proposition unfolds to the underlying
high-temperature rate comparison when a downstream theorem needs the ordinary
inequality form. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d)) := by
  rw [cubicOriginNamedRateLeHighTemp] at hnamed
  exact hnamed

/-- **Anchored cubic named proposition validates high-temperature decay**:
the lightweight named comparison proposition feeds the conditional decay
bridge without exposing the heavy comparison in the theorem statement.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

end Ambient
end IsingModel
