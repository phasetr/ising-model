import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRate

/-!
# Concrete cubic named-rate le-high-temp positivity wrappers

Narrow child module for 3 ℤ^d cubic named-rate le-high-temp positivity
wrappers extracted from `CubicPseudoMassNamedRateLeHighTempRate.lean`:

* `latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate`,
* `cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate`,
* `latticeMass_ne_zero_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate`.

Each result is a thin composition wrapper around
`HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate`
plus the `latticeMass_*_of_HasExponentialDecay` positivity bridge. The
theorem names are unchanged from the former
`CubicPseudoMassNamedRateLeHighTempRate` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **Positive target lattice mass from a positive anchored cubic pseudo-mass**:
if the named anchored cubic pseudo-mass is positive and no larger than the
high-temperature rate, then the target-exhaustion `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Target lattice-mass half-open interval for a positive anchored cubic
named rate**: positivity upgrades the closed interval membership to
`(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨ENNReal.ofReal_pos.mpr hpos,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle⟩

/-- **Nonzero target lattice mass from a positive anchored cubic pseudo-mass**:
the positive lattice-mass bridge also rules out zero. -/
theorem latticeMass_ne_zero_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
      hα hr Λ hJ hβ hlt hpos hle)

end Ambient
end IsingModel
