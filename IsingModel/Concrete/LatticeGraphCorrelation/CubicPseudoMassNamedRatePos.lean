import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRate

/-!
# Cubic named-rate _pos family wrappers

Narrow child module for four ℤ^d wrappers extracted from
`CubicPseudoMassNamedRate.lean`:

* `latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos`,
* `cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos`,
* `latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_pos`,
* `cubicNamedRate_decay_mem_Ioc_of_cubicOriginNamedRateLeHighTemp_pos`.

Each pairs strict positivity of the cubic-origin pseudo-mass with the
named `cubicOriginNamedRateLeHighTemp` proposition to upgrade
`Icc`-style bundles to the `(0, latticeMass]` regime.
-/

namespace IsingModel
namespace Ambient

/-- **Positive target lattice mass from a positive named rate and named
comparison proposition**: strict positivity is supplied directly, and the
irreducible proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Half-open target interval from a positive named rate and named
comparison proposition**: direct positivity upgrades the named-proposition
closed interval to `(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Nonzero target lattice mass from a positive named rate and named
comparison proposition**: the positive target lattice-mass bridge rules out
zero. -/
theorem latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos
      hα hr Λ hJ hβ hlt hpos hnamed)

/-- **Named-proposition decay plus half-open target interval from direct
positivity**: strict positivity supplies the interval lower endpoint while the
named proposition supplies decay and the upper endpoint.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos
      hα hr Λ hJ hβ hlt hpos hnamed⟩

end Ambient
end IsingModel
