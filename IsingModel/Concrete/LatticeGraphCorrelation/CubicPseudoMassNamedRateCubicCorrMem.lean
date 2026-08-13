import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLatticeMass

/-!
# Lattice-mass and decay consequences of the named rate comparison

Reads the irreducible `cubicOriginNamedRateLeHighTemp` as the comparison of the
origin-anchored cubic pseudo-mass with the high-temperature rate `-log(βJ·2d)`, and draws
the consequences at an arbitrary target exhaustion: strict positivity of the lattice mass,
its non-vanishing, membership of the `ENNReal.ofReal` pseudo-mass in `(0, latticeMass]`, and
bundles pairing a validating exponential-decay rate with interval membership. Throughout,
`0 ≤ J`, `0 < β` and `βJ·2d < 1`. The bundle landing in the closed interval
`[0, latticeMass]` takes the named proposition as its only further input; every other
statement here also assumes the anchored cubic pair correlation lies in `(0,2)`, which is
what makes the pseudo-mass strictly positive.
-/

namespace IsingModel
namespace Ambient


/-- **Positive target lattice mass from active range plus named proposition**:
active-range membership supplies positivity of the named pseudo-mass, while the
irreducible proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Half-open target interval from active range plus named proposition**:
the active-range proof gives the strict lower endpoint and the named proposition
gives the target lattice-mass upper endpoint.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Nonzero target lattice mass from active range plus named proposition**:
the positive target lattice-mass bridge also rules out zero. -/
theorem latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
      hα hr Λ hJ hβ hlt hcorr_cubic hnamed)

/-- **Named-proposition decay plus closed target interval**: the irreducible
comparison proposition supplies both validating exponential decay and closed
interval membership for the named rate.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Icc_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed⟩

/-- **Named-proposition decay plus half-open target interval**: active-range
membership upgrades the closed interval supplied by the named proposition to
the positive half-open interval.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hcorr_cubic hnamed⟩

end Ambient
end IsingModel
