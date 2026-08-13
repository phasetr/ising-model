import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateLeHighTempRate

/-!
# Lattice-mass consequences of a positive pseudo-mass below the high-temperature rate

Turns strict positivity of the origin-anchored cubic pseudo-mass, together with the
comparison placing it below the high-temperature rate `-log(βJ·2d)`, into strict positivity
of the lattice mass at an arbitrary target exhaustion, into non-vanishing of that lattice
mass, and into membership of the `ENNReal.ofReal` pseudo-mass in `(0, latticeMass]`. Every
statement assumes `0 ≤ J`, `0 < β` and `βJ·2d < 1`. The comparison is what makes the
pseudo-mass an admissible decay rate, so that the lattice mass dominates it; positivity is
what moves the lower endpoint of the interval off zero.
-/

namespace IsingModel
namespace Ambient


/-- **Positive target lattice mass from a positive anchored cubic pseudo-mass**:
if the named anchored cubic pseudo-mass is positive and no larger than the
high-temperature rate, then the target-exhaustion `latticeMass` is positive.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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
