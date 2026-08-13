import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay

/-!
# Cubic named-rate wrappers (`_of_le_high_temp_rate` family)

Bridges the origin-anchored cubic pseudo-mass to exponential decay and to `latticeMass`
under the hypothesis that the pseudo-mass is bounded above by the transferred
high-temperature rate. Each result passes through to the corresponding ambient lemma.
-/

namespace IsingModel
namespace Ambient

/-- **Anchored cubic pseudo-mass validates high-temperature decay**:
if the named anchored cubic pseudo-mass is bounded above by the transferred
high-temperature rate, then it is a valid exponential-decay rate for any target
exhaustion.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Anchored cubic pseudo-mass lower bound on target lattice mass**:
under the high-temperature comparison for the named anchored cubic pseudo-mass,
that pseudo-mass is bounded above by the target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (cubicOriginPseudoMassFromParamsAtPair_nonneg hα hr β J z)
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Target lattice-mass closed interval for an anchored cubic named rate**:
the nonnegative `ENNReal.ofReal` named rate lies in `[0, latticeMass]` once the
high-temperature rate comparison is available.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨zero_le _,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle⟩

end Ambient
end IsingModel
