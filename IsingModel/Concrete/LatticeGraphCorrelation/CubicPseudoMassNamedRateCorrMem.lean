import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Lattice-mass consequences of the active range and an explicit rate comparison

Turns the anchored cubic pair correlation lying in `(0,2)`, together with an explicit
comparison of the origin-anchored cubic pseudo-mass with the high-temperature rate
`-log(βJ·2d)`, into strict positivity of the lattice mass at an arbitrary target exhaustion,
into non-vanishing of that lattice mass, and into membership of the `ENNReal.ofReal`
pseudo-mass in `(0, latticeMass]`. Throughout, `0 ≤ J`, `0 < β` and `βJ·2d < 1`; the `(0,2)`
membership is what supplies strict positivity of the pseudo-mass, and the comparison is what
makes it an admissible decay rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Positive target lattice mass from cubic active range plus named-rate
comparison**: active-range membership supplies positivity of the named
pseudo-mass, so it is enough to prove the high-temperature rate comparison.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    hle

/-- **Target lattice-mass half-open interval from cubic active range plus
named-rate comparison**: active-range membership supplies the strict lower
endpoint and the named-rate comparison supplies the target upper endpoint.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    hle

/-- **Nonzero target lattice mass from cubic active range plus named-rate
comparison**: the positive target `latticeMass` bridge rules out zero. -/
theorem latticeMass_ne_zero_of_cubic_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_corr_mem_le_high_temp_rate
      hα hr Λ hJ hβ hlt hcorr_cubic hle)

end Ambient
end IsingModel
