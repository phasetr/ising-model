import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Closed lattice-mass bounds from the named rate comparison

Bounds the `ENNReal.ofReal` image of the origin-anchored cubic pseudo-mass above by the
lattice mass of an arbitrary target exhaustion, and places that image in `[0, latticeMass]`,
taking the irreducible `cubicOriginNamedRateLeHighTemp` as the only comparison input. Each
statement assumes `0 ≤ J`, `0 < β` and `βJ·2d < 1`; strict positivity of the pseudo-mass is
not assumed, which is why the interval here is the closed one.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Target lattice-mass lower bound from the named comparison proposition**:
the irreducible proposition form is enough to place the named rate below the
target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Closed target interval from the named comparison proposition**:
the `ENNReal.ofReal` named rate lies in `[0, latticeMass]` under the
irreducible comparison proposition.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Icc_latticeMass_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

end Ambient
end IsingModel
