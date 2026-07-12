import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExhaustionPos

/-!
# ℤ^d latticeMass_pos pseudoMassFromParamsAtPair cubic wrappers

Narrow child module for two ℤ^d
`latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_*` wrappers
extracted from `LatticeMassPseudoMassTransferCubic.lean`:

* `latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate`,
* `latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Cubic-reference comparison gives positive lattice mass for any exhaustion**:
if the target pseudo-mass is positive and the cubic-reference pseudo-mass is no
larger than the high-temperature rate, then the target `latticeMass` is
positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos hle_cubic

/-- **Cubic-reference profile bound gives positive lattice mass for any exhaustion**:
if the target pseudo-mass is positive and the cubic exhaustion supplies the
profile lower bound at the high-temperature rate, then the target
`latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos hcorr_cubic hprofile_cubic

end Ambient
end IsingModel
