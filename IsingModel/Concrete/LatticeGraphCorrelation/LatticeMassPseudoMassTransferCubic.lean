import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.PseudoMass
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExhaustion

/-!
# Lattice-mass: pseudoMassFromParamsAtPair cubic variants

Narrow child module for the §17.5 pseudoMassFromParamsAtPair cubic
variant wrappers (6 theorems specialising the exhaustion variants to
`cubicExhaustion d`):
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_cubic_*`,
`latticeMass_ge_pseudoMassFromParamsAtPair_of_cubic_*`, and
`latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_*`. The theorem
names are unchanged from the former `LatticeMassPseudoMassTransfer`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Cubic-reference pseudo-mass comparison transfers to any exhaustion**:
the specialization of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`
where the reference exhaustion is `cubicExhaustion d`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic-reference profile bound validates the target pseudo-mass**:
the specialization of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr`
with `cubicExhaustion d` as the reference exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Cubic-reference comparison gives an arbitrary-exhaustion lattice-mass lower bound**:
if the pseudo-mass comparison with `-log(βJ·2d)` is verified on
`cubicExhaustion d`, then the target-exhaustion pseudo-mass is bounded above
by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-- **Cubic-reference profile bound gives an arbitrary-exhaustion lattice-mass lower bound**:
if the cubic exhaustion supplies the profile lower bound at the
high-temperature rate, then the target-exhaustion pseudo-mass is bounded above
by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-! ## Moved: latticeMass_pos pseudoMassFromParamsAtPair_cubic wrappers

The two wrappers
`latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate`,
`latticeMass_pos_of_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`
now live in `LatticeMassPseudoMassTransferCubicPos.lean`. -/


end Ambient

end IsingModel
