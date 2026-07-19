import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.PseudoMass
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReference
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReferencePos

/-!
# Lattice-mass: cubic_pseudoMassFromParamsAtPair variants

Narrow child module for the §17.5 cubic_pseudoMassFromParamsAtPair
variant wrappers (6 theorems specialising the reference-form variants
to `cubicExhaustion d`):
`HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_*`,
`latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_*`, and
`latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_*`. The
theorem names are unchanged from the former
`LatticeMassPseudoMassTransfer` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Cubic pseudo-mass itself is a target validating rate**:
if the pseudo-mass/high-temperature-rate comparison is verified on
`cubicExhaustion d`, then that cubic pseudo-mass value is a validating
`HasExponentialDecay` rate for any target exhaustion `Λ`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-! ## Moved: HasExponentialDecay corr-profile wrapper

`HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr`
now lives in `LatticeMassPseudoMassTransferCubicPseudoMassCorr.lean`. -/


/-- **Cubic pseudo-mass lower bound on arbitrary-exhaustion lattice mass**:
under the cubic-reference comparison with `-log(βJ·2d)`, the cubic pseudo-mass
value itself is bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hle_cubic

/-! ## Moved: latticeMass_ge corr-profile wrapper

`latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr`
now lives in `LatticeMassPseudoMassTransferCubicPseudoMassCorr.lean`. -/


/-- **Positive target lattice mass from a positive cubic pseudo-mass**:
if the cubic-reference pseudo-mass is positive and no larger than the
high-temperature rate, then the target `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos_cubic : 0 < pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle_cubic : pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hpos_cubic hle_cubic

/-! ## Moved: latticeMass_pos corr-profile wrapper

`latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`
now lives in `LatticeMassPseudoMassTransferCubicPseudoMassCorr.lean`. -/


end Ambient

end IsingModel
