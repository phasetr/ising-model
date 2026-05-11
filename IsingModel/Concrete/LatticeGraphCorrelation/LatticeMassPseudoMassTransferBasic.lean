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

/-!
# Lattice-mass: pseudoMassFromParamsAtPair basic comparison wrappers

Narrow child module for the basic §17.5 pseudoMassFromParamsAtPair
comparison + latticeMass_ge / latticeMass_pos wrappers (7 theorems):
`pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr`,
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate`,
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`,
`latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate`,
`latticeMass_ge_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`,
`latticeMass_pos_of_pseudoMassFromParamsAtPair_le_high_temp_rate`, and
`latticeMass_pos_of_pseudoMassFromParamsAtPair_pseudoMassG_le_corr`. The
theorem names are unchanged from the former `LatticeMassPseudoMassTransfer`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient


/-- **Pseudo-mass/high-temperature comparison from a profile lower bound**:
if the infinite-volume pair correlation is in the active pseudo-mass range
`Ioo 0 2` and dominates the pseudo-mass profile
`pseudoMassG α r (-log(βJ·2d))`, then the concrete pair pseudo-mass is no
larger than the transferred Simon--Lieb high-temperature rate.

The proof unfolds `pseudoMassFromParamsAtPair`, rewrites `pseudoMassExt` to
`pseudoMass` on `Ioo 0 2`, and applies the implicit characterization
`pseudoMass(c) ≤ t ↔ pseudoMassG α r t ≤ c`. The high-temperature hypotheses
give `0 ≤ -log(βJ·2d)`.

References: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312; Glimm--Jaffe
§5.1 pp. 74--75. -/
theorem pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  unfold pseudoMassFromParamsAtPair
  rw [pseudoMassExt_of_mem hα hr hcorr]
  exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile

/-- **Pseudo-mass validates decay when it is below the high-temperature rate**:
if the concrete pair pseudo-mass is bounded above by the transferred
Simon--Lieb high-temperature rate `-log(βJ·2d)`, then that pseudo-mass itself
is a validating `HasExponentialDecay` rate.

This is the monotonicity step needed after
`HasExponentialDecay_transfer_high_temp`: smaller decay rates give weaker
exponential bounds, so they remain valid.

References: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312; Glimm--Jaffe §5.1
pp. 74--75; Friedli--Velenik Prop. 9.31 p. 428. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Profile lower bound validates the concrete pair pseudo-mass as a decay rate**:
the profile criterion
`pseudoMassG α r (-log(βJ·2d)) ≤ correlationInfinite {x,z}` supplies the
missing comparison with the transferred high-temperature rate, so the concrete
pseudo-mass is itself a valid exponential-decay rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)

/-- **Pseudo-mass lower bound from comparison with the high-temperature rate**:
under the comparison `pseudoMassFromParamsAtPair ≤ -log(βJ·2d)`, the concrete
pseudo-mass is bounded above by `latticeMass`.

This composes the transferred Simon--Lieb high-temperature decay rate, rate
monotonicity of `HasExponentialDecay`, and the `sSup` definition of
`latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z)
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Lattice-mass lower bound from a profile lower bound**:
if the correlation dominates `pseudoMassG` at the transferred
high-temperature rate, then the concrete pair pseudo-mass is bounded above by
`latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)

/-- **Positive lattice mass from positive pseudo-mass below the high-temperature rate**:
if the concrete pair pseudo-mass is positive and no larger than the transferred
Simon--Lieb high-temperature rate, then `latticeMass` is positive.

This is the positivity companion to
`latticeMass_ge_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Positive lattice mass from a profile lower bound**:
the active-range correlation hypothesis makes the concrete pair pseudo-mass
positive, and the profile lower bound supplies the comparison with the
transferred high-temperature rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_pseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr)
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr hprofile)


end Ambient

end IsingModel
