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
# Lattice-mass pseudo-mass transfer bridges at ℤ^d

This module contains the concrete §17.1 / §17.5 bridge layer split from the
legacy `Inequalities` module: Step 127 product summability bounds, critical
inverse temperature wrappers, high-temperature decay transfer to arbitrary
exhaustions, pseudo-mass comparison bridges, and below-critical cluster /
summability consequences.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient


/-! ## Moved: Step 127 summability + criticalInverseTemp foundations

The §17.5 Step 127 Lebowitz-exponential product summability bounds and
§17.1 / §17.5 criticalInverseTemp foundations now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: HasExponentialDecay transfer + high-temp exhaustion

The 5 `HasExponentialDecay_*_transfer*` and
`latticeMass_*_high_temp_exhaustion` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: pseudoMassFromParamsAtPair basic comparison wrappers

The 7 basic §17.5 pseudoMassFromParamsAtPair comparison +
latticeMass_ge / latticeMass_pos wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: pseudoMassFromParamsAtPair exhaustion variants

The 6 exhaustion-variant pseudoMassFromParamsAtPair wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExhaustion`.
The legacy import path is preserved by re-importing the new child.
-/

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

/-- **Reference pseudo-mass itself is a target validating rate**:
if the pseudo-mass/high-temperature-rate comparison is verified on a reference
exhaustion `Λ₀`, then that reference pseudo-mass value is also a validating
`HasExponentialDecay` rate for the target exhaustion `Λ`.

This is the direct reference-rate form of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`;
it only needs the numerical comparison of the reference pseudo-mass with the
transferred high-temperature rate.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle₀
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Reference pseudo-mass is a target validating rate from a profile bound**:
if the reference-exhaustion correlation dominates `pseudoMassG` at the
transferred high-temperature rate, then that reference pseudo-mass value is a
valid decay rate for the target exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Reference pseudo-mass lower bound on target lattice mass**:
under the reference-exhaustion high-temperature comparison, the reference
pseudo-mass value itself is bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ₀
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ₀ _ x z)
    (HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Reference pseudo-mass lower bound on target lattice mass from a profile bound**:
if the reference-exhaustion correlation dominates `pseudoMassG` at the
transferred high-temperature rate, then the reference pseudo-mass value is
bounded above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ₀
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Positive target lattice mass from a positive reference pseudo-mass**:
if the reference pseudo-mass is positive and no larger than the high-temperature
rate, then the target `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hpos₀ : 0 < pseudoMassFromParamsAtPair hα hr d Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos₀
    (HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Positive target lattice mass from a reference profile lower bound**:
the reference active-range hypothesis makes the reference pseudo-mass positive,
and the profile lower bound supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr₀ : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile₀ : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr₀)
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

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

/-- **Cubic pseudo-mass is a target validating rate from a profile bound**:
the specialization of
`HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr`
with `cubicExhaustion d` as the reference exhaustion.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
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
      (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

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

/-- **Cubic pseudo-mass lower bound on target lattice mass from a profile bound**:
if the cubic exhaustion supplies the profile lower bound at the
high-temperature rate, then the cubic pseudo-mass value itself is bounded
above by the target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
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
        (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

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

/-- **Positive target lattice mass from a cubic profile lower bound**:
the cubic active-range hypothesis makes the cubic pseudo-mass positive, and
the cubic profile lower bound supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
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
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_reference_pseudoMassFromParamsAtPair_exhaustion_pseudoMassG_le_corr
    hα hr Λ (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic

/-- **Tanh-power profile bound implies the cubic pair-correlation profile bound**:
the existing path lower bound
`tanh(βJ) ^ latticeDistance d 0 z ≤ twoPointFunction d ⟨J,0,β⟩ z`
turns the numerical condition
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ latticeDistance d 0 z`
into the cubic-exhaustion correlation lower bound required by the
profile-comparison bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
    {α d : ℕ} {r β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} := by
  have hpow_le_corr :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} := by
    change Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z ≤
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z
    exact twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz
  exact hprofile_tanh.trans hpow_le_corr

/-- **Cubic pair correlation is positive from a tanh-power profile bound**:
under the high-temperature hypothesis, the Lean real-log rate `-log(βJ·2d)` is
nonnegative, so `pseudoMassG` is positive at that rate.  Combining this
positivity with the tanh-power reduction gives positivity of the anchored cubic
pair correlation.

This supplies the lower half of the active-range input used by the
profile-comparison bridge toward GJ §17.5 Lemma 17.5.2.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr)
    (pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
      (α := α) (d := d) (r := r) (β := β) (J := J)
      hJ hβ (z := z) hz hprofile_tanh)

set_option maxHeartbeats 2000000 in
-- The totalized proof splits on active-interval membership and reuses the
-- implicit pseudo-mass comparison, which is heavier than the surrounding wrappers.
/-- **Two-point pseudo-mass extension comparison from a tanh-power profile bound**:
the tanh-power lower-bound reduction supplies the profile comparison whenever
the anchored two-point function is in the active interval.  Outside the active
interval, `pseudoMassExt` is zero, so the high-temperature comparison is
automatic from nonnegativity of the Lean real-log rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  by_cases hcorr : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2
  · rw [pseudoMassExt_of_mem hα hr hcorr]
    exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two
  · rw [pseudoMassExt_of_not_mem hα hr hcorr]
    exact hrate_nonneg

/-- **Two-point active range from a tanh-power profile bound**: the same
tanh-power lower-bound reduction used for the totalized comparison also proves
that the anchored two-point function lies in the pseudo-mass active interval
`(0,2)`.  The lower endpoint comes from positivity of `pseudoMassG` at the
Lean total real-log rate; the upper endpoint uses the universal bound
`twoPointFunction ≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  constructor
  · exact lt_of_lt_of_le (pseudoMassG_pos α hrate_nonneg hr) hprofile_two
  · exact lt_of_le_of_lt
      (twoPointFunction_le_one d (⟨J, 0, β⟩ : IsingParams ℝ) z) one_lt_two

/-- **Ordinary two-point pseudo-mass comparison from a tanh-power profile bound**:
once the tanh-power profile bound places the anchored two-point function in
`(0,2)`, the implicit pseudo-mass comparison gives the non-totalized
`pseudoMass` bound by the high-temperature rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_le_high_temp_rate_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)
      ≤ -Real.log (β * J * ↑(2 * d)) := by
  have hβJd_nonneg : 0 ≤ β * J * ↑(2 * d) := by
    exact mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hβJd_nonneg hlt.le)
  have hcorr :
      twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z ∈ Set.Ioo (0 : ℝ) 2 :=
    twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh
  have hprofile_two :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z :=
    hprofile_tanh.trans (twoPointFunction_ge_tanh_betaJ_pow_dist hJ hβ hz)
  exact (pseudoMass_le_iff_pseudoMassG_le hα hr hcorr hrate_nonneg).mpr hprofile_two

/-- **The totalized two-point pseudo-mass equals the ordinary pseudo-mass under
the tanh-power profile bound**: the profile condition supplies the active-range
membership needed to remove the totalization.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_eq_pseudoMass_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) =
      pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) := by
  rw [pseudoMassExt_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)]

/-- **Ordinary two-point pseudo-mass positivity from a tanh-power profile
bound**: the active-range theorem supplies the `Ioo 0 2` argument required by
`pseudoMass_pos`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMass hα hr
      (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
        (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) :=
  pseudoMass_pos hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass positivity from a tanh-power profile
bound**: under the profile condition, the anchored two-point function is active,
so `pseudoMassExt` is strictly positive.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) :=
  pseudoMassExt_pos_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass non-vanishing from a tanh-power profile
bound**: a direct non-zero corollary of positivity.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) ≠ 0 :=
  ne_of_gt
    (pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
      hα hr hJ hβ hlt hz hprofile_tanh)

/-- **Cubic pair active range from a tanh-power profile bound**:
the tanh-power reduction supplies a positive lower bound on the anchored cubic
pair correlation, and the universal correlation bound gives the upper endpoint
`< 2`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact lt_of_le_of_lt
      (Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ)))
      one_lt_two

/-- **Cubic pair correlation is nonzero from a tanh-power profile bound**:
positivity of the anchored cubic pair correlation rules out zero.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ≠ 0 :=
  ne_of_gt
    (correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh)

/-- **Cubic pair correlation is in `(0,1]` from a tanh-power profile bound**:
the tanh-power hypothesis gives positivity, while boundedness of correlations
gives the endpoint `≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ))

/-- **Cubic pair correlation is strictly below two from a tanh-power profile
bound**: this is the upper endpoint of the active interval package.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_lt_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} < 2 :=
  (correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh).2

/-- **Cluster property holds below the critical inverse temperature** (GJ §17.1):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the
cluster property holds for any exhaustion `Λ`:
```
clusterProperty (latticeGraph d) Λ ⟨J, 0, β⟩.
```

**Physics**: the hypothesis `β < β_c` is the **high-temperature** regime
(equivalently, above the critical temperature `T_c = 1/β_c`). In this regime,
the connected 2-point function decays exponentially: for all `i, j`,
`|⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩|` decays to zero as `|i - j| → ∞`. This is the
GJ §17.1 high-temperature clustering consequence for the Ising model analog.

**Proof strategy**:
* `β = 0`: `clusterProperty_latticeGraph_beta_zero` (trivial slice).
* `β > 0`: use `latticeMass_pos_of_lt_criticalInverseTemp` to get `m > 0`,
  extract a positive rate `α` via `HasExponentialDecay_of_latticeMass_pos`,
  transfer the decay from `cubicExhaustion d` to `Λ` via
  `HasExponentialDecay_transfer_exhaustion` (uses `Ferromagnetic`), and
  conclude by `clusterProperty_latticeGraph_of_HasExponentialDecay`. -/
theorem clusterProperty_latticeGraph_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    clusterProperty (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · exact clusterProperty_beta_zero (IsingModel.latticeGraph d) Λ J 0
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl _, hβ_pos⟩
    have hα_decay' : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ) :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    exact clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos hα_decay'

/-- **Summability of truncated 2-point below critical inverse temperature** (GJ §17.1/§17.5):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the truncated
2-point function is summable:
`Summable (fun j => truncated2Infinite (latticeGraph d) Λ ⟨J, 0, β⟩ i j)`.

This extends `truncated2Infinite_summable_of_high_temp` (βJD < 1 case, PR #903) to the
full below-β_c regime, giving a per-site finite-susceptibility result for all high-temperature
couplings (not just the Simon-Lieb high-temperature range).

**Proof**: β = 0 gives `U_2 = 0` (summable trivially). For β > 0: `latticeMass > 0`
(via `latticeMass_pos_of_lt_criticalInverseTemp`) → extract `α > 0` and
`HasExponentialDecay` (via `HasExponentialDecay_of_latticeMass_pos`) → transfer to `Λ`
(via `HasExponentialDecay_transfer_exhaustion`) → `|U_2(i,j)| ≤ C·exp(-α·d(i,j))` for
`i ≠ j` and `U_2(i,i) = 0` (Z₂ symmetry) → `summable_exp_neg_dist` + nonneg bound
→ `Summable.of_nonneg_of_le`. -/
theorem truncated2Infinite_summable_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp only [truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J 0]
    exact summable_zero
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl _, hβ_pos⟩
    obtain ⟨C, hC, hbound⟩ :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    apply Summable.of_nonneg_of_le
        (fun j => truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ _ hf i j)
        (fun j => ?_)
        ((summable_exp_neg_dist hα_pos d i).mul_left C)
    by_cases hij : i = j
    · subst hij
      rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β i i]
      simp only [Finset.pair_eq_singleton]
      rw [Ambient.correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β {i} (by simp)]
      exact mul_nonneg hC (Real.exp_nonneg _)
    · exact le_trans (le_abs_self _) (hbound i j hij)

end Ambient
end IsingModel
