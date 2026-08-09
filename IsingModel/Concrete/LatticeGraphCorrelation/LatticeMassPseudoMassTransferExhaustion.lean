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

/-!
# ℤ^d reference-exhaustion hypotheses with target-exhaustion conclusions (§17.5)

Instantiates at `IsingModel.latticeGraph d`, at zero external field, the transfer in which
the hypotheses are verified on a reference `Ambient.Exhaustion` `Λ₀` while the conclusion
concerns a target exhaustion `Λ`: the pseudo-mass computed with the target exhaustion is a
validating exponential-decay rate for it, and its `ENNReal.ofReal` value is a lower bound for
the target lattice mass. Each conclusion is reached in a form driven by the numerical
comparison of the reference pseudo-mass with the transferred high-temperature rate, and in a
form driven by the profile lower bound on the reference pair correlation. Every statement
assumes `1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β`, that `β * J * (2 * d)` is below one, and a
`Fintype` instance on the induced edge sets along the target exhaustion as well as along the
reference one; the profile-driven forms assume the correlation range and the profile bound on
the reference exhaustion only.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Reference-exhaustion pseudo-mass comparison transfers to a target exhaustion**:
if the concrete pair pseudo-mass computed with a reference exhaustion `Λ₀` is
bounded above by the transferred Simon--Lieb high-temperature rate
`-log(βJ·2d)`, then the pseudo-mass computed with the target exhaustion `Λ`
is a validating `HasExponentialDecay` rate.

The proof uses exhaustion-independence of `pseudoMassFromParamsAtPair` under
ferromagnetic parameters, then applies
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have hpm : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ Λ₀
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hle : pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d)) := by
    simpa [hpm] using hle₀
  exact HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt hle

/-- **Reference-exhaustion profile bound validates the target pseudo-mass**:
if a reference exhaustion supplies the profile lower bound at the
high-temperature rate, the resulting reference comparison transfers to the
target pseudo-mass by exhaustion-independence.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
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
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

/-- **Reference-exhaustion comparison gives a target-exhaustion lattice-mass lower bound**:
under the comparison of the reference pseudo-mass with the high-temperature
rate, the target-exhaustion pseudo-mass is bounded by the target
`latticeMass`.

This is the `latticeMass` consequence of
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ₀.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hle₀ : pseudoMassFromParamsAtPair hα hr d Λ₀
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z)
    (HasExponentialDecay_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
      hα hr Λ Λ₀ hJ hβ hlt hle₀)

/-- **Reference-exhaustion profile bound gives a target lattice-mass lower bound**:
the profile lower bound on the reference exhaustion supplies the reference
comparison with `-log(βJ·2d)`, and hence bounds the target pseudo-mass by the
target `latticeMass`.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ Λ₀ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
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
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_exhaustion_le_high_temp_rate
    hα hr Λ Λ₀ hJ hβ hlt
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr Λ₀ hJ hβ hlt hcorr₀ hprofile₀)

end Ambient

end IsingModel
