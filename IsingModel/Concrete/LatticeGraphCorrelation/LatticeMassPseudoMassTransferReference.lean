import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic

/-!
# ℤ^d the reference pseudo-mass as a rate for the target exhaustion (§17.5)

Instantiates at `IsingModel.latticeGraph d`, at zero external field, the variant in which the
value transported to the target exhaustion is the pseudo-mass of the reference exhaustion
itself: that value validates the exponential-decay predicate for the target exhaustion `Λ`,
and its `ENNReal.ofReal` image is a lower bound for the lattice mass of `Λ`. Each conclusion
is reached in a form driven by the numerical comparison of the reference pseudo-mass with the
transferred high-temperature rate, and in a form driven by the profile lower bound on the
reference pair correlation. Every statement assumes `1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β` and
that `β * J * (2 * d)` is below one, and requires a `Fintype` instance on the induced edge
sets along the reference exhaustion only, not along the target one.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
