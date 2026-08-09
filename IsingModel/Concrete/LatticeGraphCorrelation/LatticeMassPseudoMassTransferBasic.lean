import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay

/-!
# ℤ^d comparison of the pair pseudo-mass with the high-temperature rate

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` at zero external field, the step that turns a lower bound on the infinite-volume
pair correlation by the pseudo-mass profile into a bound of the concrete pair pseudo-mass by
the transferred high-temperature rate `-log (β * J * (2 * d))`, and the step that turns such
a bound into the statement that the pseudo-mass is itself a validating exponential-decay
rate, in the form driven by the numerical comparison and in the form driven by the profile
bound. Every statement assumes `1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β` and that `β * J * (2 * d)`
is below one. The profile-driven statements assume in addition that the pair correlation lies
in `Set.Ioo 0 2` and dominates the profile at that rate, while the statement driven by the
numerical comparison assumes only that comparison.
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

end Ambient

end IsingModel
