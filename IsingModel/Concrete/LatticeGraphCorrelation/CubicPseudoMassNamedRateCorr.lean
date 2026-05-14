import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Cubic anchored pseudo-mass named-rate bridges via cubic-correlation lower bounds

Narrow child module for 17 named-rate / latticeMass / Icc / Ioc
wrappers driven by cubic-correlation comparisons. Includes the
`*_of_cubic_pseudoMassG_le_corr`,
`*_of_cubic_corr_mem_le_high_temp_rate`,
`cubicNamedRate_decay_mem_*_of_cubic_pseudoMassG_le_corr`,
`cubicNamedRate_decay_mem_*_of_le_high_temp_rate`,
`cubicNamedRate_decay_mem_Ioc_of_pos_le_high_temp_rate`, and
`cubicNamedRate_decay_mem_Ioc_of_corr_mem_le_high_temp_rate` families.
Theorem names are unchanged from the former
`CubicPseudoMassNamedRate` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **Anchored cubic named rate validates high-temperature decay from a cubic
profile lower bound**: the named-rate comparison supplied by the cubic profile
input feeds the conditional named-rate bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Anchored cubic named pseudo-mass lower bound from a cubic profile lower
bound**: under the profile condition, the named anchored cubic pseudo-mass is
bounded above by the target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Target lattice-mass closed interval from a cubic profile lower bound**:
the cubic profile comparison places the `ENNReal.ofReal` named rate in
`[0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨zero_le _,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic⟩

/-! ## Moved: cubic named-rate corr positivity wrappers

The three positivity wrappers
(`latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`,
`cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubic_pseudoMassG_le_corr`,
`latticeMass_ne_zero_of_cubicOriginPseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`)
now live in `CubicPseudoMassNamedRateCorrPos.lean`. -/



/-! ## Moved: cubic ENNReal positivity / nonzero wrappers

The three wrappers
`cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem`,
`ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem`, and
`ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem`
now live in `CubicPseudoMassNamedRateCorrENNReal.lean`. -/

/-! ## Moved: cubic named-rate corr-mem + high-temp-rate wrappers

The three wrappers
`latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_corr_mem_le_high_temp_rate`,
`cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_corr_mem_le_high_temp_rate`,
`latticeMass_ne_zero_of_cubic_corr_mem_le_high_temp_rate` now live in
`CubicPseudoMassNamedRateCorrMem.lean`. -/


/-! ## Moved: cubic named-rate decay-plus-interval bundles

The five `cubicNamedRate_decay_mem_*` bundle wrappers
(`Icc_of_le_high_temp_rate`, `Ioc_of_pos_le_high_temp_rate`,
`Icc_of_cubic_pseudoMassG_le_corr`, `Ioc_of_cubic_pseudoMassG_le_corr`,
`Ioc_of_corr_mem_le_high_temp_rate`) now live in
`CubicPseudoMassNamedRateCorrDecay.lean`. -/




end Ambient

end IsingModel
