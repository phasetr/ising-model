import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReferencePos

/-!
# Concrete cubic-pseudoMass corr-profile wrappers

Narrow child module for the 3 ℤ^d cubic-pseudoMass
`_pseudoMassG_le_corr` profile wrappers:

* `HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr`,
* `latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr`,
* `latticeMass_pos_of_cubic_pseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr`.

Each result is a thin composition wrapper around the
`*_reference_pseudoMassFromParamsAtPair_of_exhaustion_pseudoMassG_le_corr`
lemma at the cubic exhaustion.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


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


end Ambient

end IsingModel
