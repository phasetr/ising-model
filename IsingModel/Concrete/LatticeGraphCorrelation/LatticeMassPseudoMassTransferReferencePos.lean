import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReference

/-!
# ℤ^d positivity of the target lattice mass from the reference pseudo-mass (§17.5)

Instantiates at `IsingModel.latticeGraph d`, at zero external field, the strict positivity of
the lattice mass of a target `Ambient.Exhaustion` `Λ` obtained from the pseudo-mass of a
reference exhaustion `Λ₀`. The positivity is given in a form driven by the numerical
comparison of the reference pseudo-mass with the transferred high-temperature rate, and in a
form driven by the profile lower bound on the reference pair correlation. Each form assumes
`1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β`, that `β * J * (2 * d)` is below one, and a `Fintype`
instance on the induced edge sets along the reference exhaustion only, not along the target
one. The comparison-driven form assumes in addition strict positivity of the reference
pseudo-mass; the profile-driven form does not, obtaining positivity instead from the
reference pair correlation lying in `Set.Ioo 0 2`.
-/

namespace IsingModel
namespace Ambient

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


end Ambient
end IsingModel
