import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Cubic anchored pseudo-mass ENNReal positivity wrappers

Narrow child module for three ℤ^d
`cubicOriginPseudoMassFromParamsAtPair_*_corr_mem` ENNReal positivity /
nonzero wrappers (active-range membership rules out zero). Each
wrapper is a thin pass-through to the corresponding ambient lemma.
-/

namespace IsingModel
namespace Ambient

/-- **Anchored cubic named pseudo-mass nonzero from cubic active range**:
strict positivity from active-range membership rules out zero.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≠ 0 :=
  ne_of_gt (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    hα hr hcorr_cubic)

/-- **Positive `ENNReal.ofReal` named rate from cubic active range**:
active-range membership makes the named anchored cubic pseudo-mass strictly
positive after coercion to `ENNReal`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    0 < ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  ENNReal.ofReal_pos.mpr
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)

/-- **Nonzero `ENNReal.ofReal` named rate from cubic active range**:
the positive coercion supplied by active-range membership is nonzero. -/
theorem ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≠ 0 :=
  ne_of_gt
    (ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)


end Ambient
end IsingModel
