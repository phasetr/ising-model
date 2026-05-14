import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic

/-!
# Anchored cubic pseudo-mass strict `_iff` transport wrappers

Narrow child module for 3 ℤ^d strict-comparison
`cubicOriginPseudoMassFromParamsAtPair_*_iff` transport wrappers
extracted from `CubicPseudoMassBasicIff.lean`. Each rewrites the named
anchored cubic pseudo-mass against the underlying concrete
`pseudoMassFromParamsAtPair` expression under a strict comparison.

* `_lt_iff`, `_gt_iff`, `_ne_iff`.
-/

namespace IsingModel
namespace Ambient

/-- Transport a `<` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_lt_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z < t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z < t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport a `>` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_gt_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    t < cubicOriginPseudoMassFromParamsAtPair hα hr β J z ↔
      t < pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport non-equality between the named anchored cubic pseudo-mass and the
underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ne_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≠ t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z ≠ t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

end Ambient
end IsingModel
