import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic

/-!
# Strict and non-equality transport for the origin-anchored cubic pseudo-mass

Rewrites `<`, `>` and `≠` comparisons of the origin-anchored cubic pseudo-mass against a
real threshold into the same comparisons of the underlying `pseudoMassFromParamsAtPair`
expression, so an order fact proved on either side transports to the other without unfolding
the abbreviation. The equivalences hold at arbitrary coupling, inverse temperature,
displacement and threshold.
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
