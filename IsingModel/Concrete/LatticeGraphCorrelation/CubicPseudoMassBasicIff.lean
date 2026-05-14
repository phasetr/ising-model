import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic

/-!
# Anchored cubic pseudo-mass `_iff` transport wrappers

Narrow child module for six ℤ^d
`cubicOriginPseudoMassFromParamsAtPair_*_iff` transport wrappers
extracted from `CubicPseudoMassBasic.lean`. Each rewrites the named
anchored cubic pseudo-mass against the underlying concrete
`pseudoMassFromParamsAtPair` expression.

* `_le_iff`, `_lt_iff`, `_eq_iff`, `_ge_iff`, `_gt_iff`, `_ne_iff`.
-/

namespace IsingModel
namespace Ambient

/-- Transport a `≤` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤ t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z ≤ t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-! ## Moved: cubicOriginPseudoMassFromParamsAtPair_lt_iff

The strict-`<` transport wrapper now lives in
`CubicPseudoMassBasicIffStrict.lean`. -/


/-- Transport equality between the named anchored cubic pseudo-mass and the
underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_eq_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z = t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z = t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport a `≥` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ge_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    t ≤ cubicOriginPseudoMassFromParamsAtPair hα hr β J z ↔
      t ≤ pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-! ## Moved: cubicOriginPseudoMassFromParamsAtPair_{gt,ne}_iff

The strict-`>` and non-equality transport wrappers now live in
`CubicPseudoMassBasicIffStrict.lean`. -/

end Ambient
end IsingModel
