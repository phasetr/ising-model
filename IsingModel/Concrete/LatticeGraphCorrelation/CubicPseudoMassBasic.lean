import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# Basic anchored cubic pseudo-mass names

This module contains the lightweight anchored cubic pseudo-mass abbreviations,
named profile predicates, and comparison transport lemmas used by the larger
`CubicPseudoMass` capstone module. It is split out so downstream code that only
needs the names can avoid importing the full capstone stack.
-/

namespace IsingModel
namespace Ambient

/-- **Anchored cubic pseudo-mass abbreviation**: the concrete
`pseudoMassFromParamsAtPair` value for the cubic exhaustion at the anchored
pair `(0,z)` and zero external field.

This definition is intended to keep downstream theorem statements from
restating the high-arity concrete pseudo-mass expression.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
noncomputable def cubicOriginPseudoMassFromParamsAtPair {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) : ℝ :=
  pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) 0 z

/-- The anchored cubic pseudo-mass abbreviation unfolds to the corresponding
`pseudoMassFromParamsAtPair` value. -/
theorem cubicOriginPseudoMassFromParamsAtPair_eq {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z =
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z :=
  rfl

/-- **Anchored cubic pseudo-mass nonnegativity**. -/
theorem cubicOriginPseudoMassFromParamsAtPair_nonneg {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) :
    0 ≤ cubicOriginPseudoMassFromParamsAtPair hα hr β J z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]
  exact pseudoMassFromParamsAtPair_nonneg hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) 0 z

/-- **Anchored cubic named-rate high-temperature comparison proposition**:
lightweight named proposition for the heavy comparison
`cubicOriginPseudoMassFromParamsAtPair ≤ -log(βJ·2d)`.

Keeping the comparison as an irreducible `Prop` avoids placing the full concrete
named-rate expression directly in downstream theorem conclusions, where direct
`cubicTanhProfileBound` wrappers trigger deterministic elaboration timeouts.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
@[irreducible] def cubicOriginNamedRateLeHighTemp {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) : Prop :=
  cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
    -Real.log (β * J * ↑(2 * d))

/-- **Cubic truncated two-point product summand**: the product
`U₂(x,w) * U₂(y,w)` on the cubic exhaustion at zero external field.

This definition keeps downstream summability statements from repeatedly
unfolding the full cubic-exhaustion `truncated2Infinite` product. -/
noncomputable def cubicTruncated2Product (d : ℕ) (β J : ℝ)
    (x y w : Fin d → ℤ) : ℝ :=
  Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x w *
    Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) y w

/-- **Anchored cubic tanh-power profile condition**: the lightweight named
predicate
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ dist(0,z)`.

Keeping this condition named avoids repeatedly elaborating the tanh-profile
expression in downstream theorem statements. -/
def cubicTanhProfileBound (α d : ℕ) (r β J : ℝ) (z : Fin d → ℤ) : Prop :=
  pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
    Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z

/-- The named cubic tanh-power profile condition unfolds to the underlying
`pseudoMassG` lower-bound inequality. -/
theorem cubicTanhProfileBound_iff (α d : ℕ) (r β J : ℝ) (z : Fin d → ℤ) :
    cubicTanhProfileBound α d r β J z ↔
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z :=
  Iff.rfl

/-! ## Moved: anchored cubic pseudo-mass `_iff` transport wrappers

The six wrappers
`cubicOriginPseudoMassFromParamsAtPair_le_iff`,
`cubicOriginPseudoMassFromParamsAtPair_lt_iff`,
`cubicOriginPseudoMassFromParamsAtPair_eq_iff`,
`cubicOriginPseudoMassFromParamsAtPair_ge_iff`,
`cubicOriginPseudoMassFromParamsAtPair_gt_iff`,
`cubicOriginPseudoMassFromParamsAtPair_ne_iff` now live in
`CubicPseudoMassBasicIff.lean`. -/


end Ambient
end IsingModel
