import IsingModel.TranslationInvariance
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `correlation² ≤ 1` and `-1 ≤ magnetization*` wrappers

Narrow child module for six ℤ^d wrappers extracted from
`UniformMagAbsBounds.lean`: `correlation{Λ,AlongExhaustion,Infinite}_sq_le_one`
and `neg_one_le_magnetization{Λ,AlongExhaustion,Infinite}`. Each wrapper is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationΛ² ≤ 1`**. -/
theorem correlationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion² ≤ 1`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ^ 2 ≤ 1 :=
  correlationAlongExhaustion_sq_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationInfinite² ≤ 1`**. -/
theorem correlationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-! ## Moved: `neg_one_le_magnetization*_latticeGraph` wrappers

The three wrappers
`neg_one_le_magnetizationΛ_latticeGraph`,
`neg_one_le_magnetizationAlongExhaustion_latticeGraph`,
`neg_one_le_magnetizationInfinite_latticeGraph` now live in
`UniformMagAbsBoundsNegOneMag.lean`. -/


end Ambient
end IsingModel
