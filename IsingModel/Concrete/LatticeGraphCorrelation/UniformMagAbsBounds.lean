import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d absolute / neg / sq bounds wrappers

Narrow child module for 13 ℤ^d wrappers covering pointwise
`|correlation*| ≤ 1`, `|magnetization*| ≤ 1`,
`-1 ≤ correlation*` / `-1 ≤ magnetization*`, and
`correlation*_sq_le_one` for the Λ / AlongExhaustion / Infinite
families on `latticeGraph d`. Theorem names are unchanged from the
former `UniformMag` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise `|correlationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d pointwise `|magnetizationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ≤ 1 :=
  abs_magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `|correlationInfinite| ≤ 1`** (unconditional). -/
theorem abs_correlationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    |correlationInfinite (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** (unconditional). -/
theorem abs_magnetizationInfinite_latticeGraph_le_one_unconditional
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-! ## Moved: `neg_one_le_correlation*_latticeGraph` wrappers

The three wrappers
`neg_one_le_correlationΛ_latticeGraph`,
`neg_one_le_correlationAlongExhaustion_latticeGraph`,
`neg_one_le_correlationInfinite_latticeGraph` now live in
`UniformMagAbsBoundsNegOneCorr.lean`. -/


/-! ## Moved: correlation² ≤ 1 and -1 ≤ magnetization* wrappers

The six wrappers
`correlation{Λ,AlongExhaustion,Infinite}_latticeGraph_sq_le_one` and
`neg_one_le_magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph`
now live in `UniformMagAbsBoundsSqAndNegOneMag.lean`. -/




end Ambient

end IsingModel
