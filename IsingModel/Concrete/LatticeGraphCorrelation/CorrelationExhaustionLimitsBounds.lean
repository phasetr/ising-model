import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete correlationAlongExhaustion bound + eventually wrappers

Narrow child module for six ℤ^d
`correlationAlongExhaustion_latticeGraph_*` bound + eventually +
cubicExhaustion `_le_one` / `_nonneg` wrappers. Each wrapper is a thin
pass-through to the corresponding ambient
`correlationAlongExhaustion_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: cubicExhaustion bddAbove + eventually_le_one wrappers

The two cubicExhaustion-specific wrappers
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove` and
`abs_correlationAlongExhaustion_latticeGraph_eventually_le_one` now
live in `CorrelationExhaustionLimitsBoundsCubic.lean`. -/


/-- **ℤ^d `correlationAlongExhaustion` eventually equals the lifted `correlationΛ`**
(any-Exhaustion): for any finite `A`, eventually `A ⊆ Λ.volume n` and
`correlationAlongExhaustion = correlationΛ` on the lifted set. -/
theorem correlationAlongExhaustion_latticeGraph_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ hA : A ⊆ Λ.volume n,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n =
        correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (Ambient.liftFinset A hA) :=
  correlationAlongExhaustion_eventually (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually** (any-Exhaustion). -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one
    (IsingModel.latticeGraph d) Λ p A

/-! ## Moved: cubicExhaustion per-stage le_one + nonneg wrappers

The two cubicExhaustion-specific per-stage wrappers
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one` and
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg` now
live in `CorrelationExhaustionLimitsBoundsCubic.lean`. -/

end Ambient
end IsingModel
