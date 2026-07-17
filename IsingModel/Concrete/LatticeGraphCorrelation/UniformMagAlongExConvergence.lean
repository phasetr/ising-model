import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationAlongExhaustion + correlationAlongExhaustion bounds + convergence wrappers

Narrow child module for 17 ℤ^d wrappers covering
`magnetizationAlongExhaustion_latticeGraph_*` and
`correlationAlongExhaustion_latticeGraph_*` bound / monotone /
convergent / bddAbove / bddBelow / `_le_*Infinite` / `_tendsto_ciSup`
/ `_eq_ciSup` and `tendsto_magnetizationAlongExhaustion_*Infinite`
wrappers on `latticeGraph d`. Theorem names are unchanged from the
former `UniformMag` declarations.
-/

namespace IsingModel
namespace Ambient


/-! ## Moved: magnetizationAlongEx basic per-stage bound wrappers

The three wrappers
`magnetizationAlongExhaustion_latticeGraph_le_one`,
`magnetizationAlongExhaustion_latticeGraph_nonneg`,
`magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite`
now live in `UniformMagAlongExConvergenceBasicBounds.lean`. -/


/-! ## Moved: magnetizationAlongEx tendsto / convergent / monotone wrappers

The three wrappers
`tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph`,
`magnetizationAlongExhaustion_latticeGraph_convergent`,
`magnetizationAlongExhaustion_latticeGraph_monotone` now live in
`UniformMagAlongExConvergenceMain.lean`. -/


/-- **ℤ^d `magnetizationAlongExhaustion` bounded above** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddAbove (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p i

/-! ## Moved: correlationAlongExhaustion bound / monotone / convergent wrappers

The four wrappers
`correlationAlongExhaustion_latticeGraph_{bddBelow,bddAbove,monotone,convergent}`
now live in `UniformMagAlongExConvergenceCorrAlongEx.lean`. -/


/-- **ℤ^d `magnetizationAlongExhaustion` bounded below** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddBelow (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationAlongExhaustion → ⨆ n ...** (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p i n)) :=
  magnetizationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf i

/-! ## Moved: ciSup / pointwise-le wrappers (magnetization / correlation)

The four wrappers
`magnetizationInfinite_latticeGraph_eq_ciSup`,
`correlationInfinite_latticeGraph_eq_ciSup`,
`correlationAlongExhaustion_le_correlationInfinite_latticeGraph`,
`magnetizationAlongExhaustion_le_magnetizationInfinite_latticeGraph`
now live in `UniformMagAlongExConvergenceCiSup.lean`. -/



end Ambient

end IsingModel
