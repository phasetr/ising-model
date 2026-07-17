import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete cubicExhaustion-specific correlationAlongEx bound wrappers

Narrow child module for 4 ℤ^d cubicExhaustion-specific
`correlationAlongExhaustion_latticeGraph_*` bound wrappers extracted
from `CorrelationExhaustionLimitsBounds.lean`:

* `correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove`,
* `abs_correlationAlongExhaustion_latticeGraph_eventually_le_one`,
* `correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one`,
* `correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg`.

Each is a thin pass-through to the ambient
`correlationAlongExhaustion_{bddAbove,eventually_le_one,le_one,nonneg}`
lemma at `(G, Λ) := (IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`.
The theorem names are unchanged from the former
`CorrelationExhaustionLimitsBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion range is bddAbove**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually**. -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d correlationAlongExhaustion ≤ 1** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A n

/-- **ℤ^d correlationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A n

end Ambient
end IsingModel
