import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `correlationAlongExhaustion` subset / monotone wrappers

Narrow child module for three ℤ^d
`correlationAlongExhaustion_latticeGraph_*` wrappers extracted from
`BaseCorrelationAlongEx.lean`:

* `correlationAlongExhaustion_latticeGraph_of_subset`,
* `correlationAlongExhaustion_latticeGraph_of_not_subset`,
* `correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone`.

Each result is a thin pass-through of the corresponding abstract
`correlationAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `BaseCorrelationAlongEx` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion of_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n
      = correlationΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p (liftFinset A hA) :=
  correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion of_not_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_not_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : ¬ A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n = 0 :=
  correlationAlongExhaustion_of_not_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion stage-index Monotone**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

end Ambient

end IsingModel
