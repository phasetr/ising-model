import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `truncated{2,3,4}Infinite_latticeGraph_apply` wrappers

Narrow child module for three ℤ^d
`truncated{2,3,4}Infinite_latticeGraph_apply` definitional unfolding
wrappers extracted from `TwoPointTruncatedInfinite.lean`:

* `truncated2Infinite_latticeGraph_apply`,
* `truncated4Infinite_latticeGraph_apply`,
* `truncated3Infinite_latticeGraph_apply`.

Each result is a thin pass-through of the ambient
`Ambient.truncatedNInfinite_apply` definitional unfolding lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `TwoPointTruncatedInfinite` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `truncated2Infinite` apply** (definitional). -/
theorem truncated2Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j} :=
  truncated2Infinite_apply (IsingModel.latticeGraph d) Λ p i j

/-- **ℤ^d `truncated4Infinite` apply** (definitional, pair-split form). -/
theorem truncated4Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j, k, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, l}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, k} :=
  truncated4Infinite_apply (IsingModel.latticeGraph d) Λ p i j k l

/-- **ℤ^d `truncated3Infinite` apply** (definitional). -/
theorem truncated3Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {i, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        + 2 * correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k} :=
  truncated3Infinite_apply (IsingModel.latticeGraph d) Λ p i j k

end Ambient

end IsingModel
