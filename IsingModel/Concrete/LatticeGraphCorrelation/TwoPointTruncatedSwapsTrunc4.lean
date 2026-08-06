import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `truncated4Infinite_latticeGraph_swap_*` wrappers

Narrow child module for three ℤ^d
`truncated4Infinite_latticeGraph_swap_*` adjacent-swap symmetry
wrappers extracted from `TwoPointTruncatedSwaps.lean`:

* `truncated4Infinite_latticeGraph_swap_ij`,
* `truncated4Infinite_latticeGraph_swap_jk`,
* `truncated4Infinite_latticeGraph_swap_kl`.

Each result is a thin pass-through of the ambient
`Ambient.truncated4Infinite_swap_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `TwoPointTruncatedSwaps` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `truncated4Infinite` swap symmetries** (adjacent swaps). -/
theorem truncated4Infinite_latticeGraph_swap_ij
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p j i k l :=
  truncated4Infinite_swap_ij (IsingModel.latticeGraph d) Λ p i j k l

/-- **ℤ^d `truncated4Infinite` swap symmetry** (adjacent `j ↔ k`). -/
theorem truncated4Infinite_latticeGraph_swap_jk
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i k j l :=
  truncated4Infinite_swap_jk (IsingModel.latticeGraph d) Λ p i j k l

/-- **ℤ^d `truncated4Infinite` swap symmetry** (adjacent `k ↔ l`). -/
theorem truncated4Infinite_latticeGraph_swap_kl
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i j l k :=
  truncated4Infinite_swap_kl (IsingModel.latticeGraph d) Λ p i j k l

end Ambient

end IsingModel
