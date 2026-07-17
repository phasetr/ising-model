/- TwoPointTruncatedSwaps.lean
Narrow child module for the 6 ℤ^d `truncated3Infinite_latticeGraph_swap_{ij,jk,ik}`
and `truncated4Infinite_latticeGraph_swap_{ij,jk,kl}` symmetry wrappers,
extracted from `TwoPoint.lean` in PR #2027. The theorem names are
unchanged from the former `TwoPoint` declarations.
-/
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `truncated3Infinite` swap symmetries**. -/
theorem truncated3Infinite_latticeGraph_swap_ij
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p j i k :=
  truncated3Infinite_swap_ij (IsingModel.latticeGraph d) Λ p i j k

theorem truncated3Infinite_latticeGraph_swap_jk
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p i k j :=
  truncated3Infinite_swap_jk (IsingModel.latticeGraph d) Λ p i j k

theorem truncated3Infinite_latticeGraph_swap_ik
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p k j i :=
  truncated3Infinite_swap_ik (IsingModel.latticeGraph d) Λ p i j k

/-! ## Moved: `truncated4Infinite_latticeGraph_swap_*` wrappers

The three wrappers
`truncated4Infinite_latticeGraph_swap_ij`,
`truncated4Infinite_latticeGraph_swap_jk`,
`truncated4Infinite_latticeGraph_swap_kl` now live in
`TwoPointTruncatedSwapsTrunc4.lean`. -/


end Ambient

end IsingModel
