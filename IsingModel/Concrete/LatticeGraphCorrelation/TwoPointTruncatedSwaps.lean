/- TwoPointTruncatedSwaps.lean
Narrow child module for the 6 ℤ^d `truncated3Infinite_latticeGraph_swap_{ij,jk,ik}`
and `truncated4Infinite_latticeGraph_swap_{ij,jk,kl}` symmetry wrappers,
extracted from `TwoPoint.lean` in PR #2027. The theorem names are
unchanged from the former `TwoPoint` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

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

/-- **ℤ^d `truncated4Infinite` swap symmetries** (adjacent swaps). -/
theorem truncated4Infinite_latticeGraph_swap_ij
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p j i k l :=
  truncated4Infinite_swap_ij (IsingModel.latticeGraph d) Λ p i j k l

theorem truncated4Infinite_latticeGraph_swap_jk
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i k j l :=
  truncated4Infinite_swap_jk (IsingModel.latticeGraph d) Λ p i j k l

theorem truncated4Infinite_latticeGraph_swap_kl
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i j l k :=
  truncated4Infinite_swap_kl (IsingModel.latticeGraph d) Λ p i j k l

end Ambient

end IsingModel
