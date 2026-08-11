import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Adjacent-transposition symmetry of the ℤ^d four-point truncated function

For `IsingModel.latticeGraph d`, an arbitrary exhaustion `Λ` of `Fin d → ℤ`, an arbitrary
parameter record `p : IsingParams ℝ` and arbitrary sites, the value of `truncated4Infinite` is
unchanged by each transposition of adjacent site arguments: the first with the second, the second
with the third, and the third with the fourth. Adjacent transpositions generate the symmetric
group on four letters, so these are the generating cases of full permutation symmetry of the
truncation in its sites.

Each is the specialization of the corresponding ambient swap statement to
`IsingModel.latticeGraph d`.
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
