import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncatedInfinite_latticeGraph wrappers

Narrow child module for ℤ^d `truncated2Infinite_latticeGraph_*`
nonneg wrappers and the `correlationInfinite` comparison.
Trivial-slice / symmetry / h-zero wrappers now live in
`TwoPointTruncatedInfiniteTrivialSlice.lean`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d truncated2Infinite nonneg** (general). -/
theorem truncated2Infinite_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i j :=
  truncated2Infinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf i j

/-- **ℤ^d truncated2Infinite nonneg at distinct sites**. -/
theorem truncated2Infinite_latticeGraph_nonneg_of_ne
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i j :=
  truncated2Infinite_nonneg_of_ne (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf hij

/-- **ℤ^d truncated2Infinite nonneg on diagonal**. -/
theorem truncated2Infinite_latticeGraph_nonneg_of_eq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i i :=
  truncated2Infinite_nonneg_of_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf i

/-- **ℤ^d `truncated2Infinite ≤ correlationInfinite {i, j}`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_correlationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
  truncated2Infinite_le_correlationInfinite (IsingModel.latticeGraph d) Λ p hf i j

/-! ## Moved: trivial-slice / symmetry / h-zero wrappers

The five wrappers
`truncated2Infinite_latticeGraph_{J_zero_of_ne, J_zero_diagonal, beta_zero, symm, h_zero}`
now live in `TwoPointTruncatedInfiniteTrivialSlice.lean`. -/



end Ambient

end IsingModel
