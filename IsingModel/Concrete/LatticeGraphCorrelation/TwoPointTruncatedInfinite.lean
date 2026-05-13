import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d truncatedInfinite_latticeGraph wrappers

Narrow child module for ℤ^d
`truncated{2,3,4}Infinite_latticeGraph_*` apply / nonneg / pointwise
wrappers. Bound wrappers and trivial-slice / symmetry / h-zero
wrappers now live in `TwoPointTruncatedInfiniteBounds.lean` and
`TwoPointTruncatedInfiniteTrivialSlice.lean` respectively.
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

/-- **ℤ^d `truncated2Infinite ≤ correlationInfinite {i, j}`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_correlationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
  truncated2Infinite_le_correlationInfinite (IsingModel.latticeGraph d) Λ p hf i j

/-! ## Moved: truncated2Infinite bound wrappers

The four wrappers
`{truncated2Infinite_latticeGraph_le_one,neg_one_le_truncated2Infinite_latticeGraph,
abs_truncated2Infinite_latticeGraph_le_one,truncated2Infinite_latticeGraph_sq_le_one}`
now live in `TwoPointTruncatedInfiniteBounds.lean`. -/


/-! ## Moved: trivial-slice / symmetry / h-zero wrappers

The five wrappers
`truncated2Infinite_latticeGraph_{J_zero_of_ne, J_zero_diagonal, beta_zero, symm, h_zero}`
now live in `TwoPointTruncatedInfiniteTrivialSlice.lean`. -/



end Ambient

end IsingModel
