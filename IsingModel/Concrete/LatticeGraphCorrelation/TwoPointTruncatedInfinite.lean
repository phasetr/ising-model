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

Narrow child module for 16 ℤ^d
`truncated2Infinite_latticeGraph_*` wrappers (bounds, nonneg,
symmetry, trivial slices `J_zero` / `β_zero` / `h_zero`),
`truncated3Infinite_latticeGraph_apply`, and
`truncated4Infinite_latticeGraph_apply`. Theorem names are unchanged
from the former `TwoPoint` declarations.
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

/-- **ℤ^d `truncated2Infinite ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ≤ 1 :=
  truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `-1 ≤ truncated2Infinite`** (ferromagnetic). -/
theorem neg_one_le_truncated2Infinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    -1 ≤ truncated2Infinite (IsingModel.latticeGraph d) Λ p i j :=
  neg_one_le_truncated2Infinite (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `|truncated2Infinite| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    |truncated2Infinite (IsingModel.latticeGraph d) Λ p i j| ≤ 1 :=
  abs_truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `truncated2Infinite² ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ^ 2 ≤ 1 :=
  truncated2Infinite_sq_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d truncated 2-point function vanishes at `J = 0`, `i ≠ j`**
(ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_J_zero_of_ne
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 :=
  truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ h β hf hij

/-- **ℤ^d truncated 2-point function at `J = 0` diagonal**
(ferromagnetic): `truncated2Infinite ⟨0,h,β⟩ i i = tanh(β·h) · (1 − tanh(β·h))`.
Concrete wrapper for `truncated2Infinite_J_zero_diagonal`. -/
theorem truncated2Infinite_latticeGraph_J_zero_diagonal
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  truncated2Infinite_J_zero_diagonal (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d truncated 2-point function vanishes at `β = 0`**. -/
theorem truncated2Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 :=
  truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j

/-- **ℤ^d truncated2Infinite symmetry in (i, j)**. -/
theorem truncated2Infinite_latticeGraph_symm
    (d : ℕ) (p : IsingParams ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p j i :=
  truncated2Infinite_symm (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p i j

/-- **ℤ^d truncated2Infinite at h=0**: collapses to `correlationInfinite ... {i, j}`. -/
theorem truncated2Infinite_latticeGraph_h_zero
    (d : ℕ) (J β : ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ i j
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ {i, j} :=
  truncated2Infinite_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β i j

end Ambient

end IsingModel
