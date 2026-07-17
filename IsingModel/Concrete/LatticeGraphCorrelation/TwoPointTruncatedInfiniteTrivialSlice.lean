import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated2Infinite trivial-slice / symmetry / h-zero wrappers

Narrow child module for five ℤ^d `truncated2Infinite_latticeGraph_*` wrappers
extracted from `TwoPointTruncatedInfinite.lean`:

* `truncated2Infinite_latticeGraph_J_zero_of_ne`,
* `truncated2Infinite_latticeGraph_J_zero_diagonal`,
* `truncated2Infinite_latticeGraph_beta_zero`,
* `truncated2Infinite_latticeGraph_symm`,
* `truncated2Infinite_latticeGraph_h_zero`.
-/

namespace IsingModel
namespace Ambient

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
