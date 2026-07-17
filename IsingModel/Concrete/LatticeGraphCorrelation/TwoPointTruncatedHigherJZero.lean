import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated3Infinite J=0 trivial-slice wrappers

Narrow child module for three ℤ^d
`truncated3Infinite_latticeGraph_J_zero_*` trivial-slice wrappers
extracted from `TwoPointTruncatedHigher.lean`:

* `truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct`,
* `truncated3Infinite_latticeGraph_J_zero_of_pair_coincidence`,
* `truncated3Infinite_latticeGraph_J_zero_all_coincident`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated3Infinite J=0 pairwise distinct site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hjk hik

/-- **ℤ^d truncated3Infinite J=0 pair coincidence vanishes**
(`i = j ≠ k`): concrete wrapper for
`truncated3Infinite_J_zero_of_pair_coincidence` (#742). -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k = 0 :=
  truncated3Infinite_J_zero_of_pair_coincidence (IsingModel.latticeGraph d) Λ
    h β hf hik

/-- **ℤ^d truncated3Infinite J=0 all-coincident closed form**:
`truncated3Infinite ⟨0,h,β⟩ i i i = t·(1-t)·(1-2t)` with `t = tanh(β·h)`.
Concrete wrapper for `truncated3Infinite_J_zero_all_coincident` (#743). -/
theorem truncated3Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h))
          * (1 - 2 * Real.tanh (β * h)) :=
  truncated3Infinite_J_zero_all_coincident (IsingModel.latticeGraph d) Λ h β hf i

end Ambient
end IsingModel
