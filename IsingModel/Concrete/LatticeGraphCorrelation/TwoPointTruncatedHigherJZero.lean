import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# The ℤ^d truncated three-point correlation at vanishing coupling

Concrete `IsingModel.latticeGraph d` statements along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, at the parameter record `⟨0, h, β⟩` and under `Ferromagnetic` on it, sorted by
how the sites coincide.

At pairwise distinct sites the value vanishes, and it still vanishes when the first two
sites coincide and the third differs from them. When all the sites coincide it has the
closed form `t * (1 - t) * (1 - 2 * t)`, writing `t` for `Real.tanh (β * h)`. The
ferromagnetic condition confines `t` to `[0, 1)`, where that cubic vanishes exactly at
`t = 0`, that is at `h = 0`, and at `t = 1 / 2`; between those two roots it is positive,
and above the larger one it is negative. No instance argument is taken.
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
