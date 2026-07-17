/- BaseBoundsTanh.lean
Narrow child module for the 8 ℤ^d magnetization sq-bound + correlation
J = 0 closed form + correlation/magnetization ge_tanh* wrappers
extracted from `Base.lean` in PR #2034. Theorems:
`magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph_sq_le_one`,
`correlationΛ_latticeGraph_J_zero`,
`correlation{Λ,Infinite}_latticeGraph_ge_tanh_pow_card`,
`magnetization{Λ,Infinite}_latticeGraph_ge_tanh`. Each is a thin
pass-through to the corresponding abstract lemma at `latticeGraph d`.
The theorem names are unchanged from the former `Base`
declarations.
-/
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient


/-- **ℤ^d `magnetizationΛ² ≤ 1`**. -/
theorem magnetizationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `magnetizationAlongExhaustion² ≤ 1`** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ^ 2 ≤ 1 := by
  have h := abs_magnetizationAlongExhaustion_le_one
    (IsingModel.latticeGraph d) Λ p i n
  have : |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ^ 2
      ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **ℤ^d `magnetizationInfinite² ≤ 1`** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationΛ` at `J = 0` closed form**:
`correlationΛ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationΛ_J_zero (IsingModel.latticeGraph d) Λ h β A

/-! ## Moved: ge_tanh wrappers

The four wrappers
`correlationΛ_latticeGraph_ge_tanh_pow_card`,
`correlationInfinite_latticeGraph_ge_tanh_pow_card`,
`magnetizationΛ_latticeGraph_ge_tanh`,
`magnetizationInfinite_latticeGraph_ge_tanh` now live in
`BaseBoundsTanhGe.lean`. -/



end Ambient

end IsingModel
