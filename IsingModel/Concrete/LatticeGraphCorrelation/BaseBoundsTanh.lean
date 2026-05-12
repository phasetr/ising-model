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
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

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

/-- **ℤ^d `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationΛ_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A

/-- **ℤ^d `correlationInfinite ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationInfinite_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A


/-- **ℤ^d `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationΛ_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i

/-- **ℤ^d `magnetizationInfinite ≥ tanh(β·h)`** (ferromagnetic, any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : Fin d → ℤ) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i


end Ambient

end IsingModel
