/- BaseCorrelationAlongEx.lean
Narrow child module for the 7 ℤ^d
`correlation{Λ,AlongExhaustion}_latticeGraph_*` wrappers extracted
from `Base.lean` in PR #2035. Theorems:
`correlationAlongExhaustion_latticeGraph_{J_zero_of_subset,J_zero_eventually_eq}`,
`correlationΛ_latticeGraph_empty`,
`correlationAlongExhaustion_latticeGraph_{empty,of_subset,of_not_subset,cubicExhaustion_monotone}`.
Each is a thin pass-through to the corresponding abstract lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`Base` declarations.
-/
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0`** per stage (on-stage):
`A ⊆ Λ.volume n ⇒ = tanh(β·h)^|A|`. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_of_subset
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) {A : Finset (Fin d → ℤ)} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_of_subset (IsingModel.latticeGraph d) Λ h β hAn

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0` is eventually constant
at `tanh(β·h)^|A|`**. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β A


/-- **ℤ^d correlationΛ_empty = 1** per finite volume. -/
@[simp]
theorem correlationΛ_latticeGraph_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    correlationΛ (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationΛ_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d correlationAlongExhaustion_empty = 1** per stage. -/
@[simp]
theorem correlationAlongExhaustion_latticeGraph_empty
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p ∅ n = 1 :=
  correlationAlongExhaustion_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-! ## Moved: subset / monotone wrappers

The three wrappers
`correlationAlongExhaustion_latticeGraph_of_subset`,
`correlationAlongExhaustion_latticeGraph_of_not_subset`,
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone` now
live in `BaseCorrelationAlongExSubsetMono.lean`. -/


end Ambient

end IsingModel
