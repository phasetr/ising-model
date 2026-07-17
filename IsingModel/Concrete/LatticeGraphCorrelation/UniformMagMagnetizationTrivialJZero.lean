import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `magnetization*_latticeGraph_*J_zero*` wrappers

Narrow child module for three ℤ^d magnetization J=0 closed-form
wrappers extracted from `UniformMagMagnetizationTrivial.lean`:

* `magnetizationΛ_latticeGraph_J_zero`,
* `magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem`,
* `magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq`.

Each result is a thin pass-through of the ambient
`Ambient.magnetization*_J_zero*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagMagnetizationTrivial` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationΛ at J=0 closed form**: `= tanh(β·h)`. -/
theorem magnetizationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  magnetizationΛ_J_zero (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d magnetizationAlongExhaustion at J=0** per stage (on-stage):
`i ∈ Λ.volume n ⇒ = tanh(β·h)`. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_of_mem (IsingModel.latticeGraph d) Λ h β hi

/-- **ℤ^d magnetizationAlongExhaustion at J=0 is eventually `tanh(β·h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (i : Fin d → ℤ) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β i


end Ambient

end IsingModel
