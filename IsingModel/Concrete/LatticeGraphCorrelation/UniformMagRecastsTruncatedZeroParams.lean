import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d `truncatedN_zero_params` wrappers

Narrow child module for three ℤ^d
`truncated{2,3,4}TwoPoint_zero_params` vanishing wrappers extracted
from `UniformMagRecasts.lean`:

* `truncated2TwoPoint_zero_params`,
* `truncated3TwoPoint_zero_params`,
* `truncated4TwoPoint_zero_params`.

Each result evaluates the corresponding truncated Ursell / Lebowitz
expansion using
`correlationInfinite_zero_params_vanish` for every term that appears
in the expansion. The theorem names are unchanged from the former
`UniformMagRecasts` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **`truncated2TwoPoint` at `J = h = 0` vanishes**:
`truncated2TwoPoint d ⟨0, 0, β⟩ r = 0`. All three Ursell terms vanish. -/
theorem truncated2TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated3TwoPoint` at `J = h = 0` vanishes**:
`truncated3TwoPoint d ⟨0, 0, β⟩ r s = 0`. All seven Ursell terms vanish. -/
theorem truncated3TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s = 0 := by
  unfold truncated3TwoPoint truncated3Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated4TwoPoint` at `J = h = 0` vanishes**:
`truncated4TwoPoint d ⟨0, 0, β⟩ r s u = 0`. All four Lebowitz terms vanish. -/
theorem truncated4TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s u = 0 := by
  unfold truncated4TwoPoint truncated4Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

end Ambient

end IsingModel
