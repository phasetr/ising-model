import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyInfinite trivial-slice wrappers

Narrow child module for the 9 ℤ^d
`freeEnergyInfinite_latticeGraph_{beta_zero,zero_params,J_zero}_*`
trivial-slice wrappers (3 `_of_eventually_nonempty`, 3 unconditional,
3 `cubicExhaustion_*`) extracted from `TwoPointFreeEnergy.lean` in
PR #2053. Each is a thin pass-through to the corresponding ambient
`freeEnergyInfinite_*` trivial-slice lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from the
former `TwoPointFreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyInfinite at β=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d freeEnergyInfinite at J=h=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d freeEnergyInfinite at J=0 under eventually-nonempty** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ h β hne

/-! ## Moved: unconditional Nonempty trivial-slice wrappers

The three wrappers
`freeEnergyInfinite_latticeGraph_beta_zero`,
`freeEnergyInfinite_latticeGraph_zero_params`,
`freeEnergyInfinite_latticeGraph_J_zero` now live in
`TwoPointFreeEnergyInfTrivialSlicesNonempty.lean`. -/


/-! ## Moved: cubicExhaustion freeEnergyInfinite trivial-slice wrappers

The three wrappers
`freeEnergyInfinite_latticeGraph_cubicExhaustion_beta_zero`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_zero_params`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_J_zero` now live in
`TwoPointFreeEnergyInfTrivialSlicesCubic.lean`. -/


end Ambient

end IsingModel
