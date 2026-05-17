import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFE

/-!
# Ambient alongExhaustion sharper-exp freeEnergy complete-summary ferromagnetic wrapper

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic `complete_summary_exp_ferromagnetic` freeEnergy
wrapper extracted from
`HighTemperatureBoundsExpSharperCompleteFerro.lean`:

* `freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic`

The wrapper is a thin pass-through to its non-ferromagnetic
sibling in `HighTemperatureBoundsExpSharperCompleteFE` under
`mul_nonneg hβ.le hJ`. The theorem name is unchanged from the
former `HighTemperatureBoundsExpSharperComplete` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f complete-summary exp bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

end Ambient

end IsingModel
