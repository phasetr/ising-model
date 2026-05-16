import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlicesJZero

/-!
# Free-energy trivial-parameter-slice closed forms along an exhaustion

Narrow child module for the six along-exhaustion / infinite-volume
free-energy closed-form identities at trivial parameter slices
(`β = 0`, `J = h = 0`, `J = 0`). Each wrapper is a thin pass-through
to the corresponding `IsingModel.freeEnergy_*` ambient lemma, or
(for the two `freeEnergyInfinite_*` variants) a `limsup`
specialization of a constant sequence built from the
along-exhaustion sibling. Theorem names are unchanged from the
former `FreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion β=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ, J, h`,
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_beta_zero` (PR #131) via
`change` + definitional unfolding of `freeEnergyAlongExhaustion`
through `freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_beta_zero _ J h (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Along-exhaustion J=h=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `β`,
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_zero_params` via `change` +
definitional unfolding of `freeEnergyAlongExhaustion` through
`freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)

/-! ## Moved: `freeEnergyInfinite_*` trivial-slice wrappers

The two `freeEnergyInfinite_*` trivial-slice closed-form
wrappers (`_beta_zero`, `_zero_params`) now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlicesInfinite`.
The legacy import path is preserved by re-exporting the new child
from `Legacy.lean`.
-/

/-! ## Moved: 2 `_J_zero` wrappers

The two J = 0 wrappers
(`freeEnergyAlongExhaustion_eq_bot_at_J_zero`,
`freeEnergyAlongExhaustion_J_zero`) now live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyTrivialSlicesJZero`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel
