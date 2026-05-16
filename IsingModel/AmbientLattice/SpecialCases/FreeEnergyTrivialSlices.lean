import IsingModel.AmbientLattice.SpontaneousMono

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

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

end Ambient
end IsingModel
