import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuityTrivial

/-!
# Ambient alongExhaustion freeEnergy continuity wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
freeEnergy quantitative continuity wrappers. 4 theorems:
`freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_J_zero`,
`_at_beta_zero`, `_bundle`, `_bundle_ferromagnetic`. Wrappers pass
through to the Λ-level `freeEnergyΛ_high_temp_h_zero_continuity_*`
versions via `change ... ; exact` (the bundle is an anonymous
constructor; the ferromagnetic bundle applies `mul_nonneg`). The
theorem names are unchanged from the former
`HighTemperatureBoundsDeviation` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 2 trivial-slice continuity wrappers

The two along-ex freeEnergy continuity wrappers at trivial
parameter slices
(`freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_J_zero`,
`freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_beta_zero`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuityTrivial`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_J_zero
      G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_continuity_at_beta_zero
      G Λ J β hβJ n hne⟩

/-- **Along-ex ferromagnetic f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne
end Ambient

end IsingModel
