import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnlyFerro

/-!
# Ambient alongExhaustion freeEnergy ratio_bound non-bundle wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
non-ferromagnetic
`freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound*` non-bundle
wrappers (`J = 0`, `β = 0`). Each wrapper is a thin pass-through to
the corresponding `freeEnergyΛ_high_temp_h_zero_ratio_bound*` ambient
lemma under the joint hypothesis `0 ≤ β * J`. The ferromagnetic
counterparts now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnlyFerro`
and are re-imported through this parent module. Theorem names are
unchanged from the former
`HighTemperatureBoundsRatioLogFeFreeEnergyBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex f ratio bound at J=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound G (Λ.volume n) J β hβJ hne

/-- **Along-ex f ratio bound at β=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β hβJ hne

/-! ## Moved: 2 ferromagnetic f ratio_bound wrappers

The two ferromagnetic
`freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound*_ferromagnetic`
non-bundle wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnlyFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
