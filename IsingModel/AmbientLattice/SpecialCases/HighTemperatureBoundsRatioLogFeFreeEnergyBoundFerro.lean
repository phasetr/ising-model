import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly

/-!
# Ambient alongExhaustion ferromagnetic freeEnergy ratio_bound_bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_bundle_ferromagnetic`
wrapper extracted from
`HighTemperatureBoundsRatioLogFeFreeEnergyBound.lean`.

To avoid an import cycle, the proof builds the conjunction directly
from the two non-bundle slice wrappers `_ratio_bound` /
`_ratio_bound_beta_zero` in
`HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly`, derived
under `mul_nonneg hβ.le hJ`. The theorem name is unchanged from
the former `HighTemperatureBoundsRatioLogFe` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f ratio bound bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
      G Λ J β (mul_nonneg hβ.le hJ) n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
      G Λ J β (mul_nonneg hβ.le hJ) n hne⟩

end Ambient

end IsingModel
