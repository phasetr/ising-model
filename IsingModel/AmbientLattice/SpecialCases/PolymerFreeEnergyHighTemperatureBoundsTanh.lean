import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanhLtLog2

/-!
# Polymer free-energy tanh ≤ high-temperature bound wrappers along an exhaustion

Narrow child module for the two §18.5 ambient alongExhaustion
`polymerFreeEnergy_tanh_*_le_*` non-strict bound wrappers extracted
from `PolymerFreeEnergyHighTemperatureBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_le_eps_of_betaJ_nonneg`
* `polymerFreeEnergyAlongExhaustion_tanh_le_pow_sub_one_of_betaJ_nonneg`

The corresponding strict-inequality
`_lt_log_two_of_pow_lt_two` wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanhLtLog2`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_*` lemma. Theorem names are unchanged
from the former `PolymerFreeEnergyHighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_eps_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_le_pow_sub_one_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    G (Λ.volume n) hβJ

/-! ## Moved: 1 lt_log_two_of_pow_lt_two wrapper

The `polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanhLtLog2`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
