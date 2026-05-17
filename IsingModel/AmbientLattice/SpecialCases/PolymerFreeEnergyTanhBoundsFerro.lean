import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerroSandwich

/-!
# Polymer free-energy ferromagnetic tanh ≤ bound wrappers along an exhaustion

Narrow child module for the two §18.5 ambient alongExhaustion
ferromagnetic `polymerFreeEnergy_tanh_*_ferro` upper-bound
wrappers extracted from `PolymerFreeEnergyTanhBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro`
* `polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro`

The corresponding sandwich wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerroSandwich`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_*_ferromagnetic` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyTanhBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    G (Λ.volume n) hJ hβ

/-! ## Moved: 1 ferromagnetic sandwich wrapper

The `polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerroSandwich`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
