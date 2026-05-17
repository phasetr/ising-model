import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanhOnNhd

/-!
# Polymer free-energy `tanh`-composition `AnalyticAt` wrappers along an exhaustion

Narrow child module for the two §18.6 ambient alongExhaustion
`polymerFreeEnergy ∘ tanh ∘ (·)` `AnalyticAt ℝ` wrappers extracted
from `PolymerFreeEnergyAnalyticity.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta`
* `polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J`

The two corresponding `AnalyticOnNhd ℝ _ (Set.Ici 0)` wrappers now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanhOnNhd`
and are re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_analytic*_*` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) `AnalyticAt ℝ`
in β** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β' * J))) β :=
  polymerFreeEnergy_Λ_tanh_analyticAt_beta G (Λ.volume n) J β hβJ

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) `AnalyticAt ℝ`
in J** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J'))) J :=
  polymerFreeEnergy_Λ_tanh_analyticAt_J G (Λ.volume n) β J hβJ

/-! ## Moved: 2 `AnalyticOnNhd` Ici-zero wrappers

The two `polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_*_Ici_zero`
wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanhOnNhd`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
