import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanh

/-!
# Polymer free-energy analyticity wrappers along an exhaustion (direct in `t`)

Narrow child module for along-exhaustion `polymerFreeEnergy` direct
`s ↦ polymerFreeEnergy (·) s` analytic wrappers. This keeps callers
that only need these analytic forwarders out of the monolithic
special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 4 tanh-composition analyticity wrappers

The four §18.6 `polymerFreeEnergy ∘ tanh ∘ (·)` analytic wrappers
(`polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta`,
`polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J`,
`polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero`,
`polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero`)
now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G (Λ.volume n)) s) t :=
  polymerFreeEnergy_Λ_analyticAt G (Λ.volume n) ht

/-- **Along-ex: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergyAlongExhaustion_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G (Λ.volume n)) s) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
