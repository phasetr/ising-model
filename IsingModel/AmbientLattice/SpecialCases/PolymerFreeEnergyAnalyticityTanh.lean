import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Polymer free-energy `tanh`-composition analyticity wrappers along an exhaustion

Narrow child module for the four §18.6 ambient alongExhaustion
`polymerFreeEnergy ∘ tanh ∘ (·)` analytic wrappers extracted from
`PolymerFreeEnergyAnalyticity.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta`
* `polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J`
* `polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero`
* `polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero`

Each wrapper is a thin pass-through to the corresponding ambient
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

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) `AnalyticOnNhd ℝ _
(Set.Ici 0)` in β under `0 ≤ J`** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β' * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    G (Λ.volume n) hJ

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) `AnalyticOnNhd ℝ _
(Set.Ici 0)` in J under `0 ≤ β`** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J')))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    G (Λ.volume n) hβ

end Ambient
end IsingModel
