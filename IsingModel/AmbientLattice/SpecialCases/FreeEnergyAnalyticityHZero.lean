import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient freeEnergyAlongExhaustion h=0 analyticity wrappers

Narrow child module for 4 ambient
`freeEnergyAlongExhaustion_analytic*_*_h_zero` analyticity wrappers
extracted from `FreeEnergyAnalyticity.lean`:

* `freeEnergyAlongExhaustion_analyticAt_beta_h_zero`,
* `freeEnergyAlongExhaustion_analyticAt_J_h_zero`,
* `freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero`,
* `freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero`.

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analytic*_*_h_zero` lemma. The theorem names are
unchanged from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  freeEnergyΛ_analyticAt_beta_h_zero G (Λ.volume n) J β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  freeEnergyΛ_analyticAt_J_h_zero G (Λ.volume n) β J

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, 0, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_h_zero G (Λ.volume n) J

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
`h = 0`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', 0, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_h_zero G (Λ.volume n) β

end Ambient
end IsingModel
