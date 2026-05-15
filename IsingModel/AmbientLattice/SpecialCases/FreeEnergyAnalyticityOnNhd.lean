import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient freeEnergyAlongExhaustion AnalyticOnNhd general-h wrappers

Narrow child module for 3 ambient
`freeEnergyAlongExhaustion_analyticOnNhd_*` wrappers extracted from
`FreeEnergyAnalyticity.lean`:

* `freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h`,
* `freeEnergyAlongExhaustion_analyticOnNhd_J_general_h`,
* `freeEnergyAlongExhaustion_analyticOnNhd_h`.

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analyticOnNhd_*` lemma. The theorem names are unchanged
from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_J_general_h G (Λ.volume n) β h

/-- **Along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_h G (Λ.volume n) J β


end Ambient
end IsingModel
