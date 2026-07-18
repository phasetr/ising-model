import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient free-energy per-direction analyticity wrappers

This module collects the general-graph `AnalyticAt` and `AnalyticOnNhd`
APIs for per-stage `freeEnergyAlongExhaustion` in the `β`, `J`, and `h`
directions. It provides ten wrappers, organized as the product of

* two analyticity flavours: `AnalyticAt ℝ … β/J/h` (Section A) and
  `AnalyticOnNhd ℝ … Set.univ` (Section B),
* three directions: `β`, `J`, and `h`,
* two field regimes: general `h` (for `β`/`J`) and `h = 0` (for `β`/`J`),
  together with the two field-direction wrappers.

Each wrapper is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_analytic*` lemma supplied through
`IsingModel.AmbientLattice.Analyticity` (which transitively imports the
`AnalyticityLambdaSection186` layer). The theorem names and statements are
the ambient facade preserved verbatim from the earlier split modules.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Section A: `AnalyticAt` wrappers -/

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  freeEnergyΛ_analyticAt_beta_general_h G (Λ.volume n) J h β

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  freeEnergyΛ_analyticAt_J_general_h G (Λ.volume n) β h J

/-- **Along-ex: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  freeEnergyΛ_analyticAt_h G (Λ.volume n) J β h

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

/-! ## Section B: `AnalyticOnNhd` wrappers -/

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
