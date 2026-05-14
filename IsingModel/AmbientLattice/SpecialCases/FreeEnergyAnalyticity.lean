import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityHZero

/-!
# Ambient free-energy per-direction analyticity wrappers

This module contains general-graph `AnalyticAt` and `AnalyticOnNhd` APIs
for per-stage `freeEnergyAlongExhaustion` in the `β`, `J`, and `h`
directions. It is split out of the legacy ambient special-cases module so
concrete free-energy analyticity wrappers can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion free-energy per-direction analyticity -/

/-! ## Moved: freeEnergyAlongExhaustion h=0 analyticity wrappers

The four `freeEnergyAlongExhaustion_analytic*_*_h_zero` wrappers
(AnalyticAt × {beta,J}, AnalyticOnNhd × {beta,J}) now live in
`FreeEnergyAnalyticityHZero.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



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
