import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityAtH
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityHZero
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityOnNhd

/-!
# Ambient free-energy per-direction analyticity wrappers

This module contains general-graph `AnalyticAt` and `AnalyticOnNhd` APIs
for per-stage `freeEnergyAlongExhaustion` in the `β`, `J`, and `h`
directions. It is split out of the original ambient special-cases module so
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

/-! ## Moved: 1 AnalyticAt `h` wrapper

The `freeEnergyAlongExhaustion_analyticAt_h` wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticityAtH`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: freeEnergyAlongExhaustion AnalyticOnNhd general-h wrappers

The three `freeEnergyAlongExhaustion_analyticOnNhd_*` wrappers
(beta_general_h, J_general_h, h) now live in
`FreeEnergyAnalyticityOnNhd.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/


end Ambient
end IsingModel
