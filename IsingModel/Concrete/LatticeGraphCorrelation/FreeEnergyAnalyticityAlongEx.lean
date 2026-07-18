import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity

/-!
# Concrete along-ex free-energy analyticity wrappers

Narrow child module for ten ℤ^d `freeEnergyAlongExhaustion_latticeGraph_analytic*`
wrappers (`analyticAt` / `analyticOnNhd` in β/J/h, at `h = 0` and at
general h). Each wrapper is a thin pass-through to the corresponding
ambient `freeEnergyAlongExhaustion_analytic*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-exhaustion free-energy per-direction analyticity -/

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β n

/-! ## Moved: freeEnergyAlongEx AnalyticAt general-h wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_analyticAt_beta_general_h`,
`freeEnergyAlongExhaustion_latticeGraph_analyticAt_J_general_h`,
`freeEnergyAlongExhaustion_latticeGraph_analyticAt_h` now live in
`FreeEnergyAnalyticityAlongExAnalyticAtGeneralH.lean`. -/


/-! ## Moved: freeEnergyAlongEx AnalyticOnNhd general-h wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_general_h`,
`freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_general_h`,
`freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_h` now live in
`FreeEnergyAnalyticityAlongExOnNhdGeneralH.lean`. -/


end Ambient
end IsingModel
