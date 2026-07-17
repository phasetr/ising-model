import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Concrete free-energy per-direction analyticity wrappers

This module contains `latticeGraph` wrappers for per-direction free-energy
`AnalyticAt` and `AnalyticOnNhd` APIs at the finite-volume and
along-exhaustion layers. It is split out of the original concrete correlation
module so downstream users can import the free-energy analyticity surface
without pulling the whole original module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume free-energy per-direction analyticity -/

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) β :=
  Ambient.freeEnergyΛ_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) J :=
  Ambient.freeEnergyΛ_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
`h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
`h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β

/-! ## Moved: freeEnergyΛ AnalyticAt at general h

The three wrappers
`freeEnergyΛ_latticeGraph_analyticAt_beta_general_h`,
`freeEnergyΛ_latticeGraph_analyticAt_J_general_h`,
`freeEnergyΛ_latticeGraph_analyticAt_h` now live in
`FreeEnergyAnalyticityAtGeneralH.lean`. -/


/-! ## Moved: freeEnergyΛ AnalyticOnNhd at general h

The three wrappers
`freeEnergyΛ_latticeGraph_analyticOnNhd_beta_general_h`,
`freeEnergyΛ_latticeGraph_analyticOnNhd_J_general_h`,
`freeEnergyΛ_latticeGraph_analyticOnNhd_h` now live in
`FreeEnergyAnalyticityOnNhdGeneralH.lean`. -/


/-! ## Moved: along-ex free-energy analyticity wrappers

The ten `freeEnergyAlongExhaustion_latticeGraph_analytic*` wrappers
(`analyticAt` / `analyticOnNhd` in β/J/h, at `h = 0` and at general h)
now live in `FreeEnergyAnalyticityAlongEx.lean`. -/


end Ambient
end IsingModel
