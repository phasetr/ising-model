import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# ℤ^d finite-volume free-energy analyticity in one parameter at zero field

Concrete `latticeGraph d` statements that the free energy of a fixed finite volume at zero
external field, read as a function of a single real parameter with the other held fixed, is
analytic. Analyticity at a prescribed base point and analyticity on a neighbourhood of all of
`Set.univ` are each stated in the inverse temperature and in the coupling. Every statement is
made over the subgraph induced by that volume and requires a `Fintype` instance on its edge
set; that instance is the entire requirement, since no `Prop`-typed hypothesis is carried
anywhere in this module.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
