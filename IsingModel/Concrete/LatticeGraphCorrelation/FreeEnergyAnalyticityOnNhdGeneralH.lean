import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# ℤ^d freeEnergyΛ AnalyticOnNhd at general h

Narrow child module for three ℤ^d
`freeEnergyΛ_latticeGraph_analyticOnNhd_*` wrappers (β, J, h at
general h) extracted from `FreeEnergyAnalyticity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_J_general_h
    (IsingModel.latticeGraph d) Λ β h

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_h
    (IsingModel.latticeGraph d) Λ J β

end Ambient
end IsingModel
