import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# ℤ^d Λ-layer freeEnergy `AnalyticAt` general-h wrappers

Narrow child module for three ℤ^d Λ-layer freeEnergy `AnalyticAt`
wrappers at general `h` extracted from `FreeEnergyAnalyticity.lean`:

* `freeEnergyΛ_latticeGraph_analyticAt_beta_general_h`,
* `freeEnergyΛ_latticeGraph_analyticAt_J_general_h`,
* `freeEnergyΛ_latticeGraph_analyticAt_h`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyΛ_analyticAt_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `FreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) β :=
  Ambient.freeEnergyΛ_analyticAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) J :=
  Ambient.freeEnergyΛ_analyticAt_J_general_h
    (IsingModel.latticeGraph d) Λ β h J

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) h :=
  Ambient.freeEnergyΛ_analyticAt_h
    (IsingModel.latticeGraph d) Λ J β h

end Ambient
end IsingModel
