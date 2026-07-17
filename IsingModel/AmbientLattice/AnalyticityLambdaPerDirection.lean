import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.GibbsExpectation

/-!
# AmbientLattice/Analyticity Λ partitionFunction per-direction wrappers

Narrow child module for the 6 partitionFunctionΛ per-direction
Continuous / Differentiable wrappers at general h:
`partitionFunctionΛ_continuous_beta_general_h`,
`partitionFunctionΛ_differentiable_beta_general_h`,
`partitionFunctionΛ_continuous_J_general_h`,
`partitionFunctionΛ_differentiable_J_general_h`,
`partitionFunctionΛ_continuous_h`,
`partitionFunctionΛ_differentiable_h`. The theorem names are
unchanged from the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Λ-layer partitionFunction per-direction regularity at general h -/

/-- **partitionFunctionΛ Continuous in `β` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_beta_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Continuous (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) :=
  IsingModel.partitionFunction_continuous_beta_general_h (inducedGraph G Λ) J h

/-- **partitionFunctionΛ Differentiable in `β` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_beta_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) :=
  IsingModel.partitionFunction_differentiable_beta_general_h (inducedGraph G Λ) J h

/-- **partitionFunctionΛ Continuous in `J` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_J_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    Continuous (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) :=
  IsingModel.partitionFunction_continuous_J_general_h (inducedGraph G Λ) β h

/-- **partitionFunctionΛ Differentiable in `J` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_J_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) :=
  IsingModel.partitionFunction_differentiable_J_general_h (inducedGraph G Λ) β h

/-- **partitionFunctionΛ Continuous in `h`** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Continuous (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) :=
  IsingModel.partitionFunction_continuous_h (inducedGraph G Λ) J β

/-- **partitionFunctionΛ Differentiable in `h`** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) :=
  IsingModel.partitionFunction_differentiable_h (inducedGraph G Λ) J β


end Ambient

end IsingModel
