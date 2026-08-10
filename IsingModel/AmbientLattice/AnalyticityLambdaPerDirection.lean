import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.GibbsExpectation

/-!
# Per-direction continuity and differentiability of the Λ-restricted partition function

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`,
about the three one-variable slices of `partitionFunctionΛ G Λ` obtained by freezing two of
the three parameters: `fun β' ↦ partitionFunctionΛ G Λ ⟨J, h, β'⟩`,
`fun J' ↦ partitionFunctionΛ G Λ ⟨J', h, β⟩` and
`fun h' ↦ partitionFunctionΛ G Λ ⟨J, h', β⟩`. Each slice is `Continuous` and
`Differentiable ℝ` on all of `ℝ`. In the inverse-temperature and coupling slices the frozen
field is an arbitrary real rather than `0`, which is what the `_general_h` name marks.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`, and its Prop-valued hypothesis list is empty: the two
frozen parameters range over all of `ℝ`, and `Λ` is unrestricted. Each is the corresponding
base-layer statement at `inducedGraph G Λ`, to which `partitionFunctionΛ G Λ` is equal by
definition.
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
