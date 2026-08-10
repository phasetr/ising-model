import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAtBeta

/-!
# Differentiability of the stage free energy at a point of the field and coupling axes

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

The stage free energy as a function of the external field is differentiable over `ℝ` at every
point `h`, with `J` and `β` fixed, and as a function of the coupling it is differentiable over
`ℝ` at every point `J`, with `h` and `β` fixed. Each statement is the `.differentiableAt`
projection of the corresponding differentiability on all of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **freeEnergyAlongExhaustion DifferentiableAt h**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_differentiable_field G (Λ.volume n) J β).differentiableAt

/-- **freeEnergyAlongExhaustion DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_differentiable_J G (Λ.volume n) h β).differentiableAt

end Ambient
end IsingModel
