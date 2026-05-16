import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient `partitionFunctionAlongExhaustion` `Differentiable` regularity wrappers

Narrow child module for the three ambient
`partitionFunctionAlongExhaustion_differentiable_*` regularity
wrappers extracted from `PartitionFreeEnergyRegularity.lean`:

* `partitionFunctionAlongExhaustion_differentiable_beta_general_h`
* `partitionFunctionAlongExhaustion_differentiable_J_general_h`
* `partitionFunctionAlongExhaustion_differentiable_h`

Each result is a thin pass-through of the corresponding Λ-level
`partitionFunctionΛ_differentiable_*` lemma. Theorem names are
unchanged from the former `PartitionFreeEnergyRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction Differentiable in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Differentiable in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h

/-- **Along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_differentiable_h G (Λ.volume n) J β

end Ambient
end IsingModel
