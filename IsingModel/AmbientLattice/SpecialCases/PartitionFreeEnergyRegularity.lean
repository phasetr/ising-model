import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFE

/-!
# Ambient partition/free-energy regularity wrappers

This module contains general-graph `Continuous` and `Differentiable` APIs for
per-stage `partitionFunctionAlongExhaustion` and `freeEnergyAlongExhaustion`.
It is split out of the legacy ambient special-cases module so concrete
partition/free-energy wrappers can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition/free-energy Continuous and Differentiable -/

/-- **Along-ex: partitionFunction Continuous in `β` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_continuous_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Continuous in `J` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_continuous_J_general_h G (Λ.volume n) β h

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

/-- **Along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_continuous_h G (Λ.volume n) J β

/-- **Along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_differentiable_h G (Λ.volume n) J β

/-! ## Moved: freeEnergyAlongExhaustion regularity wrappers

The eight `freeEnergyAlongExhaustion_{continuous,differentiable}_*`
regularity wrappers (joint, beta, field, J) now live in
`PartitionFreeEnergyRegularityFE.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



end Ambient
end IsingModel
