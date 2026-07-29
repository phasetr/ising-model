import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity

/-!
# Concrete along-ex partitionFunction regularity wrappers

Narrow child module for four ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_*`
`Continuous`/`Differentiable` regularity wrappers (continuous_*,
differentiable_* in β, J at general h). Each wrapper is a thin
pass-through to the corresponding ambient
`partitionFunctionAlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: partitionFunction Continuous in `β` at general
`h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h, β'⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: partitionFunction Continuous in `J` at general
`h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J', h, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `β` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h, β'⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `J` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J', h, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

end Ambient
end IsingModel
