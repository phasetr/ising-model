import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection

/-!
# ℤ^d partitionFunctionΛ continuous/differentiable general-h wrappers

Narrow child module for four ℤ^d
`partitionFunctionΛ_latticeGraph_{continuous,differentiable}_{beta,J}_general_h`
wrappers extracted from `PartitionFreeEnergyRegularity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: partitionFunction Continuous in `β` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    Continuous (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) :=
  Ambient.partitionFunctionΛ_continuous_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: partitionFunction Continuous in `J` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    Continuous (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) :=
  Ambient.partitionFunctionΛ_continuous_J_general_h
    (IsingModel.latticeGraph d) Λ β h

/-- **ℤ^d Λ: partitionFunction Differentiable in `β` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) :=
  Ambient.partitionFunctionΛ_differentiable_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: partitionFunction Differentiable in `J` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_J_general_h
    (IsingModel.latticeGraph d) Λ β h

end Ambient
end IsingModel
