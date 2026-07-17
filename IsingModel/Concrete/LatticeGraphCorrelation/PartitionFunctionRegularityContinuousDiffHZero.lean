import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# ℤ^d partitionFunctionΛ continuous/diff h=0 wrappers

Narrow child module for four ℤ^d
`partitionFunctionΛ_latticeGraph_{continuous,differentiable}_{beta,J}_h_zero`
wrappers extracted from `PartitionFunctionRegularity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    Continuous (fun β : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩) :=
  Ambient.partitionFunctionΛ_continuous_beta_h_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    Continuous (fun J : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩) :=
  Ambient.partitionFunctionΛ_continuous_J_h_zero
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d Λ: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    Differentiable ℝ (fun β : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_beta_h_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    Differentiable ℝ (fun J : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_J_h_zero
    (IsingModel.latticeGraph d) Λ β

end Ambient
end IsingModel
