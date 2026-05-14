import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity

/-!
# ℤ^d partitionFunctionAlongEx continuous/diff h=0 wrappers

Narrow child module for four ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_{continuous,differentiable}_{beta,J}_h_zero`
wrappers extracted from `PartitionFunctionRegularityAlongEx.lean`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    Continuous (fun β : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_beta_h_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    Continuous (fun J : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_J_h_zero
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `β` at
`h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_beta_h_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `J` at
`h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_J_h_zero
    (IsingModel.latticeGraph d) Λ β n


end Ambient
end IsingModel
