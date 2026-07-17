import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralH

/-!
# ℤ^d partitionFunctionAlongEx continuousAt/diffAt general-h wrappers

Narrow child module for four ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_{continuousAt,differentiableAt}_{beta,J}_general_h`
wrappers extracted from `PartitionFreeEnergyPointwiseRegularity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_J_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_J_general_h
    (IsingModel.latticeGraph d) Λ J h β n

end Ambient
end IsingModel
