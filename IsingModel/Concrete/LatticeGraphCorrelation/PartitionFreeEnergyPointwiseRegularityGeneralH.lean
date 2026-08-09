import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralH

/-!
# ℤ^d pointwise regularity of the partition function at a general field

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the pointwise regularity of the partition function at
the parameter record `⟨J, h, β⟩` with the field left arbitrary: `ContinuousAt` and
`DifferentiableAt ℝ` in the inverse temperature with the coupling fixed, and in the coupling
with the inverse temperature fixed. No sign condition on any parameter is imposed.
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
