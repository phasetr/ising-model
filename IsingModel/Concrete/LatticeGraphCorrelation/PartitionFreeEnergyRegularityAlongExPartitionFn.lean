import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity

/-!
# ℤ^d global regularity of the partition function at a general field

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the regularity of the partition function as a function
of one parameter of the record `⟨J, h, β⟩` with the field left arbitrary: `Continuous` and
`Differentiable ℝ` in the inverse temperature with the coupling fixed, and in the coupling
with the inverse temperature fixed, in each case on the whole line. No sign condition on any
parameter is imposed.
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
