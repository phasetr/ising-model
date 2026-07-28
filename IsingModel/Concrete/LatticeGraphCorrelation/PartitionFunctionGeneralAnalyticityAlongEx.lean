import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticity

/-!
# ℤ^d AlongExhaustion partition-function general analyticity wrappers

Narrow child module for five ℤ^d AlongExhaustion
`partitionFunctionAlongExhaustion_latticeGraph_*` analyticity wrappers
of the concrete general-analyticity family:

* `partitionFunctionAlongExhaustion_latticeGraph_continuous_joint`,
* `partitionFunctionAlongExhaustion_latticeGraph_differentiable_joint`,
* `partitionFunctionAlongExhaustion_latticeGraph_analyticAt_beta_general_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_analyticAt_J_general_h`,
* `partitionFunctionAlongExhaustion_latticeGraph_analyticAt_h`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: partitionFunction jointly `Continuous`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: partitionFunction jointly
`Differentiable ℝ`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: partitionFunction `AnalyticAt ℝ` in `β` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: partitionFunction `AnalyticAt ℝ` in `J` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J', h, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_J_general_h
    (IsingModel.latticeGraph d) Λ β h J n

/-- **ℤ^d along-ex: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h', β⟩ n) h :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_h
    (IsingModel.latticeGraph d) Λ J β h n


end Ambient
end IsingModel
