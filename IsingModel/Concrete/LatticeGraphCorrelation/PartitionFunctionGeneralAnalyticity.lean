import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Concrete partition-function joint and general-h analyticity wrappers

This module contains concrete `latticeGraph` specializations of joint
`Continuous` / `Differentiable` APIs and general-h `AnalyticAt` APIs for
partition functions. It is split out of the original concrete correlation module
so downstream users can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition-function joint and general-h analyticity -/

/-- **ℤ^d Λ: partitionFunction jointly `Continuous` in `(β, J, h)`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.partitionFunctionΛ_continuous_joint
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.partitionFunctionΛ_differentiable_joint
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) β :=
  Ambient.partitionFunctionΛ_analyticAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d Λ: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticAt_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) J :=
  Ambient.partitionFunctionΛ_analyticAt_J_general_h
    (IsingModel.latticeGraph d) Λ β h J

/-- **ℤ^d Λ: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticAt_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) h :=
  Ambient.partitionFunctionΛ_analyticAt_h
    (IsingModel.latticeGraph d) Λ J β h

/-! ## Moved: AlongExhaustion partition-function general analyticity wrappers

The five AlongExhaustion `partitionFunctionAlongExhaustion_latticeGraph_*`
analyticity wrappers (`continuous_joint`, `differentiable_joint`,
`analyticAt_beta_general_h`, `analyticAt_J_general_h`, `analyticAt_h`)
now live in `PartitionFunctionGeneralAnalyticityAlongEx.lean`. -/


end Ambient
end IsingModel
