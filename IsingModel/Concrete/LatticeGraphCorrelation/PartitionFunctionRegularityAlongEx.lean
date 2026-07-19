import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity

/-!
# Concrete partitionFunctionAlongExhaustion regularity at `h = 0`

Narrow child module for eight ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_*_h_zero` regularity
wrappers (continuous/differentiable/analyticAt/analyticOnNhd in β/J at
`h = 0`). Each wrapper is a thin pass-through to the corresponding
ambient `partitionFunctionAlongExhaustion_*_h_zero` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient
/-! ## Moved: partitionFunctionAlongEx continuous/diff h=0 wrappers

The four wrappers
`partitionFunctionAlongExhaustion_latticeGraph_continuous_beta_h_zero`,
`partitionFunctionAlongExhaustion_latticeGraph_continuous_J_h_zero`,
`partitionFunctionAlongExhaustion_latticeGraph_differentiable_beta_h_zero`,
`partitionFunctionAlongExhaustion_latticeGraph_differentiable_J_h_zero`
now live in `PartitionFunctionRegularityAlongExContinuousDiff.lean`. -/

/-- **ℤ^d along-ex: partitionFunction `AnalyticAt ℝ` in `β` at
`h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: partitionFunction `AnalyticAt ℝ` in `J` at
`h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J n

/-- **ℤ^d along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ`
in `β` at `h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) Set.univ :=
  Ambient.partitionFunctionAlongExhaustion_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: partitionFunction `AnalyticOnNhd ℝ _ Set.univ`
in `J` at `h = 0`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) Set.univ :=
  Ambient.partitionFunctionAlongExhaustion_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β n

end Ambient
end IsingModel
