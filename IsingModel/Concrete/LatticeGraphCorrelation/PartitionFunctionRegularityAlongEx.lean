import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity

/-!
# ℤ^d analyticity of the partition function at zero field, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the analyticity of the partition function at the
parameter record `⟨J, 0, β⟩`: `AnalyticAt ℝ` in the inverse temperature with the coupling
fixed and in the coupling with the inverse temperature fixed, and `AnalyticOnNhd ℝ` on
`Set.univ` in each of those directions. No sign condition on either parameter is imposed.
-/

namespace IsingModel
namespace Ambient

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
