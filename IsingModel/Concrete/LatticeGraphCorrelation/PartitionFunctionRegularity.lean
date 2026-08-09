import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# ℤ^d analyticity of the partition function at zero field, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the analyticity of
the partition function at the parameter record `⟨J, 0, β⟩`: `AnalyticAt ℝ` in the inverse
temperature with the coupling fixed and in the coupling with the inverse temperature fixed,
and `AnalyticOnNhd ℝ` on `Set.univ` in each of those directions. No sign condition on either
parameter is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) β :=
  Ambient.partitionFunctionΛ_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) J :=
  Ambient.partitionFunctionΛ_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J

/-- **ℤ^d Λ: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) Set.univ :=
  Ambient.partitionFunctionΛ_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionΛ_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) Set.univ :=
  Ambient.partitionFunctionΛ_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β

end Ambient
end IsingModel
