import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity

/-!
# Concrete partition-function regularity wrappers

This module contains concrete `latticeGraph` specializations of `Continuous`,
`Differentiable`, `AnalyticAt`, and `AnalyticOnNhd` APIs for partition
functions at zero external field. It is split out of the legacy concrete
correlation module so downstream users can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition-function regularity at `h = 0` -/

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
