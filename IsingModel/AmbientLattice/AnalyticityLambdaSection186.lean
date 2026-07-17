import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.FreeEnergyAnalyticity

/-!
# AmbientLattice/Analyticity §18.6 partitionFunction + freeEnergy regularity wrappers

Narrow child module for 23 §18.6 Λ-layer wrappers covering:

- partitionFunctionΛ per-direction regularity at `h = 0` (β / J
  Continuous, Differentiable, AnalyticAt, AnalyticOnNhd).
- freeEnergyΛ per-direction `AnalyticAt` / `AnalyticOnNhd` analyticity
  at `h = 0` (β / J).
- partitionFunction joint + general-h `AnalyticAt` / `AnalyticOnNhd`
  Λ-layer wrappers over `(β, J, h)` and at the general-h slice.

The theorem names are unchanged from the former `Analyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 partitionFunctionΛ regularity at `h = 0` Λ-layer wraps -/

/-- **Λ-layer: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ
      (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ
      (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_h_zero
    (inducedGraph G Λ) J β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_h_zero
    (inducedGraph G Λ) β J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_J_h_zero
    (inducedGraph G Λ) β

/-! ### §18.6 freeEnergyΛ per-direction analyticity Λ-layer wraps -/

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_h_zero (inducedGraph G Λ) J β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_h_zero (inducedGraph G Λ) β J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_h_zero (inducedGraph G Λ) J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_h_zero (inducedGraph G Λ) β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) h :=
  IsingModel.freeEnergy_analyticAt_h (inducedGraph G Λ) J β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_general_h
    (inducedGraph G Λ) J h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_general_h
    (inducedGraph G Λ) β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticOnNhd ℝ
      (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_h (inducedGraph G Λ) J β

/-! ### §18.6 partitionFunction joint + general-h analyticity
Λ-layer wraps -/

/-- **Λ-layer: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_continuous_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_joint (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_differentiable_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_joint
    (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) h := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_h
    (inducedGraph G Λ) J β h


end Ambient

end IsingModel
