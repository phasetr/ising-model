import IsingModel.AmbientLattice.Defs.Regularity.Convergent

/-!
# Lambda-layer regularity split — correlation continuity, differentiability, and pointwise variants

Part of the split Lambda-layer regularity wrappers (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **correlationΛ Continuous in β at h = 0**. -/
theorem correlationΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta _ J A

/-- **correlationΛ Continuous in β at general h**. -/
theorem correlationΛ_continuous_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta_general_h _ J h A

/-- **correlationΛ Differentiable in β at h = 0**. -/
theorem correlationΛ_differentiable_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta _ J A

/-- **correlationΛ Differentiable in β at general h**. -/
theorem correlationΛ_differentiable_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta_general_h _ J h A

/-- **correlationΛ Continuous in `h`**. -/
theorem correlationΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_field _ J β A

/-- **correlationΛ Differentiable in `h`**. -/
theorem correlationΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_field _ J β A

/-- **correlationΛ Continuous in `J`**. -/
theorem correlationΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_J _ h β A

/-- **correlationΛ Differentiable in `J`**. -/
theorem correlationΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_J _ h β A

/-- **correlationΛ ContinuousAt β at h = 0** at a specific point. -/
theorem correlationΛ_continuousAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_beta _ J β A

/-- **correlationΛ ContinuousAt h** at a specific point. -/
theorem correlationΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_field _ J h β A

/-- **correlationΛ DifferentiableAt h** at a specific point. -/
theorem correlationΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    DifferentiableAt ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiableAt_field _ J h β A

/-- **susceptibilityΛ ContinuousAt β at h = 0**. -/
theorem susceptibilityΛ_continuousAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_beta _ J β _

/-- **susceptibilityΛ DifferentiableAt β at h = 0**. -/
theorem susceptibilityΛ_differentiableAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_beta _ J β _

/-- **susceptibilityΛ ContinuousAt h**. -/
theorem susceptibilityΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_field _ J h β _

/-- **susceptibilityΛ DifferentiableAt h**. -/
theorem susceptibilityΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_field _ J h β _


end Ambient
end IsingModel
