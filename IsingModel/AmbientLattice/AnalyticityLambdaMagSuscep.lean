import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# AmbientLattice/Analyticity magnetizationΛ + susceptibilityΛ wrappers

Narrow child module for the 14 magnetizationΛ + susceptibilityΛ +
correlationΛ continuousAt/differentiableAt/analyticAt/analyticOnNhd
joint wrappers. The theorem names are unchanged from the former
`Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **magnetizationΛ jointly `Continuous` in `(β, J, h)`** (Λ-layer). -/
theorem magnetizationΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_joint (inducedGraph G Λ) {i}

/-- **magnetizationΛ jointly `Differentiable ℝ` in `(β, J, h)`** (Λ-layer). -/
theorem magnetizationΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_joint (inducedGraph G Λ) {i}

/-- **susceptibilityΛ jointly `Continuous` in `(β, J, h)`** (Λ-layer). -/
theorem susceptibilityΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_joint (inducedGraph G Λ) i

/-- **susceptibilityΛ jointly `Differentiable ℝ` in `(β, J, h)`** (Λ-layer). -/
theorem susceptibilityΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_joint (inducedGraph G Λ) i

/-- **correlationΛ jointly `ContinuousAt`** (Λ-layer). -/
theorem correlationΛ_continuousAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _))
    (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      correlationΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlationΛ_continuous_joint G Λ A).continuousAt

/-- **correlationΛ jointly `DifferentiableAt ℝ`** (Λ-layer). -/
theorem correlationΛ_differentiableAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _))
    (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      correlationΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlationΛ_differentiable_joint G Λ A).differentiableAt

/-- **magnetizationΛ jointly `ContinuousAt`** (Λ-layer). -/
theorem magnetizationΛ_continuousAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetizationΛ_continuous_joint G Λ i).continuousAt

/-- **magnetizationΛ jointly `DifferentiableAt ℝ`** (Λ-layer). -/
theorem magnetizationΛ_differentiableAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetizationΛ_differentiable_joint G Λ i).differentiableAt

/-- **susceptibilityΛ jointly `ContinuousAt`** (Λ-layer). -/
theorem susceptibilityΛ_continuousAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibilityΛ_continuous_joint G Λ i).continuousAt

/-- **susceptibilityΛ jointly `DifferentiableAt ℝ`** (Λ-layer). -/
theorem susceptibilityΛ_differentiableAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibilityΛ_differentiable_joint G Λ i).differentiableAt

/-- **magnetizationΛ jointly `AnalyticAt ℝ`** (Λ-layer). -/
theorem magnetizationΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) (β, J, h) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_analyticAt_joint (inducedGraph G Λ) {i} β J h

/-- **magnetizationΛ jointly `AnalyticOnNhd ℝ`** over `Set.univ` (Λ-layer). -/
theorem magnetizationΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) Set.univ :=
  fun ⟨β, J, h⟩ _ => magnetizationΛ_analyticAt_joint G Λ i β J h

/-- **susceptibilityΛ jointly `AnalyticAt ℝ`** (Λ-layer). -/
theorem susceptibilityΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) (β, J, h) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_analyticAt_joint (inducedGraph G Λ) i β J h

/-- **susceptibilityΛ jointly `AnalyticOnNhd ℝ`** over `Set.univ` (Λ-layer). -/
theorem susceptibilityΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ i) Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibilityΛ_analyticAt_joint G Λ i β J h


end Ambient

end IsingModel
