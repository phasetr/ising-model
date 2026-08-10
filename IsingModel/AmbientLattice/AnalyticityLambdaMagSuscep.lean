import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Joint regularity of the Λ-restricted magnetization, susceptibility and correlation

Statements for an ambient graph `G : SimpleGraph V`, a finite volume `Λ : Finset V` and
either a site `i : ↑Λ` or a test set `A : Finset ↑Λ`, about the maps on `ℝ × ℝ × ℝ` sending
`(β, J, h)` to `magnetizationΛ G Λ ⟨J, h, β⟩ i`, to `susceptibilityΛ G Λ ⟨J, h, β⟩ i` and to
`correlationΛ G Λ ⟨J, h, β⟩ A`.

The magnetization and the susceptibility carry the full ladder in the joint variable:
`ContinuousAt` and `DifferentiableAt ℝ` at an arbitrary point, `Continuous` and
`Differentiable ℝ` on the whole space, `AnalyticAt ℝ` at an arbitrary point, and
`AnalyticOnNhd ℝ` over `Set.univ`, so no parameter value is excluded. The correlation
appears here in the pointwise `ContinuousAt` and `DifferentiableAt ℝ` forms alone.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`, and its Prop-valued hypothesis list is empty; `Λ` is
unrestricted, and a site `i : ↑Λ` exists only when `Λ` does. The `Continuous`,
`Differentiable ℝ` and `AnalyticAt ℝ` statements rewrite the Λ-layer definition to the
base layer at `inducedGraph G Λ` — the magnetization through
`magnetizationΛ G Λ p i = correlationΛ G Λ p {i}`, the susceptibility through the
unfolding of `susceptibilityΛ`. The `ContinuousAt` and `DifferentiableAt ℝ` statements are
then specializations of the whole-space ones, and each `AnalyticOnNhd ℝ` statement is its
`AnalyticAt ℝ` counterpart applied at every point.
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
