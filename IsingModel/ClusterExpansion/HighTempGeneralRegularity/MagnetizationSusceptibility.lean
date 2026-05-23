import IsingModel.ClusterExpansion.HighTempGeneralRegularity.CorrelationRegularity

/-!
# High-temperature magnetization and susceptibility regularity

Mechanical child split from `ClusterExpansion.HighTempGeneralRegularity`.
-/

namespace IsingModel

open Finset
/-- **Magnetization jointly `Continuous` in `(β, J, h)`**: direct
corollary of `correlation_continuous_joint` at `A = {i}`. -/
theorem magnetization_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetization G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetization
  exact correlation_continuous_joint G {i}

/-- **Magnetization jointly `Differentiable ℝ` in `(β, J, h)`**:
direct corollary of `correlation_differentiable_joint` at `A = {i}`. -/
theorem magnetization_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetization G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetization
  exact correlation_differentiable_joint G {i}

/-- **Susceptibility jointly `Continuous` in `(β, J, h)`**: finite sum of
`truncated2 = correlation {i,j} - correlation {i} · correlation {j}`,
each Continuous joint. -/
theorem susceptibility_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  have heq : (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine continuous_finset_sum _ (fun j _ => ?_)
  unfold truncated2
  exact (correlation_continuous_joint G {i, j}).sub
    ((correlation_continuous_joint G {i}).mul
      (correlation_continuous_joint G {j}))

/-- **Susceptibility jointly `Differentiable ℝ` in `(β, J, h)`**:
finite sum of differentiable `truncated2` summands. -/
theorem susceptibility_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  have heq : (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine Differentiable.fun_sum (fun j _ => ?_)
  unfold truncated2
  exact (correlation_differentiable_joint G {i, j}).sub
    ((correlation_differentiable_joint G {i}).mul
      (correlation_differentiable_joint G {j}))

/-- **Correlation jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem correlation_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => correlation G ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlation_continuous_joint G A).continuousAt

/-- **Correlation jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem correlation_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ
      (fun q : ℝ × ℝ × ℝ => correlation G ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlation_differentiable_joint G A).differentiableAt

/-- **Magnetization jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem magnetization_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetization G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetization_continuous_joint G i).continuousAt

/-- **Magnetization jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem magnetization_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetization G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetization_differentiable_joint G i).differentiableAt

/-- **Susceptibility jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem susceptibility_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibility G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibility_continuous_joint G i).continuousAt

/-- **Susceptibility jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem susceptibility_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibility G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibility_differentiable_joint G i).differentiableAt

/-- **Magnetization jointly `AnalyticAt ℝ` in `(β, J, h)`**:
direct corollary of `correlation_analyticAt_joint` at `A = {i}`. -/
theorem magnetization_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => magnetization G ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) := by
  unfold magnetization
  exact correlation_analyticAt_joint G {i} β J h

/-- **Magnetization jointly `AnalyticOnNhd ℝ` over `Set.univ`**. -/
theorem magnetization_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => magnetization G ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => magnetization_analyticAt_joint G i β J h

/-- **Susceptibility jointly `AnalyticAt ℝ` in `(β, J, h)`**: finite
sum of analytic `truncated2 = corr({i,j}) − corr({i})·corr({j})`. -/
theorem susceptibility_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) := by
  have heq : (fun p : ℝ × ℝ × ℝ =>
        susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
  unfold truncated2
  exact (correlation_analyticAt_joint G {i, j} β J h).sub
    ((correlation_analyticAt_joint G {i} β J h).mul
      (correlation_analyticAt_joint G {j} β J h))

/-- **Susceptibility jointly `AnalyticOnNhd ℝ` over `Set.univ`**. -/
theorem susceptibility_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibility_analyticAt_joint G i β J h

end IsingModel
