import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Ambient joint regularity wrappers

This module contains general-graph joint `Continuous`, `Differentiable`,
`ContinuousAt`, and `DifferentiableAt` APIs for along-exhaustion correlation,
magnetization, and susceptibility. It is split out of the legacy ambient
special-cases module so concrete joint wrappers can depend on a narrower child
path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion joint regularity wrappers -/

/-- **Along-ex: correlation jointly Continuous in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_continuous_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset A hA)
  · simp only [hA, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: correlation jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_differentiable_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_differentiable_joint G (Λ.volume n) (liftFinset A hA)
  · simp only [hA, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: magnetization jointly Continuous in `(β, J, h)`** (general G). -/
theorem magnetizationAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_continuous_joint G (Λ.volume n) (liftFinset {i} hi)
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem magnetizationAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_differentiable_joint G (Λ.volume n) (liftFinset {i} hi)
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: susceptibility jointly Continuous in `(β, J, h)`** (general G). -/
theorem susceptibilityAlongExhaustion_continuous_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_joint G (Λ.volume n) ⟨i, hi⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: susceptibility jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_joint G (Λ.volume n) ⟨i, hi⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: correlation jointly ContinuousAt** (general G). -/
theorem correlationAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  (correlationAlongExhaustion_continuous_joint_gen G Λ A n).continuousAt

/-- **Along-ex: correlation jointly DifferentiableAt** (general G). -/
theorem correlationAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  (correlationAlongExhaustion_differentiable_joint_gen G Λ A n).differentiableAt

/-- **Along-ex: magnetization jointly ContinuousAt** (general G). -/
theorem magnetizationAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_continuous_joint G Λ i n).continuousAt

/-- **Along-ex: magnetization jointly DifferentiableAt** (general G). -/
theorem magnetizationAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (magnetizationAlongExhaustion_differentiable_joint G Λ i n).differentiableAt

/-- **Along-ex: susceptibility jointly ContinuousAt** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_continuous_joint_gen G Λ i n).continuousAt

/-- **Along-ex: susceptibility jointly DifferentiableAt** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  (susceptibilityAlongExhaustion_differentiable_joint_gen G Λ i n).differentiableAt

end Ambient
end IsingModel
