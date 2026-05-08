import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Joint analyticity wrappers along an exhaustion

Narrow child module for general-graph `AnalyticAt` / `AnalyticOnNhd` wrappers
in the joint `(β, J, h)` parameters. This keeps callers that only need these
along-exhaustion forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Joint AnalyticAt + AnalyticOnNhd along-ex wrappers
(general G), for correlation, magnetization, susceptibility -/

/-- **Along-ex: correlation jointly AnalyticAt in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) (β, J, h) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_analyticAt_joint G (Λ.volume n) (liftFinset A hA) β J h
  · simp only [hA, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: correlation jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem correlationAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) Set.univ :=
  fun ⟨β, J, h⟩ _ => correlationAlongExhaustion_analyticAt_joint_gen G Λ A n β J h

/-- **Along-ex: magnetization jointly AnalyticAt** (general G). -/
theorem magnetizationAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_analyticAt_joint G (Λ.volume n) (liftFinset {i} hi) β J h
  · simp only [hi, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: magnetization jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem magnetizationAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  fun ⟨β, J, h⟩ _ => magnetizationAlongExhaustion_analyticAt_joint G Λ i n β J h

/-- **Along-ex: susceptibility jointly AnalyticAt** (general G). -/
theorem susceptibilityAlongExhaustion_analyticAt_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_analyticAt_joint G (Λ.volume n) ⟨i, hi⟩ β J h
  · simp only [hi, dif_neg, not_false_iff]
    exact analyticAt_const

/-- **Along-ex: susceptibility jointly AnalyticOnNhd over Set.univ** (general G). -/
theorem susceptibilityAlongExhaustion_analyticOnNhd_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibilityAlongExhaustion_analyticAt_joint_gen G Λ i n β J h

/-- **Along-ex: partitionFunction jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  partitionFunctionΛ_analyticAt_joint G (Λ.volume n) β J h

/-- **Along-ex: partitionFunction jointly AnalyticOnNhd over Set.univ**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_joint G (Λ.volume n)

/-- **Along-ex: freeEnergy jointly AnalyticAt**. -/
theorem freeEnergyAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  freeEnergyΛ_analyticAt_joint G (Λ.volume n) β J h

/-- **Along-ex: freeEnergy jointly AnalyticOnNhd over Set.univ**. -/
theorem freeEnergyAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  freeEnergyΛ_analyticOnNhd_joint G (Λ.volume n)

end Ambient
end IsingModel
