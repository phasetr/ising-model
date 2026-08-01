import IsingModel.AmbientLattice.Exhaustion
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# correlationAlongExhaustion field/J regularity wrappers (GJ §17.5–§17.6)

Narrow child module for the 6 `correlationAlongExhaustion_*_gen`
field/J regularity wrappers extracted from `BetaDerivative.lean` in
PR #2064. Theorems:
`correlationAlongExhaustion_continuousAt_field_gen`,
`correlationAlongExhaustion_continuous_field_gen`,
`correlationAlongExhaustion_differentiableAt_field_gen`,
`correlationAlongExhaustion_differentiable_field_gen`,
`correlationAlongExhaustion_continuous_J_gen`,
`correlationAlongExhaustion_differentiable_J_gen`. Each splits on
`A ⊆ Λ.volume n`; subset case lifts to the finite-volume `correlation_*`
lemma on the induced graph; non-subset case is the constant zero
function. Both branches are discharged by the first-order family
equations `correlationAlongExhaustion_family_eq_of_subset` and
`correlationAlongExhaustion_family_eq_zero_of_not_subset`
(`AmbientLattice/Exhaustion.lean`) instead of unfolding the `dite` by
hand. The theorem names are unchanged from the former
`BetaDerivative` declarations.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **correlationAlongExhaustion ContinuousAt h** (Step 205, general G, Λ).
Subset case: lift to finite-volume `correlation_continuousAt_field`; non-subset: constant 0. -/
theorem correlationAlongExhaustion_continuousAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ContinuousAt
      (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) h := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact IsingModel.correlation_continuousAt_field _ J h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact continuousAt_const

/-- **correlationAlongExhaustion Continuous in h** (Step 205, general G, Λ, whole-ℝ). -/
theorem correlationAlongExhaustion_continuous_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    Continuous
      (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) :=
  continuous_iff_continuousAt.mpr fun h =>
    correlationAlongExhaustion_continuousAt_field_gen G Λ J h β A n

/-- **correlationAlongExhaustion DifferentiableAt h** (Step 205, general G, Λ). -/
theorem correlationAlongExhaustion_differentiableAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) h := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact IsingModel.correlation_differentiableAt_field _ J h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact differentiableAt_const _

/-- **correlationAlongExhaustion Differentiable in h** (Step 205, general G, Λ, whole-ℝ). -/
theorem correlationAlongExhaustion_differentiable_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    Differentiable ℝ
      (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) :=
  fun h => correlationAlongExhaustion_differentiableAt_field_gen G Λ J h β A n

/-- **correlationAlongExhaustion Continuous in J** (Step 209, general G, Λ).
Subset case: lift to `correlation_continuous_J` on induced graph; non-subset: constant 0. -/
theorem correlationAlongExhaustion_continuous_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (A : Finset V) (n : ℕ) :
    Continuous
      (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact IsingModel.correlation_continuous_J _ h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact continuous_const

/-- **correlationAlongExhaustion Differentiable in J** (Step 212, general G, Λ).
Subset case: lift to `correlation_differentiable_J` on induced graph; non-subset: constant 0. -/
theorem correlationAlongExhaustion_differentiable_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (A : Finset V) (n : ℕ) :
    Differentiable ℝ
      (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact IsingModel.correlation_differentiable_J _ h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact differentiable_const _


end IsingModel.Ambient
