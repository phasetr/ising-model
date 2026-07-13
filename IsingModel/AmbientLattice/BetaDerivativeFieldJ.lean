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
function. The theorem names are unchanged from the former
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
  · have heq : (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) =
               (fun h' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                  (⟨J, h', β⟩ : IsingParams ℝ) (liftFinset A h_sub)) := by
      funext h'
      rw [correlationAlongExhaustion_of_subset G Λ _ h_sub, correlationΛ_apply]
    rw [heq]
    exact IsingModel.correlation_continuousAt_field _ J h β _
  · have heq : (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) =
               (fun _ => (0 : ℝ)) := by
      funext h'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h_sub
    rw [heq]
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
  · have heq : (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) =
               (fun h' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                  (⟨J, h', β⟩ : IsingParams ℝ) (liftFinset A h_sub)) := by
      funext h'
      rw [correlationAlongExhaustion_of_subset G Λ _ h_sub, correlationΛ_apply]
    rw [heq]
    exact IsingModel.correlation_differentiableAt_field _ J h β _
  · have heq : (fun h' => correlationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) A n) =
               (fun _ => (0 : ℝ)) := by
      funext h'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h_sub
    rw [heq]
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
  · have heq : (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) =
               (fun J' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                  (⟨J', h, β⟩ : IsingParams ℝ) (liftFinset A h_sub)) := by
      funext J'
      rw [correlationAlongExhaustion_of_subset G Λ _ h_sub, correlationΛ_apply]
    rw [heq]
    exact IsingModel.correlation_continuous_J _ h β _
  · have heq : (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) =
               (fun _ => (0 : ℝ)) := by
      funext J'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h_sub
    rw [heq]
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
  · have heq : (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) =
               (fun J' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                  (⟨J', h, β⟩ : IsingParams ℝ) (liftFinset A h_sub)) := by
      funext J'
      rw [correlationAlongExhaustion_of_subset G Λ _ h_sub, correlationΛ_apply]
    rw [heq]
    exact IsingModel.correlation_differentiable_J _ h β _
  · have heq : (fun J' => correlationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) A n) =
               (fun _ => (0 : ℝ)) := by
      funext J'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h_sub
    rw [heq]
    exact differentiable_const _


end IsingModel.Ambient
