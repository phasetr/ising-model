import IsingModel.AmbientLattice.Exhaustion
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# Regularity of the stage correlation in the field and in the coupling

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V`, a test set
`A : Finset V` and a stage index `n`, about the stage correlation
`correlationAlongExhaustion G Λ p A n`: `correlationΛ` read on the induced subgraph of the
finite volume `Λ.volume n` when `A ⊆ Λ.volume n`, and `0` otherwise.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of that induced subgraph, and its Prop-valued hypothesis
list is empty.

Holding the coupling and the inverse temperature fixed and varying the field, the map
`h' ↦ correlationAlongExhaustion G Λ ⟨J, h', β⟩ A n` is continuous and differentiable, at a
point and on all of `ℝ`. Holding the field and the inverse temperature fixed and varying the
coupling, the map `J' ↦ correlationAlongExhaustion G Λ ⟨J', h, β⟩ A n` is continuous and
differentiable on all of `ℝ`; in the coupling direction only the whole-`ℝ` forms are stated.

The pointwise field statements and the coupling statements are proved by splitting on
`A ⊆ Λ.volume n`: the covered branch lifts to the finite-volume correlation on the induced
subgraph, and off it the map is constant `0`. The whole-`ℝ` field statements are wrappers
around their pointwise counterparts.
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
