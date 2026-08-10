import IsingModel.AmbientLattice.Exhaustion
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# Regularity of the stage correlation in the inverse temperature

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V`, a test set
`A : Finset V` and a stage index `n`. The stage correlation
`correlationAlongExhaustion G Λ p A n` is `correlationΛ` read on the induced subgraph of the
finite volume `Λ.volume n` when `A ⊆ Λ.volume n`, and `0` otherwise.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of that induced subgraph, and its Prop-valued hypothesis
list is empty: the coupling, the field and the inverse temperature are unconstrained reals.

Fixing the coupling and the field and varying the inverse temperature, the map
`β' ↦ correlationAlongExhaustion G Λ ⟨J, h, β'⟩ A n` has a derivative at every point — stated
in the existence form `∃ d, HasDerivAt … d β`, without naming the derivative — and is
differentiable and continuous, at a point and on all of `ℝ`. Statements are given at the zero
field and at an arbitrary field.

Derivative existence, and the pointwise continuity and differentiability at an arbitrary
field, are proved by splitting on `A ⊆ Λ.volume n`: on the covered branch the stage
correlation is the finite-volume correlation on the induced subgraph, which is differentiable
in the inverse temperature; off it the map is constant `0`, whose derivative is `0`. The
zero-field pointwise statements are read off zero-field derivative existence, and each
whole-`ℝ` `Continuous` or `Differentiable` statement from its pointwise counterpart.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **β-derivative of correlationAlongExhaustion** (Step 156, GJ §17.5):
The function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, rewrite by the first-order family
equation to the finite-volume correlation on the induced graph and apply
`hasDerivAt_correlation_beta`. In the non-subset case, the function is constant zero,
with derivative 0.

Reference: Glimm–Jaffe §17.5. -/
theorem correlationAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) d β := by
  by_cases h : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, 0, β'⟩ : IsingParams ℝ)) h]
    exact ⟨_, hasDerivAt_correlation_beta _ J β _⟩
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, 0, β'⟩ : IsingParams ℝ)) h]
    exact ⟨0, hasDerivAt_const β 0⟩

/-- **β-derivative of correlationAlongExhaustion at general h** (Step 257):
The function `fun β' => correlationAlongExhaustion G Λ ⟨J, h, β'⟩ A n` has a derivative
at β, at any `h` (extends Step 156 from h = 0).

Subset case: lift to finite-volume correlation and apply `hasDerivAt_correlation_beta_general_h`.
Non-subset case: constant zero. -/
theorem correlationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) d β := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact ⟨_, hasDerivAt_correlation_beta_general_h _ J h β _⟩
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact ⟨0, hasDerivAt_const β 0⟩

/-- **correlationAlongExhaustion DifferentiableAt β at h = 0** (Step 196, general G, Λ):
For any graph G with finite-edge-set exhaustion stages, the correlation along exhaustion
is differentiable in β at h = 0. Wraps `correlationAlongExhaustion_hasDerivAt_beta`. -/
theorem correlationAlongExhaustion_differentiableAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) β := by
  obtain ⟨_, hd⟩ := correlationAlongExhaustion_hasDerivAt_beta G Λ J β A n
  exact hd.differentiableAt

/-- **correlationAlongExhaustion ContinuousAt β at h = 0** (Step 196, general G, Λ):
Wraps `differentiableAt` to `continuousAt`. -/
theorem correlationAlongExhaustion_continuousAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    ContinuousAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) β :=
  (correlationAlongExhaustion_differentiableAt_beta_gen G Λ J β A n).continuousAt

/-- **correlationAlongExhaustion Continuous β at h = 0** (Step 196, general G, Λ).
Whole-ℝ Continuous version. -/
theorem correlationAlongExhaustion_continuous_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (A : Finset V) (n : ℕ) :
    Continuous
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) :=
  continuous_iff_continuousAt.mpr fun β =>
    correlationAlongExhaustion_continuousAt_beta_gen G Λ J β A n

/-- **correlationAlongExhaustion Differentiable β at h = 0** (Step 196, general G, Λ).
Whole-ℝ Differentiable version. -/
theorem correlationAlongExhaustion_differentiable_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (A : Finset V) (n : ℕ) :
    Differentiable ℝ
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) :=
  fun β => correlationAlongExhaustion_differentiableAt_beta_gen G Λ J β A n

/-- **correlationAlongExhaustion ContinuousAt β at general h** (Step 249, general G, Λ).
Extends Step 196 from h = 0 to general h.
Subset case: lift to finite-volume `correlation_continuous_beta_general_h`;
non-subset: constant 0. -/
theorem correlationAlongExhaustion_continuousAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ContinuousAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) β := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact (IsingModel.correlation_continuous_beta_general_h _ J h _).continuousAt
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact continuousAt_const

/-- **correlationAlongExhaustion DifferentiableAt β at general h** (Step 249, general G, Λ). -/
theorem correlationAlongExhaustion_differentiableAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) β := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact IsingModel.correlation_differentiable_beta_general_h _ J h _ β
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) h_sub]
    exact differentiableAt_const _

/-- **correlationAlongExhaustion Continuous β at general h** (Step 249, general G, Λ).
Whole-ℝ version. -/
theorem correlationAlongExhaustion_continuous_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (n : ℕ) :
    Continuous
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) :=
  continuous_iff_continuousAt.mpr fun β =>
    correlationAlongExhaustion_continuousAt_beta_general_h_gen G Λ J h β A n

/-- **correlationAlongExhaustion Differentiable β at general h** (Step 249, general G, Λ). -/
theorem correlationAlongExhaustion_differentiable_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (n : ℕ) :
    Differentiable ℝ
      (fun β' => correlationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A n) :=
  fun β => correlationAlongExhaustion_differentiableAt_beta_general_h_gen G Λ J h β A n

end IsingModel.Ambient
