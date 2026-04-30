import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# β-derivative of correlationAlongExhaustion (GJ §17.5)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

When `A ⊆ Λ.volume n` the function reduces to the finite-volume correlation
(differentiable by `hasDerivAt_correlation_beta`); otherwise it is constant zero.

Step 156, GJ §17.5 (first step toward ∞-vol β-derivative). -/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **β-derivative of correlationAlongExhaustion** (Step 156, GJ §17.5):
The function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, unfold to the finite-volume correlation
on the induced graph and apply `hasDerivAt_correlation_beta`. In the non-subset case,
the function is constant zero, with derivative 0.

Reference: Glimm–Jaffe §17.5. -/
theorem correlationAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) d β := by
  by_cases h : A ⊆ Λ.volume n
  · -- Rewrite to the induced-graph correlation
    have heq : (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) =
               (fun β' => IsingModel.correlation (inducedGraph G (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) (liftFinset A h)) := by
      funext β'
      rw [correlationAlongExhaustion_of_subset G Λ _ h, correlationΛ_apply]
    rw [heq]
    exact ⟨_, hasDerivAt_correlation_beta _ J β _⟩
  · -- Function is constant zero
    have heq : (fun β' => correlationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A n) =
               fun _ => 0 := by
      funext β'
      exact correlationAlongExhaustion_of_not_subset G Λ _ h
    rw [heq]
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

/-! ## Step 213: magnetizationAlongExhaustion regularity (β/h/J directions) -/

/-- **magnetizationAlongExhaustion Continuous in β at h = 0** (Step 213, general G, Λ).
Reduces to `correlationAlongExhaustion_continuous_beta_gen` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_continuous_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    Continuous
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_continuous_beta_gen G Λ J {i} n

/-- **magnetizationAlongExhaustion Differentiable in β at h = 0** (Step 213, general G, Λ). -/
theorem magnetizationAlongExhaustion_differentiable_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_differentiable_beta_gen G Λ J {i} n

/-- **magnetizationAlongExhaustion Continuous in h** (Step 213, general G, Λ). -/
theorem magnetizationAlongExhaustion_continuous_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Continuous
      (fun h' => magnetizationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_continuous_field_gen G Λ J β {i} n

/-- **magnetizationAlongExhaustion Differentiable in h** (Step 213, general G, Λ). -/
theorem magnetizationAlongExhaustion_differentiable_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ
      (fun h' => magnetizationAlongExhaustion G Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_differentiable_field_gen G Λ J β {i} n

/-- **magnetizationAlongExhaustion Continuous in J** (Step 213, general G, Λ). -/
theorem magnetizationAlongExhaustion_continuous_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Continuous
      (fun J' => magnetizationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_continuous_J_gen G Λ h β {i} n

/-- **magnetizationAlongExhaustion Differentiable in J** (Step 213, general G, Λ). -/
theorem magnetizationAlongExhaustion_differentiable_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ
      (fun J' => magnetizationAlongExhaustion G Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_differentiable_J_gen G Λ h β {i} n

end IsingModel.Ambient
