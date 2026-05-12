import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# magnetizationAlongExhaustion regularity wrappers (Step 213, GJ §17.5)

Narrow child module for the 10 `magnetizationAlongExhaustion`
regularity wrappers (9 with `_gen` suffix plus
`magnetizationAlongExhaustion_hasDerivAt_beta`): continuous +
differentiable + differentiableAt + hasDerivAt in
β / β_general_h / field / J directions. Extracted from
`BetaDerivative.lean` in PR #2063. Each is a thin pass-through to the
corresponding `correlationAlongExhaustion_*` lemma at `A = {i}`.
The theorem names are unchanged from the former `BetaDerivative`
declarations.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

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

/-- **magnetizationAlongExhaustion Continuous in β at general h** (Step 250, general G, Λ).
Extends Step 213 from h = 0 to general h via Step 249. -/
theorem magnetizationAlongExhaustion_continuous_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_continuous_beta_general_h_gen G Λ J h {i} n

/-- **magnetizationAlongExhaustion Differentiable in β at general h** (Step 250, general G, Λ). -/
theorem magnetizationAlongExhaustion_differentiable_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  simp only [magnetizationAlongExhaustion_apply]
  exact correlationAlongExhaustion_differentiable_beta_general_h_gen G Λ J h {i} n

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

/-- **β-derivative of `magnetizationAlongExhaustion` at `h = 0`** (GJ §17.5):
The function `fun β' => magnetizationAlongExhaustion G Λ ⟨J, 0, β'⟩ i n`
has a derivative at `β`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_beta` at
`A = {i}`. -/
theorem magnetizationAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_beta G Λ J β {i} n

/-- **β-derivative of `magnetizationAlongExhaustion` at general `h`** (GJ §17.5):
The function `fun β' => magnetizationAlongExhaustion G Λ ⟨J, h, β'⟩ i n`
has a derivative at `β`, at any `h`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_beta_general_h_gen`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_beta_general_h_gen G Λ J h β {i} n

end IsingModel.Ambient
