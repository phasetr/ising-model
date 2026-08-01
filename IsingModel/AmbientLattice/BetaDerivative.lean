import IsingModel.AmbientLattice.Exhaustion
import IsingModel.BetaDerivative
import IsingModel.FieldDerivative

/-!
# β-derivative of correlationAlongExhaustion (GJ §17.5)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the function `fun β' => correlationAlongExhaustion G Λ ⟨J, 0, β'⟩ A n` has a derivative at β.

When `A ⊆ Λ.volume n` the function reduces to the finite-volume correlation
(differentiable by `hasDerivAt_correlation_beta`); otherwise it is constant zero.

The four case-splitting proofs below discharge both branches through the
first-order family equations `correlationAlongExhaustion_family_eq_of_subset`
and `correlationAlongExhaustion_family_eq_zero_of_not_subset`
(`AmbientLattice/Exhaustion.lean`) instead of rebuilding the corresponding
function equation in-proof with `funext` and the pointwise
`correlationAlongExhaustion_of_{subset, not_subset}` lemmas.

Step 156, GJ §17.5 (first step toward ∞-vol β-derivative). -/

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

/-! ## Moved: correlationAlongExhaustion field/J regularity wrappers

The 6 `correlationAlongExhaustion_*_gen` field/J regularity wrappers
(`continuousAt_field`, `continuous_field`, `differentiableAt_field`,
`differentiable_field`, `continuous_J`, `differentiable_J`) now live
in `IsingModel.Ambient.BetaDerivativeFieldJ`
(`AmbientLattice/BetaDerivativeFieldJ.lean`).
-/

/-! ## Moved: magnetizationAlongExhaustion regularity wrappers

The 10 `magnetizationAlongExhaustion` regularity wrappers (9 with
`_gen` suffix plus `magnetizationAlongExhaustion_hasDerivAt_beta`):
continuous + differentiable + differentiableAt + hasDerivAt in
β / β_general_h / field / J directions. They now live in
`IsingModel.Ambient.BetaDerivativeMagnetization`
(`AmbientLattice/BetaDerivativeMagnetization.lean`).
-/


/-! ## Moved: partition / free-energy / susceptibility β-derivative wrappers

The 4 `*AlongExhaustion_hasDerivAt_beta*` wrappers
(`partitionFunctionAlongExhaustion_hasDerivAt_beta`,
`freeEnergyAlongExhaustion_hasDerivAt_beta_general_h`,
`susceptibilityAlongExhaustion_hasDerivAt_beta_gen`,
`susceptibilityAlongExhaustion_hasDerivAt_beta_general_h_gen`) now
live in `IsingModel.Ambient.BetaDerivativePartitionSusc`
(`AmbientLattice/BetaDerivativePartitionSusc.lean`).
-/


end IsingModel.Ambient
