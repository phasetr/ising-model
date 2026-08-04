import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.BetaDerivativeFieldJ
import IsingModel.JDerivative

/-!
# J-derivative of correlationAlongExhaustion / magnetizationAlongExhaustion (GJ §17.5)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the functions
`fun J' => correlationAlongExhaustion G Λ ⟨J', h, β⟩ A n` and
`fun J' => magnetizationAlongExhaustion G Λ ⟨J', h, β⟩ i n`
have a derivative at J.

Subset / membership case: lift to the finite-volume `hasDerivAt_correlation_J`.
Non-subset / non-member case: constant zero.

The `correlationAlongExhaustion` case split is discharged through the
first-order family equations `correlationAlongExhaustion_family_eq_of_subset`
and `correlationAlongExhaustion_family_eq_zero_of_not_subset`
(`AmbientLattice/Exhaustion.lean`) rather than by rebuilding the corresponding
function equation in-proof with `funext`, matching `BetaDerivative.lean`.

Companion to `IsingModel.AmbientLattice.BetaDerivative` (β-direction).
The corresponding `Continuous*` / `Differentiable*` wrappers already
exist in `BetaDerivative.lean` under the `_gen` suffix.

Reference: Glimm–Jaffe §17.5–§17.6 (covariance-form thermodynamic
derivative identities). -/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **J-derivative of `correlationAlongExhaustion`** (GJ §17.5):
The function `fun J' => correlationAlongExhaustion G Λ ⟨J', h, β⟩ A n`
has a derivative at `J`.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, rewrite by the
first-order family equation to the finite-volume correlation on the induced
graph and apply `hasDerivAt_correlation_J`. In the non-subset case, the
function is constant zero, with derivative 0. -/
theorem correlationAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => correlationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) d J := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact ⟨_, IsingModel.hasDerivAt_correlation_J _ J h β _⟩
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) h_sub]
    exact ⟨0, hasDerivAt_const J 0⟩

/-- **J-derivative of `magnetizationAlongExhaustion`** (GJ §17.5):
The function `fun J' => magnetizationAlongExhaustion G Λ ⟨J', h, β⟩ i n`
has a derivative at `J`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_J` at
`A = {i}`, since `magnetizationAlongExhaustion = correlationAlongExhaustion`
at `A = {i}` by definition. -/
theorem magnetizationAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) d J := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_J G Λ J h β {i} n

/-- **J-derivative of `partitionFunctionAlongExhaustion`** (GJ §17.5):
Direct specialization of `hasDerivAt_partitionFunctionΛ_J` at
`Λ := Λ.volume n`. -/
theorem partitionFunctionAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => partitionFunctionAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) d J :=
  ⟨_, hasDerivAt_partitionFunctionΛ_J G (Λ.volume n) J h β⟩

/-- **J-derivative of `freeEnergyAlongExhaustion`** (GJ §17.5):
Direct specialization of `hasDerivAt_freeEnergyΛ_J` at
`Λ := Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_hasDerivAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => freeEnergyAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) d J :=
  ⟨_, hasDerivAt_freeEnergyΛ_J G (Λ.volume n) J h β⟩

/-- **J-derivative of `susceptibilityAlongExhaustion`** (GJ §17.5,
general G). -/
theorem susceptibilityAlongExhaustion_hasDerivAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun J' => susceptibilityAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) d J := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact ⟨_, susceptibilityΛ_hasDerivAt_J G (Λ.volume n) J h β _⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact ⟨0, hasDerivAt_const J 0⟩

/-- **`correlationAlongExhaustion` ContinuousAt J** (general G). -/
theorem correlationAlongExhaustion_continuousAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ContinuousAt
      (fun J' => correlationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) J :=
  (correlationAlongExhaustion_continuous_J_gen G Λ h β A n).continuousAt

/-- **`correlationAlongExhaustion` DifferentiableAt J** (general G). -/
theorem correlationAlongExhaustion_differentiableAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => correlationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) J :=
  (correlationAlongExhaustion_differentiable_J_gen G Λ h β A n).differentiableAt

end IsingModel.Ambient
