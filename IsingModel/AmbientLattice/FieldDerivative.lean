import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.FieldDerivative

/-!
# h-derivative of correlationAlongExhaustion / magnetizationAlongExhaustion (GJ §17.6)

Shows that for any graph G whose exhaustion stages have finite edge sets,
the functions
`fun h' => correlationAlongExhaustion G Λ ⟨J, h', β⟩ A n` and
`fun h' => magnetizationAlongExhaustion G Λ ⟨J, h', β⟩ i n`
have a derivative at h.

Subset / membership case: lift to the finite-volume `hasDerivAt_correlation_field`.
Non-subset / non-member case: constant zero.

The `correlationAlongExhaustion` case split is discharged through the
first-order family equations `correlationAlongExhaustion_family_eq_of_subset`
and `correlationAlongExhaustion_family_eq_zero_of_not_subset`
(`AmbientLattice/Exhaustion.lean`) rather than by rebuilding the corresponding
function equation in-proof with `funext`, matching `BetaDerivative.lean`.

Companion to `IsingModel.AmbientLattice.BetaDerivative` (β-direction)
and `IsingModel.AmbientLattice.JDerivative` (J-direction).
The corresponding `Continuous*` / `Differentiable*` wrappers already
exist in `BetaDerivative.lean` under the `_gen` suffix.

Reference: Glimm–Jaffe §17.6 (covariance derivative w.r.t. external field). -/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **h-derivative of `correlationAlongExhaustion`** (GJ §17.6):
The function `fun h' => correlationAlongExhaustion G Λ ⟨J, h', β⟩ A n`
has a derivative at `h`.

Proof: split on `A ⊆ Λ.volume n`. In the subset case, rewrite by the
first-order family equation to the finite-volume correlation on the induced
graph and apply `hasDerivAt_correlation_field`. In the non-subset case, the
function is constant zero, with derivative 0. -/
theorem correlationAlongExhaustion_hasDerivAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun h' => correlationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) A n) d h := by
  by_cases h_sub : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact ⟨_, IsingModel.hasDerivAt_correlation_field _ J h β _⟩
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) h_sub]
    exact ⟨0, hasDerivAt_const h 0⟩

/-- **h-derivative of `magnetizationAlongExhaustion`** (GJ §17.6):
The function `fun h' => magnetizationAlongExhaustion G Λ ⟨J, h', β⟩ i n`
has a derivative at `h`.

Direct specialization of `correlationAlongExhaustion_hasDerivAt_field`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_hasDerivAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) d h := by
  unfold magnetizationAlongExhaustion
  exact correlationAlongExhaustion_hasDerivAt_field G Λ J h β {i} n

/-- **h-derivative of `partitionFunctionAlongExhaustion`** (GJ §17.6):
Direct specialization of `hasDerivAt_partitionFunctionΛ_field` at
`Λ := Λ.volume n`. -/
theorem partitionFunctionAlongExhaustion_hasDerivAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun h' => partitionFunctionAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) d h :=
  ⟨_, hasDerivAt_partitionFunctionΛ_field G (Λ.volume n) J h β⟩

/-- **h-derivative of `freeEnergyAlongExhaustion`** (GJ §17.6):
Direct specialization of `hasDerivAt_freeEnergyΛ_field` at
`Λ := Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_hasDerivAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun h' => freeEnergyAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) d h :=
  ⟨_, hasDerivAt_freeEnergyΛ_field G (Λ.volume n) J h β⟩

/-- **h-derivative of `susceptibilityAlongExhaustion`** (GJ §17.6,
general G). -/
theorem susceptibilityAlongExhaustion_hasDerivAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) d h := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact ⟨_, susceptibilityΛ_hasDerivAt_field G (Λ.volume n) J h β _⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact ⟨0, hasDerivAt_const h 0⟩

end IsingModel.Ambient
