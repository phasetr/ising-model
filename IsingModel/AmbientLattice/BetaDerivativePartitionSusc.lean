import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.BetaDerivative

/-!
# Partition / free-energy / susceptibility β-derivative wrappers (GJ §17.5)

Narrow child module for the 4 `*AlongExhaustion_hasDerivAt_beta*`
wrappers (`partitionFunctionAlongExhaustion_hasDerivAt_beta`,
`freeEnergyAlongExhaustion_hasDerivAt_beta_general_h`,
`susceptibilityAlongExhaustion_hasDerivAt_beta_gen`,
`susceptibilityAlongExhaustion_hasDerivAt_beta_general_h_gen`)
extracted from `BetaDerivative.lean` in PR #2065. Each is a thin
pass-through to the corresponding Λ-level `hasDerivAt_*` lemma at
`Λ := Λ.volume n`; the susceptibility variants split on `i ∈ Λ.volume n`
and fall back to the constant-0 derivative on the off-stage branch.
The theorem names are unchanged from the former `BetaDerivative`
declarations.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **β-derivative of `partitionFunctionAlongExhaustion`** (GJ §17.5):
The function `fun β' => partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n`
has a derivative at `β`. Direct specialization of
`hasDerivAt_partitionFunctionΛ_beta` at `Λ := Λ.volume n`. -/
theorem partitionFunctionAlongExhaustion_hasDerivAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => partitionFunctionAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) d β :=
  ⟨_, hasDerivAt_partitionFunctionΛ_beta G (Λ.volume n) J h β⟩

/-- **β-derivative of `freeEnergyAlongExhaustion` at general `h`** (GJ §17.5).
Direct specialization of `hasDerivAt_freeEnergyΛ_beta_general_h` at
`Λ := Λ.volume n`. -/
theorem freeEnergyAlongExhaustion_hasDerivAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => freeEnergyAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) d β :=
  ⟨_, hasDerivAt_freeEnergyΛ_beta_general_h G (Λ.volume n) J h β⟩

/-- **β-derivative of `susceptibilityAlongExhaustion` at h = 0**
(GJ §17.5, general G). The `_gen` suffix avoids clash with potential
ℤ^d-specialized variants. -/
theorem susceptibilityAlongExhaustion_hasDerivAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact ⟨_, susceptibilityΛ_hasDerivAt_beta G (Λ.volume n) J β _⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact ⟨0, hasDerivAt_const β 0⟩

/-- **β-derivative of `susceptibilityAlongExhaustion` at general h**
(GJ §17.5, general G). -/
theorem susceptibilityAlongExhaustion_hasDerivAt_beta_general_h_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ∃ d : ℝ, HasDerivAt
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) d β := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact ⟨_, susceptibilityΛ_hasDerivAt_beta_general_h
              G (Λ.volume n) J h β _⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact ⟨0, hasDerivAt_const β 0⟩

end IsingModel.Ambient
