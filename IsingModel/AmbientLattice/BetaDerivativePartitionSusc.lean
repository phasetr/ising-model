import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.BetaDerivative

/-!
# Inverse-temperature derivatives of the stage partition function, free energy, susceptibility

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V` and a stage
index `n`. Each quantity is read on the finite volume `Λ.volume n`: the stage partition
function and the stage free energy are `partitionFunctionΛ` and `freeEnergyΛ` there, and the
stage susceptibility is `susceptibilityΛ` at the lifted site when the site lies in that
volume, and `0` otherwise.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`, and its
Prop-valued hypothesis list is empty.

Fixing the remaining parameters and varying the inverse temperature, the stage partition
function and the stage free energy have a derivative at every point, and so does the stage
susceptibility, at the zero field and at an arbitrary field alike. Every statement is in the
existence form `∃ d, HasDerivAt … d β`, without naming the derivative.

The partition-function and free-energy statements are specializations of the corresponding
finite-volume statements at `Λ.volume n`. The susceptibility statements split on whether the
site lies in `Λ.volume n`: on the covered branch they specialize the finite-volume
susceptibility statement at the lifted site, and off it the map is constant `0`, whose
derivative is `0`.
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
