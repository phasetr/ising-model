import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# Ambient alongExhaustion closed-form / correlation wrappers at h = 0

Narrow child module for five §18.3-§18.4 ambient alongExhaustion
closed-form and correlation wrappers extracted from
`HighTemperatureBoundsExpansionClosedForms.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero`,
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero`,
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`,
* `correlationAlongExhaustion_high_temp_h_zero_nonneg`,
* `correlationAlongExhaustion_high_temp_expansion_h_zero_closed`.

Each wrapper is a thin pass-through to the corresponding
`partitionFunctionΛ_*` or `correlationΛ_*` ambient lemma. Theorem
names are unchanged from the former
`HighTemperatureBoundsExpansionClosedForms` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion FV (3.45) at `J = 0` consistency check**:
`Z_n(⟨0, 0, β⟩) = 2^|Λ_n|`. Per-stage Step 314 abstract. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    G (Λ.volume n) β

/-- **Along-exhaustion FV (3.45) at `β = 0` consistency check**:
`Z_n(⟨J, 0, 0⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    G (Λ.volume n) J

/-- **Along-exhaustion partition function high-temperature closed form (FV §3.7.3 eq. (3.45))**:
at every stage `n`,
`partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n = 2^|Λ.volume n| · cosh(βJ)^|E_{Λ.volume n}|
  · ∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(βJ)^|X|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`
(Step 285). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑(Λ.volume n),
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β

/-- **Along-exhaustion correlation nonnegativity from FV (3.46)**:
under `0 ≤ β * J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n`.
When `A ⊄ Λ.volume n`, equals `0` by definition. When `A ⊆`, lifts via
`liftFinset` and applies `correlationΛ_high_temp_h_zero_nonneg` (Step 294). -/
theorem correlationAlongExhaustion_high_temp_h_zero_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_nonneg G (Λ.volume n) J β hβJ
      (liftFinset A hAn)
  · rw [dif_neg hAn]

/-- **Along-exhaustion correlation high-temperature closed form (FV §3.7.3 eq. (3.46))**:
at every stage `n` with `A ⊆ Λ.volume n`, the per-stage correlation
admits the FV (3.46) ratio form. When `A ⊄ Λ.volume n`, the
along-exhaustion correlation is `0` by definition.

For the `A ⊆` case, lifts via `liftFinset` and applies
`correlationΛ_high_temp_expansion_h_zero_closed` (Step 285). -/
theorem correlationAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n =
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
            Even ((if v ∈ liftFinset A hAn then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  unfold correlationAlongExhaustion
  rw [dif_pos hAn]
  exact correlationΛ_high_temp_expansion_h_zero_closed G (Λ.volume n) J β
    (liftFinset A hAn)

end Ambient

end IsingModel
