import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedCorrelation

/-!
# Ambient alongExhaustion partitionFunction closed-form wrappers at h = 0

Narrow child module for the three §18.3-§18.4 ambient alongExhaustion
partition function closed-form wrappers extracted from
`HighTemperatureBoundsExpansionClosedForms.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero`
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero`
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`

Each wrapper is a thin pass-through to the corresponding
`partitionFunctionΛ_*` ambient lemma. Theorem names are unchanged
from the former `HighTemperatureBoundsExpansionClosedForms`
declarations.
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

/-! ## Moved: 2 correlation closed-form / nonnegativity wrappers

The two ambient alongExhaustion correlation wrappers
(`correlationAlongExhaustion_high_temp_h_zero_nonneg`,
`correlationAlongExhaustion_high_temp_expansion_h_zero_closed`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedCorrelation`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
