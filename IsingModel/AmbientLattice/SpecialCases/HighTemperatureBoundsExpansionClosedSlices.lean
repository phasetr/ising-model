import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion partitionFunction closed-form trivial slice wrappers

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
partition function closed-form trivial-slice consistency wrappers
extracted from `HighTemperatureBoundsExpansionClosed.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero`
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero`

Each wrapper is a thin `change` + Λ-level pass-through to the
corresponding `partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_*_zero`
trivial-slice lemma. The theorem names are unchanged from the
former `HighTemperatureBoundsExpansionClosedForms` declarations.
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

end Ambient

end IsingModel
