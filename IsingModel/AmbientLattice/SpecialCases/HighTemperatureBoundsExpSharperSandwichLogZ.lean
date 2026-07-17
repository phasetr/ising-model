import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion sharper-exp log Z sandwich wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
sharper-exp `log_partitionFunctionAlongExhaustion_..._sandwich_exp`
wrapper extracted from `HighTemperatureBoundsExpSharperSandwich.lean`:

* `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp`

The wrapper is a thin `change` + Λ-level pass-through to
`log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp`.
The theorem name is unchanged from the former
`HighTemperatureBoundsExpSharper` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex sharper log Z sandwich at stage `n`**: under `0 ≤ β·J`,
`|Λ_n|·log 2 + |E_n|·log cosh(β·J) ≤ log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change ((Λ.volume n).card : ℝ) * _ + _ * _ ≤
      Real.log (partitionFunctionΛ G (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel
