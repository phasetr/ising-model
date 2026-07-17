import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion log Z ratio_bound singleton wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound{,_beta_zero}`
slice-singleton wrappers extracted from
`HighTemperatureBoundsRatioLogFeLogBoundOnly.lean`:

* `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound`
  (J = 0 trivial slice)
* `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero`
  (β = 0 trivial slice)

Each wrapper unfolds `partitionFunctionAlongExhaustion` to
`log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound*`
via `change` + `exact`. Theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFeLogBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex log Z ratio bound at J=0, stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨0, 0, β⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    G (Λ.volume n) J β hβJ

/-- **Along-ex log Z ratio bound at β=0, stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card := by
  change Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨J, 0, 0⟩ : IsingParams ℝ)) ≤ _
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β hβJ

end Ambient

end IsingModel
