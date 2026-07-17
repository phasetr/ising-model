import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion log Z ratio sandwich / bound wrappers at h = 0

Narrow child module for the six §18.3-§18.4 ambient alongExhaustion
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_*`
wrappers: the two `ratio_sandwich_bundle` variants (general and
ferromagnetic) and the four `ratio_bound` variants (`J = 0`, `β = 0`,
the general `ratio_bound_bundle`, and the ferromagnetic
`ratio_bound_bundle_ferromagnetic`). Each wrapper is a thin
pass-through to the corresponding `log_partitionFunctionΛ_*` ambient
lemma. The theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFe` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex log Z ratio sandwich bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) := by
  change (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ))
      - Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨0, 0, β⟩ : IsingParams ℝ)) ∧ _) ∧
      (_ ≤ Real.log (partitionFunctionΛ G (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G (Λ.volume n)
              (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧ _)
  exact log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G (Λ.volume n) J β hβJ

/-! ## Moved: 1 ferromagnetic log Z ratio_sandwich_bundle wrapper

The ferromagnetic log Z `ratio_sandwich_bundle_ferromagnetic`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: log Z `ratio_bound` wrappers

The four
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound*`
wrappers (`J = 0`, `β = 0`, `_bundle`, `_bundle_ferromagnetic`) now
live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnly`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
