import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion log Z ratio sandwich / bound wrappers at h = 0

Narrow child module for the single surviving §18.3-§18.4 ambient
alongExhaustion
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle`
wrapper (general variant). It is a thin pass-through to the
corresponding `log_partitionFunctionΛ_*` ambient lemma. The former
ferromagnetic `ratio_sandwich_bundle` variant and the four `ratio_bound`
variants (`J = 0`, `β = 0`, the general `ratio_bound_bundle`, and the
ferromagnetic `ratio_bound_bundle_ferromagnetic`) were removed as unused
pass-through wrappers (see the `## Removed` note below). The theorem name
is unchanged from the former `HighTemperatureBoundsRatioLogFe`
declarations.
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

/-! ## Removed: log Z `ratio_bound` wrappers

The `ratio_bound{,_beta_zero}` slice-singleton wrappers together with
the `ratio_bound_bundle`, `ratio_bound_bundle_ferromagnetic`, and
`ratio_sandwich_bundle_ferromagnetic` conjunction wrappers were removed
as unused pass-through wrappers.
-/

end Ambient

end IsingModel
