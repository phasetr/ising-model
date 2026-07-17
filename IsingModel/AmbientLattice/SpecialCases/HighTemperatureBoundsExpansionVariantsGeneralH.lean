import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion partition function high-temperature expansion (general h)

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
high-temperature `partitionFunctionAlongExhaustion` expansion
wrappers at general `h` extracted from
`HighTemperatureBoundsExpansionVariants.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion`
* `partitionFunctionAlongExhaustion_high_temp_expansion_subset_form`

Each wrapper unfolds `partitionFunctionAlongExhaustion` to the
ambient `partitionFunctionΛ_high_temp_expansion*` lemma via
`change` + `exact`. Theorem names are unchanged from the former
`HighTemperatureBoundsExpansion` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion partition function high-temperature expansion (general h)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑_i σ_i)`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion`
(Step 311). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        (∏ e ∈ (inducedGraph G (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h *
                  ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) := by
  change partitionFunctionΛ G (Λ.volume n) p = _
  exact partitionFunctionΛ_high_temp_expansion G (Λ.volume n) p

/-- **Along-exhaustion general-h subset expansion (GJ §18.3)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_X tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_subset_form`
(Step 301). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_subset_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
      ∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h *
                      ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) := by
  change partitionFunctionΛ G (Λ.volume n) p = _
  exact partitionFunctionΛ_high_temp_expansion_subset_form
    G (Λ.volume n) p

end Ambient

end IsingModel
