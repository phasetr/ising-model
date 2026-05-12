import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion

/-!
# Ambient alongExhaustion high-temp expansion variant wrappers at h = 0

Narrow child module for 4 ambient alongExhaustion §18.3-§18.4
high-temperature expansion variant wrappers covering
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero`,
`partitionFunctionAlongExhaustion_high_temp_expansion`,
`partitionFunctionAlongExhaustion_high_temp_expansion_subset_form`,
and the `one_le_sum_pow_tanh_even_subgraph_alongExhaustion` helper.
Theorem names are unchanged from the former
`HighTemperatureBoundsExpansion` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-- **Along-exhaustion partition function high-temperature expansion at `h = 0`**:
`Z_n(⟨J, 0, β⟩) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`
at every stage `n`. Per-stage application of
`partitionFunctionΛ_high_temp_expansion_h_zero` (Step 312). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n =
      Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        ∏ e ∈ (inducedGraph G (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero G (Λ.volume n) J β

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

/-- **Along-exhaustion high-temperature even-subgraph sum is `≥ 1`**:
under `0 ≤ β * J`, at every stage `n`,
`∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(β J)^|X| ≥ 1`.
Per-stage application of `one_le_sum_pow_tanh_even_subgraph_Λ`
(Step 296). -/
theorem one_le_sum_pow_tanh_even_subgraph_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_Λ G (Λ.volume n) J β hβJ

end Ambient

end IsingModel
