import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedCorrelation

/-!
# Ambient alongExhaustion correlation pair base wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
correlation pair base wrappers extracted from
`HighTemperatureBoundsCorrelationBasicPair.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg`

The `_le_one` wrapper unfolds `correlationAlongExhaustion` and
dispatches on `{i, j} ⊆ Λ.volume n`, falling back to `0 ≤ 1` when
the pair lies outside the exhaustion. The `_nonneg` wrapper is a
thin specialisation of the general
`correlationAlongExhaustion_high_temp_h_zero_nonneg` at the
two-point finset. Theorem names are unchanged from the former
`HighTemperatureBoundsCorrelationBasic` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex pair correlation ≤ 1 at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_le_one G (Λ.volume n) _ _
  · rw [dif_neg hAn]; exact zero_le_one

/-- **Along-exhaustion pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n :=
  correlationAlongExhaustion_high_temp_h_zero_nonneg G Λ J β hβJ {i, j} n

end Ambient

end IsingModel
