import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic

/-!
# Ambient alongExhaustion correlation singleton trivial-slice wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
correlation singleton wrappers at the trivial parameter slices
`J = 0` and `β = 0` extracted from
`HighTemperatureBoundsCorrelationBasicSingleton.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero`
* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero`

The `J_zero` wrapper reduces to the `_odd_card_eq_zero` general
helper at singleton cardinality. The `β = 0` wrapper unfolds
`correlationAlongExhaustion` and dispatches on `{i} ⊆ Λ.volume n`,
falling back to the trivial `0` case when the singleton lies outside
the exhaustion. Theorem names are unchanged from the former
`HighTemperatureBoundsCorrelationBasic` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex singleton at J=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ 0 β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton at β=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_at_singleton_beta_zero
      G (Λ.volume n) J ⟨i, hAn (by simp)⟩
  · rw [dif_neg hAn]

end Ambient

end IsingModel
