import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonTrivial

/-!
# Ambient alongExhaustion correlation singleton wrappers at h = 0

Narrow child module for four §18.3-§18.4 ambient alongExhaustion
correlation singleton wrappers extracted from
`HighTemperatureBoundsCorrelationBasicSingletonBundle.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero`,
* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero`,
* `correlationAlongExhaustion_high_temp_h_zero_at_singleton`,
* `correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one`.

Internal dependency `_eq_zero_le_one` → `_at_singleton` stays inside
the child. External dependencies on `_odd_card_eq_zero` and
`correlationΛ_*_at_singleton_beta_zero` come via the parent's
import chain.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 2 trivial-slice singleton vanishing wrappers

The two trivial-parameter-slice singleton vanishing wrappers
(`correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero`,
`correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonTrivial`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-- **Along-exhaustion magnetization vanishes at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0` for any
ambient site `i : V`. Specialization at `A = {i}`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ J β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton sandwich at h = 0**: `= 0 ∧ ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   (correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n).symm
      ▸ zero_le_one⟩

end Ambient

end IsingModel
