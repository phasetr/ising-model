import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairBase
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairTrivial
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Ambient alongExhaustion correlation singleton + pair-singleton bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
correlation wrappers covering the singleton family
(`_at_singleton_J_zero`, `_at_singleton_beta_zero`, `_at_singleton`,
`_at_singleton_eq_zero_le_one`) and the pair-singleton
`_at_pair_singleton_complete_summary` bundle. Each wrapper is a thin
pass-through that reduces to `_odd_card_eq_zero`, the `_at_pair_*`
basic wrappers, or `correlationΛ_*` ambient lemmas. Theorem names
are unchanged from the former `HighTemperatureBoundsCorrelationBasic`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Moved: correlation singleton wrappers

The four `correlationAlongExhaustion_high_temp_h_zero_at_singleton*`
wrappers (`_J_zero`, `_beta_zero`, `_at_singleton`, `_eq_zero_le_one`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

end Ambient

end IsingModel
