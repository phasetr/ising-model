import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Ambient alongExhaustion correlation singleton + pair-singleton bundle wrappers at h = 0

Narrow child module for the eight §18.3-§18.4 ambient alongExhaustion
correlation wrappers covering the singleton family
(`_at_singleton_J_zero`, `_at_singleton_beta_zero`, `_at_singleton`,
`_at_singleton_eq_zero_le_one`) and the four pair-singleton bundle
variants (`_at_pair_singleton_bundle`,
`_at_pair_singleton_complete_summary`,
`_at_pair_singleton_trivial_slices_bundle`,
`_at_pair_singleton_bundle_ferromagnetic`). Each wrapper is a thin
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
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex pair+singleton bundle at h=0**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

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

/-- **Along-ex pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both pair and singleton correlations vanish at
every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero G Λ β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero G Λ J i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

/-- **Along-ex pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and
`⟨σ_iσ_j⟩ ≤ 1` at every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    G Λ J β (mul_nonneg hβ.le hJ) i j n

end Ambient

end IsingModel
