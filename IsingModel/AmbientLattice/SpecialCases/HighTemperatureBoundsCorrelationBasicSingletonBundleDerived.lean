import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPair
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairTrivial
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Ambient alongExhaustion correlation pair+singleton derived bundle wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
derived pair+singleton bundle wrappers extracted from
`HighTemperatureBoundsCorrelationBasicSingletonBundle.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`

The trivial-slices bundle assembles the four
`_at_singleton_J_zero` / `_at_singleton_beta_zero` /
`_at_pair_J_zero` / `_at_pair_beta_zero` vanishings into one
conjunction. The ferromagnetic bundle derives `0 ≤ β * J` from
`0 ≤ J` and `0 < β` and assembles `⟨σ_i⟩ = 0`,
`0 ≤ ⟨σ_iσ_j⟩`, `⟨σ_iσ_j⟩ ≤ 1` inline from
`_at_singleton` / `_at_pair_nonneg` / `_at_pair_le_one` (the same
construction as the parent's general `_at_pair_singleton_bundle`).
Theorem names are unchanged from the former
`HighTemperatureBoundsCorrelationBasic` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
     G Λ J β (mul_nonneg hβ.le hJ) i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

end Ambient

end IsingModel
