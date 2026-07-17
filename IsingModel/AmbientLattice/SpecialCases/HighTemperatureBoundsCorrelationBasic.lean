import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion correlation basic + bundle wrappers at h = 0

Narrow child module for 16 ambient alongExhaustion §18.3-§18.4
correlation basic / bundle wrappers
(`correlationAlongExhaustion_high_temp_h_zero_*`): odd_card_eq_zero;
at_empty_A; pair (`le_one`, `nonneg`, `sandwich`, `ferromagnetic`,
`J_zero`, `beta_zero`); singleton (`J_zero`, `beta_zero`,
`_at_singleton`, `eq_zero_le_one`); and bundle / complete_summary /
trivial_slices_bundle / pair_singleton_bundle_ferromagnetic. Theorem
names are unchanged from the former
`AmbientLattice/SpecialCases/HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion correlation Z₂ symmetry at h = 0 (GJ §18.3)**:
for any ambient `A : Finset V` with odd cardinality, at every stage `n`
where `A ⊆ Λ.volume n`, the per-stage correlation
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0`.

When `A ⊄ Λ.volume n`, `correlationAlongExhaustion` is `0` by definition,
trivially satisfying the equation. When `A ⊆ Λ.volume n`, lift via
`liftFinset` (preserves cardinality) and apply
`correlationΛ_high_temp_h_zero_odd_card_eq_zero` (Step 299). -/
theorem correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · simp only [dif_pos hAn]
    have hcard : (liftFinset A hAn).card = A.card := liftFinset_card hAn
    refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G (Λ.volume n) J β
      (liftFinset A hAn) ?_
    rw [hcard]; exact hA_odd
  · simp only [dif_neg hAn]

/-- **Along-exhaustion FV (3.46) at A = ∅ consistency check**:
under `0 ≤ β·J`, at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ ∅ n = 1`.
The empty Finset is always a subset of `Λ.volume n`, so we lift via
`liftFinset`, then apply `correlationΛ_high_temp_h_zero_at_empty_A` (Step 314). -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_empty_A
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset V) n = 1 := by
  unfold correlationAlongExhaustion
  rw [dif_pos (Finset.empty_subset _)]
  have h_lift : liftFinset (∅ : Finset V) (Finset.empty_subset (Λ.volume n))
      = (∅ : Finset ↑(Λ.volume n)) := by
    ext v; simp [liftFinset]
  rw [h_lift]
  exact correlationΛ_high_temp_h_zero_at_empty_A G (Λ.volume n) J β hβJ

/-! ## Moved: correlation pair wrappers

The six `correlationAlongExhaustion_high_temp_h_zero_at_pair_*`
wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPair`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: correlation singleton + pair-singleton bundle wrappers

The eight `correlationAlongExhaustion_high_temp_h_zero_*` wrappers
covering the singleton family (`_at_singleton_J_zero`,
`_at_singleton_beta_zero`, `_at_singleton`,
`_at_singleton_eq_zero_le_one`) and the four pair-singleton bundle
variants (`_at_pair_singleton_bundle`,
`_at_pair_singleton_complete_summary`,
`_at_pair_singleton_trivial_slices_bundle`,
`_at_pair_singleton_bundle_ferromagnetic`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

end Ambient

end IsingModel
