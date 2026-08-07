import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion correlation degenerate-case wrappers at h = 0

Puts the GJ §18.3 zero-field correlation degeneracies — Z₂ vanishing on odd subsets and the
normalization at the empty subset — into along-exhaustion form, so downstream stagewise
estimates can quote them directly. Each is lifted from its `correlationΛ_high_temp_h_zero_*`
counterpart through `liftFinset` at the stage volume.
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

end Ambient

end IsingModel
