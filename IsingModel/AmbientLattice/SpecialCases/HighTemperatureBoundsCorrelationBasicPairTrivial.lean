import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry

/-!
# The zero-field pair correlation at the trivial parameter slices, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

For ambient sites `i` and `j`, the along-exhaustion correlation of `{i, j}` vanishes at the
parameter record `⟨0, 0, β⟩` for arbitrary `β`, and at `⟨J, 0, 0⟩` for arbitrary `J`. On the
stages whose volume misses the pair the value is `0` by definition of
`correlationAlongExhaustion`; on the remaining stages the lifted site set is nonempty, and a
nonempty site set has vanishing correlation at either slice.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex pair at J=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨0, 0, β⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn, correlationΛ_J_zero, mul_zero, Real.tanh_zero]
    have hcard_pos : 0 < (liftFinset ({i, j} : Finset V) hAn).card := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact zero_pow hcard_pos.ne'
  · rw [dif_neg hAn]

/-- **Along-ex pair at β=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, 0⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    apply IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    have : (liftFinset ({i, j} : Finset V) hAn).card ≥ 1 := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact Finset.card_pos.mp this
  · rw [dif_neg hAn]

end Ambient

end IsingModel
