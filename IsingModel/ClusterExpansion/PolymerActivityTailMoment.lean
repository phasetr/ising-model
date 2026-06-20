import IsingModel.ClusterExpansion.PolymerActivityMoment

/-!
# Sharpened (tail) per-vertex polymer-activity moment bound (GJ §18.5)

The per-vertex polymer-activity moment bound (`rootedPolymerActivity_cardPow_le`, #4099)
bounds `∑_{Q ∋ v} |Q|^d u^{|Q|} ≤ d!/(1−Δ²u)^{d+1}`.  Since every polymer is nonempty
(`|Q| ≥ 1`), the `ℓ = 0` term of the underlying geometric series is absent, so the bound
sharpens to carry an extra factor `Δ²u`:

`∑_{Q ∋ v} |Q|^d u^{|Q|} ≤ (Δ²u)·d!/(1−Δ²u)^{d+1}`.

This `Δ²u` factor — one per non-root vertex of the rooted-tree leaf-peel — is what a
convergent (summable-over-`n`) cluster-expansion bound needs, since the bare
`d!/(1−Δ²u)^{d+1}` factors do not decay with the tree size.

* `rootedPolymerActivity_cardPow_tail_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharpened (tail) per-vertex polymer-activity moment bound.**  Since every polymer
through `v` is nonempty, the size-`0` fiber of the moment sum is empty, so the bound of
`rootedPolymerActivity_cardPow_le` sharpens by a factor `Δ²u`:
`∑_{Q ∋ v} |Q|^d u^{|Q|} ≤ (Δ²u)·d!/(1−Δ²u)^{d+1}`.  The proof fibers over the polymer
size `ℓ` as in #4099, drops the empty `ℓ = 0` fiber, reindexes `ℓ ↦ ℓ + 1`, and applies
the tail geometric-moment bound `tsum_succ_pow_mul_geometric_succ_le`. -/
theorem rootedPolymerActivity_cardPow_tail_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (v : ι) (d : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (G.maxDegree : ℝ) ^ 2 * u < 1) :
    (∑ Q ∈ rootedPolymers G v, (Q.card : ℝ) ^ d * u ^ Q.card)
      ≤ ((G.maxDegree : ℝ) ^ 2 * u)
          * ((d.factorial : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * u) ^ (d + 1)) := by
  set r : ℝ := (G.maxDegree : ℝ) ^ 2 * u with hr
  have hr0 : (0 : ℝ) ≤ r := mul_nonneg (by positivity) hu0
  have hmaps : ∀ P ∈ rootedPolymers G v, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    rw [rootedPolymers, Finset.mem_filter] at hP
    have hsub : P ⊆ G.edgeFinset := (mem_allPolymers.mp hP.1).isEven.subset
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hsub))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun Q => (Q.card : ℝ) ^ d * u ^ Q.card)]
  -- Each fiber is bounded by `if ℓ = 0 then 0 else ℓ^d r^ℓ`.
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ Q ∈ (rootedPolymers G v).filter (fun Q => Q.card = ℓ), (Q.card : ℝ) ^ d * u ^ Q.card)
        ≤ (if ℓ = 0 then 0 else (ℓ : ℝ) ^ d * r ^ ℓ) := by
    intro ℓ _
    by_cases hℓ : ℓ = 0
    · subst hℓ
      rw [if_pos rfl]
      refine le_of_eq (Finset.sum_eq_zero fun Q hQ => ?_)
      rw [Finset.mem_filter] at hQ
      have hcard0 : Q.card = 0 := hQ.2
      have hQin : Q ∈ rootedPolymers G v := hQ.1
      rw [rootedPolymers, Finset.mem_filter] at hQin
      have hne := (mem_allPolymers.mp hQin.1).nonempty
      rw [← Finset.card_pos] at hne
      exact absurd hcard0 (by omega)
    · rw [if_neg hℓ]
      have hconst :
          (∑ Q ∈ (rootedPolymers G v).filter (fun Q => Q.card = ℓ), (Q.card : ℝ) ^ d * u ^ Q.card)
            = ((rootedPolymersOfCard G v ℓ).card : ℝ) * ((ℓ : ℝ) ^ d * u ^ ℓ) := by
        rw [rootedPolymersOfCard]
        rw [Finset.sum_congr rfl fun Q hQ => by rw [(Finset.mem_filter.mp hQ).2]]
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      have hcount : ((rootedPolymersOfCard G v ℓ).card : ℝ) ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) := by
        exact_mod_cast rootedPolymersOfCard_card_le_maxDegree_pow G v ℓ
      calc ((rootedPolymersOfCard G v ℓ).card : ℝ) * ((ℓ : ℝ) ^ d * u ^ ℓ)
          ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) * ((ℓ : ℝ) ^ d * u ^ ℓ) :=
            mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = (ℓ : ℝ) ^ d * r ^ ℓ := by rw [hr, mul_pow, pow_mul]; ring
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  -- Drop the empty `ℓ = 0` term and reindex `ℓ ↦ ℓ + 1`.
  rw [Finset.sum_range_succ' (fun ℓ => if ℓ = 0 then 0 else (ℓ : ℝ) ^ d * r ^ ℓ), if_pos rfl,
    add_zero]
  have hreidx : ∀ m ∈ Finset.range G.edgeFinset.card,
      (if m + 1 = 0 then (0 : ℝ) else ((m + 1 : ℕ) : ℝ) ^ d * r ^ (m + 1))
        = ((m + 1 : ℕ) : ℝ) ^ d * r ^ (m + 1) := fun m _ => if_neg (Nat.succ_ne_zero m)
  rw [Finset.sum_congr rfl hreidx]
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hsumm : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ d * r ^ (m + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ d * r ^ n) 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one d hnorm)
  refine le_trans (hsumm.sum_le_tsum _ (fun m _ => by positivity)) ?_
  exact tsum_succ_pow_mul_geometric_succ_le d hr0 hu

end IsingModel
