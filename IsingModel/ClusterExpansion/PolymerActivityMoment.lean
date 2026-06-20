import IsingModel.ClusterExpansion.PolymerActivity
import IsingModel.ClusterExpansion.GeometricMoment

/-!
# Per-vertex polymer activity moment bound (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction accumulates polynomial moments
of the per-vertex polymer activity (each peeled leaf leaves a `|parent|`-power
factor).  Combining the volume-uniform rooted polymer count
(`rootedPolymersOfCard_card_le_maxDegree_pow`, `≤ Δ^{2ℓ}`) with the geometric-moment
bound (`tsum_pow_mul_geometric_le`) gives the per-vertex `d`-th activity moment
bound, volume-uniform (depending only on `Δ = G.maxDegree`):
`∑_{Q ∋ v} |Q|^d u^{|Q|} ≤ d!·(1 − Δ²u)^{-(d+1)}` for `0 ≤ u`, `Δ²u < 1`.

The `d = 0` case is the per-vertex activity bound `rootedPolymerActivity_le_geometric`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Per-vertex polymer activity moment bound (volume-uniform).**  For `0 ≤ u` and
`Δ²u < 1` (`Δ = G.maxDegree`), the `d`-th moment of the per-vertex polymer activity
is bounded by `d!·(1 − Δ²u)^{-(d+1)}`, independently of the volume:
`∑_{Q ∋ v} |Q|^d u^{|Q|} ≤ d!/(1 − Δ²u)^{d+1}`.  Partition the rooted polymers by
cardinality, bound each size-`ℓ` fibre by `Δ^{2ℓ}·ℓ^d·u^ℓ = ℓ^d·(Δ²u)^ℓ` via the
volume-uniform count, then dominate by the geometric moment series. -/
theorem rootedPolymerActivity_cardPow_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (v : ι) (d : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (G.maxDegree : ℝ) ^ 2 * u < 1) :
    (∑ Q ∈ rootedPolymers G v, (Q.card : ℝ) ^ d * u ^ Q.card)
      ≤ (d.factorial : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * u) ^ (d + 1) := by
  have hr0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * u := mul_nonneg (by positivity) hu0
  have hmaps : ∀ P ∈ rootedPolymers G v, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    rw [rootedPolymers, Finset.mem_filter] at hP
    have hsub : P ⊆ G.edgeFinset := (mem_allPolymers.mp hP.1).isEven.subset
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hsub))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun Q => (Q.card : ℝ) ^ d * u ^ Q.card)]
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ Q ∈ (rootedPolymers G v).filter (fun Q => Q.card = ℓ), (Q.card : ℝ) ^ d * u ^ Q.card)
        ≤ (ℓ : ℝ) ^ d * ((G.maxDegree : ℝ) ^ 2 * u) ^ ℓ := by
    intro ℓ _
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
      _ = (ℓ : ℝ) ^ d * ((G.maxDegree : ℝ) ^ 2 * u) ^ ℓ := by rw [mul_pow, pow_mul]; ring
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  have hnorm : ‖(G.maxDegree : ℝ) ^ 2 * u‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  refine le_trans ((summable_pow_mul_geometric_of_norm_lt_one d hnorm).sum_le_tsum _
    (fun ℓ _ => by positivity)) ?_
  exact tsum_pow_mul_geometric_le d hr0 hu

end IsingModel
