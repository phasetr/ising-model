import IsingModel.ClusterExpansion.PolymerCounting
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Per-vertex polymer activity bound (GJ §18.5)

Summing the volume-uniform rooted polymer count of `PolymerCounting`
(`rootedPolymersOfCard_card_le_maxDegree_pow`, `≤ Δ^{2ℓ}`) against the activity
`t^ℓ` gives the geometric series bound
`∑_{P ∋ v} t^{|P|} ≤ (1 − Δ²t)⁻¹` under `0 ≤ t` and `Δ²t < 1`, where
`Δ = G.maxDegree`.  This bound depends only on the maximum degree, **not** on the
volume — the per-vertex Kotecky--Preiss activity input that survives the
infinite-volume limit, unlike the per-volume conditions of
`InteractingFreeEnergyMayerHighTemp`.

Double-counting the per-vertex bound over all vertices then controls the *total*
polymer activity `∑_{P ∈ allPolymers} t^{|P|}` by `|ι|·(1 − Δ²t)⁻¹`
(`allPolymersActivity_le_card_mul_geometric`), hence the **per-site** activity
`(1/|ι|)·∑_P t^{|P|}` by the volume-uniform constant `(1 − Δ²t)⁻¹`
(`allPolymersActivity_div_card_le_geometric`).

The result is a finite-graph bound in terms of `G.maxDegree`; assembling the full
volume-uniform Kotecky--Preiss convergence and the infinite-volume pressure from
it is later work.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.3, eq.~(3.49).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polymer activity through a vertex `v`: `∑_{P ∋ v} t^{|P|}`. -/
noncomputable def rootedPolymerActivity (G : SimpleGraph ι) [Fintype G.edgeSet]
    (v : ι) (t : ℝ) : ℝ :=
  ∑ P ∈ rootedPolymers G v, t ^ P.card

/-- **Per-vertex polymer activity bound (volume-uniform).**  For `0 ≤ t` and
`Δ²t < 1` (`Δ = G.maxDegree`), the polymer activity through `v` is bounded by the
geometric series `(1 − Δ²t)⁻¹`, independently of the volume. -/
theorem rootedPolymerActivity_le_geometric (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (v : ι) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (G.maxDegree : ℝ) ^ 2 * t < 1) :
    rootedPolymerActivity G v t ≤ (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
  have hr0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * t := mul_nonneg (by positivity) ht0
  have hmaps : ∀ P ∈ rootedPolymers G v, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    rw [rootedPolymers, Finset.mem_filter] at hP
    have hsub : P ⊆ G.edgeFinset := (mem_allPolymers.mp hP.1).isEven.subset
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hsub))
  rw [rootedPolymerActivity,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun P => t ^ P.card)]
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), t ^ P.card)
        ≤ ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by
    intro ℓ _
    have hconst : (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), t ^ P.card)
        = ((rootedPolymersOfCard G v ℓ).card : ℝ) * t ^ ℓ := by
      rw [rootedPolymersOfCard]
      rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2]]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcount : ((rootedPolymersOfCard G v ℓ).card : ℝ) ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) := by
      exact_mod_cast rootedPolymersOfCard_card_le_maxDegree_pow G v ℓ
    calc ((rootedPolymersOfCard G v ℓ).card : ℝ) * t ^ ℓ
        ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) * t ^ ℓ :=
          mul_le_mul_of_nonneg_right hcount (pow_nonneg ht0 ℓ)
      _ = ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by rw [mul_pow, pow_mul]
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  refine le_trans ((summable_geometric_of_lt_one hr0 ht).sum_le_tsum _
    (fun ℓ _ => pow_nonneg hr0 ℓ)) ?_
  rw [tsum_geometric_of_lt_one hr0 ht]

/-- The total polymer activity of `G`: `∑_{P ∈ allPolymers G} t^{|P|}`. -/
noncomputable def allPolymersActivity (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) : ℝ :=
  ∑ P ∈ allPolymers G, t ^ P.card

/-- **A polymer touches at least one vertex.**  Since a polymer is a nonempty edge
set and every edge contains a vertex, its support is nonempty. -/
theorem one_le_card_polymerSupport_of_mem_allPolymers (G : SimpleGraph ι)
    [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    1 ≤ (polymerSupport P).card := by
  obtain ⟨e, he⟩ := (mem_allPolymers.mp hP).nonempty
  refine Finset.card_pos.mpr ?_
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, mem_polymerSupport.mpr ⟨_, he, Sym2.mem_mk_left a b⟩⟩

/-- **The summed per-vertex activity equals the support-weighted total activity.**
`∑_v ∑_{P ∋ v} t^{|P|} = ∑_{P ∈ allPolymers} |supp P| · t^{|P|}`, by exchanging the
order of summation. -/
theorem sum_rootedPolymerActivity_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) :
    (∑ v : ι, rootedPolymerActivity G v t)
      = ∑ P ∈ allPolymers G, (polymerSupport P).card • t ^ P.card := by
  simp only [rootedPolymerActivity, rootedPolymers]
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_filter _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]

/-- **Total polymer activity bound (vertices × per-vertex geometric bound).**  For
`0 ≤ t` and `Δ²t < 1` (`Δ = G.maxDegree`), the total polymer activity is at most
`|ι|·(1 − Δ²t)⁻¹`.  Each polymer is counted at least once in the vertex sum
(its support is nonempty), so the total activity is dominated by the summed
per-vertex activity, itself at most `|ι|` copies of the geometric bound. -/
theorem allPolymersActivity_le_card_mul_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (G.maxDegree : ℝ) ^ 2 * t < 1) :
    allPolymersActivity G t
      ≤ (Fintype.card ι : ℝ) * (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
  have hle : allPolymersActivity G t ≤ ∑ v : ι, rootedPolymerActivity G v t := by
    rw [allPolymersActivity, sum_rootedPolymerActivity_eq]
    refine Finset.sum_le_sum fun P hP => ?_
    have h1 : (1 : ℝ) ≤ ((polymerSupport P).card : ℝ) := by
      exact_mod_cast one_le_card_polymerSupport_of_mem_allPolymers G hP
    calc t ^ P.card = 1 * t ^ P.card := (one_mul _).symm
      _ ≤ ((polymerSupport P).card : ℝ) * t ^ P.card :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg ht0 _)
      _ = (polymerSupport P).card • t ^ P.card := (nsmul_eq_mul _ _).symm
  refine hle.trans ?_
  calc (∑ v : ι, rootedPolymerActivity G v t)
      ≤ ∑ _v : ι, (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ :=
        Finset.sum_le_sum fun v _ => rootedPolymerActivity_le_geometric G v ht0 ht
    _ = (Fintype.card ι : ℝ) * (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Per-site polymer activity bound (volume-uniform).**  For `0 ≤ t`,
`Δ²t < 1`, and a nonempty vertex type, the per-site total polymer activity
`(1/|ι|)·∑_{P} t^{|P|}` is bounded by the volume-uniform constant `(1 − Δ²t)⁻¹`,
`Δ = G.maxDegree`. -/
theorem allPolymersActivity_div_card_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (G.maxDegree : ℝ) ^ 2 * t < 1) :
    allPolymersActivity G t / (Fintype.card ι : ℝ)
      ≤ (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard, mul_comm]
  exact allPolymersActivity_le_card_mul_geometric G ht0 ht

end IsingModel
