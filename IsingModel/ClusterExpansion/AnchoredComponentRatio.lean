import IsingModel.ClusterExpansion.AnchoredPeel
import IsingModel.ClusterExpansion.AvoidingDeleteEdges
import IsingModel.ClusterExpansion.TwoPointRatioBound

/-!
# General-boundary component-ratio bricks (GJ Theorem 17.6.1, §18 cluster expansion)

This file is **brick K2** of the general-source (`Q_A`) ratio-bound chain (issue #4404) toward
Glimm–Jaffe Theorem 17.6.1 (p.313).  Building on the anchored peel identity
`htSubgraphSum_anchored_peel` (K1, `AnchoredPeel.lean`)
`Q_A(t) = ∑_{B ∈ evenSubsetsThrough A a} ∑_{C ∈ connectedComponentsWithBoundary G B}
  t^{|C|} · Q^{av}_{C, A ∖ B}(t)`,
it supplies the three general-boundary analogues of the two-point (pair) ingredients that make the
K3 induction possible.  Each is the faithful `B`-boundary generalization of an existing pair lemma
(no new mathematics):

* **K2a** `htSubgraphSumAvoiding'_eq_htSubgraphSum_Gavoid` — the boundary-`A'` structural reduction
  `Q^{av}_{C,A'}(t) = htSubgraphSum (Gavoid G C) A' t` (generalizes
  `htSubgraphSumAvoiding_eq_htSubgraphSum_empty_Gavoid`, recovered at `A' = ∅`), rewriting the peel
  remainder as a smaller numerator on the deleted graph `Gavoid G C` where `maxDegree_Gavoid_le`
  and the KP window are preserved.
* **K2b** `connectedComponentsWithBoundaryOfCard_card_le_maxDegree_pow` — the volume-uniform count
  `|{C ∈ connectedComponentsWithBoundary G B : |C| = ℓ}| ≤ Δ^{2ℓ}`, anchored at `a ∈ B`
  (generalizes `connectingComponentsOfCard_card_le_maxDegree_pow`; evenness of `B` is not used).
* **K2c** `boundaryComponentRatio_norm_le_geometric` — the per-`B`-block geometric packaging
  `‖(∑_C t^{|C|} Q^{av}_{C,A∖B}) / Q_∅‖ ≤ M / (1 - a₀ Δ²)` from a per-component estimate
  (generalizes `twoPointRatio_norm_le_geometric`; `hbound` is a *hypothesis*, discharged in K3, not
  an axiom, and is unrelated to K4's `hbdd`).

The *closed* ratio bound `‖Q_A/Q_∅‖ ≤ M(|A|,Δ)` is **K3** (the induction that discharges `hbound`
and sums K2c over `evenSubsetsThrough A a`), not K2.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), Theorem 17.6.1 (p.313),
Chapter 18 cluster expansion (§18.4–18.7, high-temperature Kotecký–Preiss window);
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **K2a — boundary-`A'` structural reduction.**  The avoiding remainder sum `Q^{av}_{C,A'}` equals
the ordinary boundary-`A'` high-temperature subgraph sum of the delete-edges graph `Gavoid G C`.
This is the boundary-keeping generalization of `htSubgraphSumAvoiding_eq_htSubgraphSum_empty_Gavoid`
(recovered at `A' = ∅`, where `∂Y = ∅` selects the even subgraphs).  Both sides sum `t^{|Y|}` over
the same index: `Y ⊆ (Gavoid G C).edgeFinset ↔ Y ⊆ G.edgeFinset ∧ IsPolymerVertexDisjoint C Y`
(`subset_edgeFinset_Gavoid_iff`), with the boundary filter `∂Y = A'` untouched.  Rewriting the peel
remainder this way exposes the smaller numerator on `Gavoid G C` that drives the K3 induction. -/
theorem htSubgraphSumAvoiding'_eq_htSubgraphSum_Gavoid
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (A' : Finset ι) (t : ℂ) :
    htSubgraphSumAvoiding' G C A' t = htSubgraphSum (Gavoid G C) A' t := by
  classical
  unfold htSubgraphSumAvoiding' htSubgraphSum subgraphsAvoidingBoundary
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext Y
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_filter, Finset.mem_powerset]
  have h := subset_edgeFinset_Gavoid_iff G C Y
  tauto

/-- **K2b — volume-uniform anchored count of boundary components.**  The number of components
`C ∈ connectedComponentsWithBoundary G B` (edge-connected, `∂C = B`) of size `ℓ` is at most
`Δ^{2ℓ}`, where `Δ = G.maxDegree` — independent of the volume.  Anchoring at any `a ∈ B` (so
`a ∈ ∂C ⊆ polymerSupport C`), each such `C` is a connected edge subset of size `ℓ` through `a`, so
it injects into the closed walks of length `2ℓ` from `a` (`card_connected_edge_sets_le`).  Evenness
of `B` is not used; this generalizes `connectingComponentsOfCard_card_le_maxDegree_pow` from
`B = {i,j}` to arbitrary boundary `B`. -/
theorem connectedComponentsWithBoundaryOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (B : Finset ι) {a : ι} (ha : a ∈ B) (ℓ : ℕ) :
    ((connectedComponentsWithBoundary G B).filter (fun C => C.card = ℓ)).card
      ≤ G.maxDegree ^ (2 * ℓ) := by
  classical
  refine le_trans (card_connected_edge_sets_le (G := G) a ℓ _ (fun C hC => ?_)) ?_
  · simp only [Finset.mem_filter, connectedComponentsWithBoundary, Finset.mem_powerset] at hC
    obtain ⟨⟨hCsub, _hCne, hCconn, hCbd⟩, hCcard⟩ := hC
    refine ⟨hCsub, hCconn, hCcard, ?_⟩
    have ha' : a ∈ polymerSupport C := by
      apply oddBoundary_subset_polymerSupport C
      rw [hCbd]; exact ha
    exact mem_polymerSupport.mp ha'
  · refine le_trans ?_ (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * ℓ) a)
    rw [walksFromCount]
    exact Finset.single_le_sum (f := fun u => (G.finsetWalkLength (2 * ℓ) a u).card)
      (fun u _ => Nat.zero_le _) (Finset.mem_univ a)

/-- **K2c — per-`B`-block geometric packaging.**  If every component
`C ∈ connectedComponentsWithBoundary G B` satisfies the per-component avoiding-ratio estimate
`‖t‖^{|C|} · ‖Q^{av}_{C,A∖B}(t)/Q_∅(t)‖ ≤ M · a₀^{|C|}` and the geometric ratio `a₀·Δ²` is below `1`
(with `Δ = G.maxDegree`), then the norm of the whole `B`-block ratio is bounded by the
volume-uniform value `M / (1 - a₀·Δ²)`.  The count of size-`ℓ` boundary components is `≤ Δ^{2ℓ}`
(K2b) and the
geometric summation is `sum_le_geometric_closed_of_fiber_card_le`.  This is the general-boundary
analogue of `twoPointRatio_norm_le_geometric`; it bounds one `B`-block, not `Q_A/Q_∅` (summing over
`B ∈ evenSubsetsThrough A a` and discharging `hbound` is K3).  `hbound` is a hypothesis, not an
axiom. -/
theorem boundaryComponentRatio_norm_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {A B : Finset ι} {a : ι} (ha : a ∈ B) (t : ℂ)
    (M a₀ : ℝ) (hM : 0 ≤ M) (ha₀ : 0 ≤ a₀)
    (hbound : ∀ C ∈ connectedComponentsWithBoundary G B,
      ‖t‖ ^ C.card *
        ‖htSubgraphSumAvoiding' G C (A \ B) t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ M * a₀ ^ C.card)
    (hq : a₀ * ((G.maxDegree : ℝ) ^ 2) < 1) :
    ‖(∑ C ∈ connectedComponentsWithBoundary G B,
        t ^ C.card * htSubgraphSumAvoiding' G C (A \ B) t)
       / htSubgraphSum G (∅ : Finset ι) t‖
      ≤ M / (1 - a₀ * ((G.maxDegree : ℝ) ^ 2)) := by
  classical
  set Q0 : ℂ := htSubgraphSum G (∅ : Finset ι) t with hQ0
  -- the ratio is the sum over boundary components of the per-component ratios
  have hsum : (∑ C ∈ connectedComponentsWithBoundary G B,
        t ^ C.card * htSubgraphSumAvoiding' G C (A \ B) t) / Q0
      = ∑ C ∈ connectedComponentsWithBoundary G B,
          t ^ C.card * (htSubgraphSumAvoiding' G C (A \ B) t / Q0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [mul_div_assoc]
  -- bound the norm by the sum of per-component norms
  have hnorm : ‖(∑ C ∈ connectedComponentsWithBoundary G B,
        t ^ C.card * htSubgraphSumAvoiding' G C (A \ B) t) / Q0‖
      ≤ ∑ C ∈ connectedComponentsWithBoundary G B,
          ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding' G C (A \ B) t / Q0‖ := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun C _ => ?_)
    rw [norm_mul, norm_pow]
  refine hnorm.trans ?_
  -- apply the geometric fiber-count bound
  refine sum_le_geometric_closed_of_fiber_card_le
    (connectedComponentsWithBoundary G B) (fun C => C.card)
    (fun C => ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding' G C (A \ B) t / Q0‖)
    M a₀ ((G.maxDegree : ℝ) ^ 2) G.edgeFinset.card ?_ ?_ ?_ ?_ hM ha₀ ?_ hq
  · -- sizes are at most the number of edges
    intro C hC
    rw [connectedComponentsWithBoundary, Finset.mem_filter, Finset.mem_powerset] at hC
    exact Finset.card_le_card hC.1
  · -- nonnegativity of the weights
    intro C _
    exact mul_nonneg (pow_nonneg (norm_nonneg t) _) (norm_nonneg _)
  · -- the per-component bound
    exact hbound
  · -- fiber-count bound: components of size n number at most (Δ²)^n
    intro n
    have hcount := connectedComponentsWithBoundaryOfCard_card_le_maxDegree_pow G B ha n
    have hcast : (((connectedComponentsWithBoundary G B).filter (fun C => C.card = n)).card : ℝ)
        ≤ ((G.maxDegree ^ (2 * n) : ℕ) : ℝ) := by exact_mod_cast hcount
    refine hcast.trans ?_
    rw [Nat.cast_pow, pow_mul]
  · -- nonnegativity of Δ²
    positivity

end IsingModel
