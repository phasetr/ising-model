import IsingModel.Peierls.DualCutSubConnected

/-!
# The dual cut over a common box (FV §3.7.2)

The contour count `card_connected_edge_sets_inducedLatticeGraph_le` ranges over a **fixed** box
`Λd`, so the per-region support box `dualSupport F` must be promoted into a common box `Λd ⊇
dualSupport F`. We map `dualCutSub F` along the subtype inclusion `↑(dualSupport F) ↪ ↑Λd`
and carry over its three count-ready properties: edge-finset membership, cardinality, and
(given one orbit) edge-connectivity.

* `isEdgeConnected_image_map` — forward connectivity transfer.
* `dualCutInBox` — the dual cut placed in the common box.
* `dualCutInBox_subset_edgeFinset`, `dualCutInBox_card`,
  `dualCutInBox_isEdgeConnected_of_single_orbit`.
* `dualCutInBox_isEdgeConnected_of_anchored` — the common-box connectivity wrapper for the
  anchored `DartReachable` route.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λd : Finset (Fin 2 → ℤ)}

/-- **Forward edge-connectivity transfer**: the image of an edge-connected set under any
`Sym2.map f` is edge-connected. A shared vertex maps forward to a shared vertex, and a
reachability chain maps forward step by step (no injectivity needed). -/
theorem isEdgeConnected_image_map {V W : Type*} [DecidableEq W]
    {f : V → W} {X : Finset (Sym2 V)} (hX : IsEdgeConnected X) :
    IsEdgeConnected (X.image (Sym2.map f)) := by
  classical
  -- one edge-adjacency step maps forward
  have hstep : ∀ {p q : Sym2 V}, edgeAdjacentIn X p q →
      edgeAdjacentIn (X.image (Sym2.map f)) (Sym2.map f p) (Sym2.map f q) := by
    intro p q hpq
    obtain ⟨hp, hq, v, hvp, hvq⟩ := hpq
    refine ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, f v, ?_, ?_⟩
    · rw [Sym2.mem_map]; exact ⟨v, hvp, rfl⟩
    · rw [Sym2.mem_map]; exact ⟨v, hvq, rfl⟩
  -- a reachability chain maps forward
  have hmap : ∀ {a y : Sym2 V}, Relation.ReflTransGen (edgeAdjacentIn X) a y →
      Relation.ReflTransGen (edgeAdjacentIn (X.image (Sym2.map f)))
        (Sym2.map f a) (Sym2.map f y) := by
    intro a y hreach
    induction hreach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _hch hpq ih => exact ih.tail (hstep hpq)
  intro e₁ he₁ e₂ he₂
  rw [Finset.mem_image] at he₁ he₂
  obtain ⟨a, ha, rfl⟩ := he₁
  obtain ⟨b, hb, rfl⟩ := he₂
  exact hmap (hX a ha b hb)

/-- The inclusion of the support box into a containing box, as a subtype map. -/
noncomputable def supportIncl (hsub : dualSupport F ⊆ Λd) : ↑(dualSupport F) → ↑Λd :=
  fun v => ⟨v.1, hsub v.2⟩

/-- The subtype inclusion is injective. -/
theorem supportIncl_injective (hsub : dualSupport F ⊆ Λd) :
    Function.Injective (supportIncl hsub) := by
  intro a b hab
  apply Subtype.ext
  calc (a : Fin 2 → ℤ) = (supportIncl hsub a : Fin 2 → ℤ) := rfl
    _ = (supportIncl hsub b : Fin 2 → ℤ) := congrArg Subtype.val hab
    _ = (b : Fin 2 → ℤ) := rfl

/-- **The dual cut placed in a common box** `Λd ⊇ dualSupport F`. -/
noncomputable def dualCutInBox (hsub : dualSupport F ⊆ Λd) : Finset (Sym2 ↑Λd) :=
  (dualCutSub F).image (Sym2.map (supportIncl hsub))

/-- **The common-box dual cut lies in the induced lattice graph's edge finset**. -/
theorem dualCutInBox_subset_edgeFinset (hsub : dualSupport F ⊆ Λd) :
    dualCutInBox hsub ⊆ (Ambient.inducedGraph (latticeGraph 2) Λd).edgeFinset := by
  classical
  intro e he
  rw [dualCutInBox, Finset.mem_image] at he
  obtain ⟨e', he', rfl⟩ := he
  rw [dualCutSub, Finset.mem_image] at he'
  obtain ⟨d, _, rfl⟩ := he'
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Ambient.inducedGraph_apply]
  exact SimpleGraph.induce_adj.mpr d.tail_adj_head

/-- **The common-box dual cut keeps the dart cardinality**. -/
theorem dualCutInBox_card (hsub : dualSupport F ⊆ Λd) :
    (dualCutInBox hsub).card = (Finset.univ : Finset (BoundaryDart F)).card := by
  classical
  rw [dualCutInBox, Finset.card_image_of_injective _
    (Sym2.map.injective (supportIncl_injective hsub)), dualCutSub_card]

/-- **The common-box dual cut is edge-connected given a single orbit**. -/
theorem dualCutInBox_isEdgeConnected_of_single_orbit (hsub : dualSupport F ⊆ Λd)
    (hone : ∀ d e : BoundaryDart F, d.SameOrbit e) :
    IsEdgeConnected (dualCutInBox hsub) :=
  isEdgeConnected_image_map (dualCutSub_isEdgeConnected_of_single_orbit hone)

/-- **The common-box dual cut is edge-connected from anchored dart reachability data**. -/
theorem dualCutInBox_isEdgeConnected_of_anchored (hsub : dualSupport F ⊆ Λd)
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hanchor : ∀ d : BoundaryDart F, DartReachable F d (φ ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, (latticeGraph 2).Adj a.1 b.1 →
      DartReachable F (φ a) (φ b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  isEdgeConnected_image_map
    (dualCutSub_isEdgeConnected_of_anchored φ hanchor hstep hconn)

end IsingModel
