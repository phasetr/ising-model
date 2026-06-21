import IsingModel.Peierls.PlanarBondReduction
import IsingModel.Peierls.DartDualComponentImage
import IsingModel.Peierls.DartFinite

/-!
# Assembly of the planar bond hypothesis from the separation core (FV §3.7.2)

This file composes the homological-route lemmas (`PlanarBondParityCore`,
`PlanarBondSeparationBridge`, `EdgeSideComponent`, `DartDualComponentImage`) into a reduction of
`PlanarBondHypothesis F` to a single geometric input: the discrete-Jordan **separation** that a
boundary dart's dual component places its two sites on opposite sides of the induced region.

`planarBondHypothesis_of_separates` discharges `PlanarBondHypothesis F` from the hypothesis
`hsep` (the `dual_component_separates_primal` statement). The only nontrivial bookkeeping is
confining the ambient outside walk `ReachableOutside F` to a finite box: the walk has finite
support (`ReachableOutside.exists_finset_support`), and `BoundaryDart F` is finite, so a finite
box `Λ ⊇ F ∪ support ∪ {dart outside-sites}` carries the box-confined walk the bridge needs.

* `boundaryDartRightSites` — the finite set of all darts' outside endpoints.
* `ReachableOutside.exists_finset_support` — an outside walk has finite support, confined to any
  box containing it.
* `planarBondHypothesis_of_separates` — `PlanarBondHypothesis F` from the separation core.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {F : Finset (Fin 2 → ℤ)}

/-- **The finite set of all darts' outside endpoints**: the image of `q ↦ q.right` over the finite
type `BoundaryDart F`. -/
noncomputable def boundaryDartRightSites (F : Finset (Fin 2 → ℤ)) : Finset (Fin 2 → ℤ) :=
  (Finset.univ : Finset (BoundaryDart F)).image (fun q => q.right)

/-- **Each dart's outside endpoint lies in `boundaryDartRightSites`**. -/
theorem BoundaryDart.right_mem_boundaryDartRightSites (q : BoundaryDart F) :
    q.right ∈ boundaryDartRightSites F := by
  classical
  unfold boundaryDartRightSites
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

/-- **An outside walk has finite support**: from `ReachableOutside F x y` there is a finite set `P`
containing `x` and `y` such that any box `Λ ⊇ P` carries the box-confined walk
`ReachableOutsideInBox F hFΛ ⟨x⟩ ⟨y⟩`. -/
theorem ReachableOutside.exists_finset_support {x y : Fin 2 → ℤ} (h : ReachableOutside F x y) :
    ∃ P : Finset (Fin 2 → ℤ), ∃ hxP : x ∈ P, ∃ hyP : y ∈ P,
      ∀ {Λ : Finset (Fin 2 → ℤ)} (hFΛ : F ⊆ Λ) (hPΛ : P ⊆ Λ),
        ReachableOutsideInBox F hFΛ ⟨x, hPΛ hxP⟩ ⟨y, hPΛ hyP⟩ := by
  induction h with
  | refl =>
    refine ⟨{x}, by simp, by simp, ?_⟩
    intro Λ hFΛ hPΛ
    exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    obtain ⟨P, hxP, hbP, hbox⟩ := ih
    refine ⟨insert c P, Finset.mem_insert_of_mem hxP, Finset.mem_insert_self c P, ?_⟩
    intro Λ hFΛ hPΛ
    have hPΛ' : P ⊆ Λ := fun z hz => hPΛ (Finset.mem_insert_of_mem hz)
    have hbΛ : b ∈ Λ := hPΛ' hbP
    have hcΛ : c ∈ Λ := hPΛ (Finset.mem_insert_self c P)
    refine (hbox hFΛ hPΛ').tail ⟨inducedLattice_adj_iff.mpr hbc.1, ?_, ?_⟩
    · exact fun hbLift => hbc.2.1 ((Ambient.mem_liftFinset hFΛ ⟨b, hbΛ⟩).mp hbLift)
    · exact fun hcLift => hbc.2.2 ((Ambient.mem_liftFinset hFΛ ⟨c, hcΛ⟩).mp hcLift)

/-- **The planar bond hypothesis from the separation core**: if every boundary dart's dual
component separates its two sites in the induced region (`hsep`, the discrete-Jordan input), then
`PlanarBondHypothesis F` holds. Contrapositively, assuming `¬ DartReachable F d e`, the region
`edgeSideComponentDart hFΛ hRΛ d` separates `d` (it crosses) from `e` (it does not) on a box `Λ`
large enough to confine the outside walk, contradicting the bond hypothesis's inside/outside
connectivity via `false_of_box_separating_region_boundaryDart`. -/
theorem planarBondHypothesis_of_separates
    (hsep : ∀ {Λ : Finset (Fin 2 → ℤ)} (hFΛ : F ⊆ Λ)
      (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F),
      (⟨d.right, hRΛ d⟩ : (↑Λ : Type _)) ∉ edgeSideComponentDart hFΛ hRΛ d) :
    PlanarBondHypothesis F := by
  classical
  intro d e hin hout
  by_contra hne
  obtain ⟨P, hxP, hyP, hconfine⟩ := ReachableOutside.exists_finset_support hout
  set Λ : Finset (Fin 2 → ℤ) := F ∪ (P ∪ boundaryDartRightSites F) with hΛ
  have hFΛ : F ⊆ Λ := fun z hz => Finset.mem_union_left _ hz
  have hPΛ : P ⊆ Λ := fun z hz => Finset.mem_union_right _ (Finset.mem_union_left _ hz)
  have hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ := fun q =>
    Finset.mem_union_right _ (Finset.mem_union_right _
      (BoundaryDart.right_mem_boundaryDartRightSites q))
  have houtBox : ReachableOutsideInBox F hFΛ ⟨d.right, hRΛ d⟩ ⟨e.right, hRΛ e⟩ :=
    hconfine hFΛ hPΛ
  have hd_left : (⟨d.left, hFΛ d.left_mem⟩ : (↑Λ : Type _)) ∈
      edgeSideComponentDart hFΛ hRΛ d :=
    base_mem_edgeSideComponent _ _ _
  have hd_right : (⟨d.right, hRΛ d⟩ : (↑Λ : Type _)) ∉
      edgeSideComponentDart hFΛ hRΛ d :=
    hsep hFΛ hRΛ d
  have hd_cross : s(⟨d.left, hFΛ d.left_mem⟩, ⟨d.right, hRΛ d⟩) ∈
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (edgeSideComponentDart hFΛ hRΛ d) :=
    mem_cutEdges_of_mem_not_mem
      (boundaryDart_box_adj_left_right d (hFΛ d.left_mem) (hRΛ d)) hd_left hd_right
  exact false_of_box_separating_region_boundaryDart hFΛ d e (hRΛ d) (hRΛ e)
    (cutEdges_edgeSideComponentDart_subset_lift hFΛ hRΛ d) hd_cross
    (boxPrimalCutEdge_not_mem_cutEdges_edgeSideComponentDart_of_not_reachable hFΛ hRΛ hne)
    hin houtBox

end IsingModel
