import IsingModel.Peierls.PlanarBondParityCore
import IsingModel.Peierls.SameOrbit
import IsingModel.Peierls.DartCutChar
import IsingModel.Peierls.LiftBoxCut
import IsingModel.AmbientLattice.Exhaustion

/-!
# Box bridge for the mod-2 separation engine (FV §3.7.2)

The abstract separation engine of `PlanarBondParityCore.lean` works on a finite graph with a
`Fintype` edge set, while `PlanarBondHypothesis` is stated on the infinite `latticeGraph 2`. This
file bridges the two: it transports the bond data of two `BoundaryDart F` (and an inside walk
`ReachableWithin (latticeGraph 2) F`) into the induced graph on a finite box `Λ ⊇ F`, where
`PlanarBondParityCore.not_separated_of_inside_outside_reachable` applies.

The headline `false_of_box_separating_region_boundaryDart` shows that a *box* separating region
`A : Finset ↑Λ` (with `cutEdges A ⊆ cutEdges (liftFinset F)`, crossing `d`, not crossing `e`)
contradicts the inside/outside connectivity of the bond hypothesis. This isolates the remaining
topological obligation to constructing such a separating region from `¬ DartReachable F d e`
(the next step in the campaign), not addressed here.

* `inducedLattice_adj_iff` — induced-box adjacency reduces to ambient `latticeGraph 2` adjacency.
* `ReachableOutsideInBox` — complement reachability confined to the box `Λ`.
* `reachableWithin_box_liftFinset_of_reachableWithin` — lift an inside walk to the box subtype.
* `boundaryDart_box_adj_left_right` — a dart's two sites are adjacent in the box graph.
* `boundaryDart_box_primalCut_mem_cutEdges_lift` — a dart's primal edge cuts `liftFinset F`.
* `false_of_box_separating_region_boundaryDart` — the box separation contradiction.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {F Λ : Finset (Fin 2 → ℤ)}

/-- **Induced-box adjacency reduces to ambient adjacency**: two box vertices are adjacent in
`inducedGraph (latticeGraph 2) Λ` iff their underlying lattice points are `latticeGraph 2`
adjacent. -/
theorem inducedLattice_adj_iff {a b : (↑Λ : Type _)} :
    (Ambient.inducedGraph (latticeGraph 2) Λ).Adj a b ↔ (latticeGraph 2).Adj a.val b.val :=
  Iff.rfl

/-- **Complement reachability confined to the box `Λ`**: a chain of `latticeGraph 2` adjacencies
staying inside `Λ` and outside `F`, phrased on the box subtype `↑Λ`. The hypothesis form of the
outside connectivity that the box bridge consumes (the ambient `ReachableOutside F` does not by
itself confine the path to `Λ`). -/
def ReachableOutsideInBox (F : Finset (Fin 2 → ℤ)) {Λ : Finset (Fin 2 → ℤ)}
    (hFΛ : F ⊆ Λ) (x y : (↑Λ : Type _)) : Prop :=
  Relation.ReflTransGen
    (fun a b : (↑Λ : Type _) =>
      (Ambient.inducedGraph (latticeGraph 2) Λ).Adj a b ∧
        a ∉ Ambient.liftFinset F hFΛ ∧ b ∉ Ambient.liftFinset F hFΛ) x y

/-- **Lift an inside walk to the box subtype**: an inside-`F` walk on `latticeGraph 2` between two
box points lifts to a `ReachableWithin` walk on the induced box graph with vertex set
`liftFinset F`. -/
theorem reachableWithin_box_liftFinset_of_reachableWithin (hFΛ : F ⊆ Λ)
    {x y : Fin 2 → ℤ} (hxΛ : x ∈ Λ) (hyΛ : y ∈ Λ)
    (h : ReachableWithin (latticeGraph 2) F x y) :
    ReachableWithin (Ambient.inducedGraph (latticeGraph 2) Λ) (Ambient.liftFinset F hFΛ)
      ⟨x, hxΛ⟩ ⟨y, hyΛ⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have hbΛ : b ∈ Λ := hFΛ hbc.2.1
    exact (ih hbΛ).tail
      ⟨inducedLattice_adj_iff.mpr hbc.1,
       (Ambient.mem_liftFinset hFΛ ⟨b, hbΛ⟩).mpr hbc.2.1,
       (Ambient.mem_liftFinset hFΛ ⟨c, hyΛ⟩).mpr hbc.2.2⟩

/-- **A dart's two sites are adjacent in the box graph**: the left and right sites of a boundary
dart, viewed as box vertices, are adjacent in `inducedGraph (latticeGraph 2) Λ`. -/
theorem boundaryDart_box_adj_left_right (d : BoundaryDart F)
    (hL : d.left ∈ Λ) (hR : d.right ∈ Λ) :
    (Ambient.inducedGraph (latticeGraph 2) Λ).Adj ⟨d.left, hL⟩ ⟨d.right, hR⟩ :=
  inducedLattice_adj_iff.mpr (leftSite_adj_rightSite d.tail d.dir)

/-- **A dart's primal edge cuts `liftFinset F`**: the primal edge `s(left, right)` of a boundary
dart is a cut edge of the lifted region `liftFinset F` in the box graph (its left site lies in `F`,
its right site does not). -/
theorem boundaryDart_box_primalCut_mem_cutEdges_lift (hFΛ : F ⊆ Λ) (d : BoundaryDart F)
    (hR : d.right ∈ Λ) :
    s(⟨d.left, hFΛ d.left_mem⟩, ⟨d.right, hR⟩) ∈
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (Ambient.liftFinset F hFΛ) := by
  rw [mem_cutEdges_iff]
  refine ⟨boundaryDart_box_adj_left_right d (hFΛ d.left_mem) hR, ?_⟩
  rw [Ambient.mem_liftFinset hFΛ ⟨d.left, hFΛ d.left_mem⟩,
    Ambient.mem_liftFinset hFΛ ⟨d.right, hR⟩]
  exact iff_of_true d.left_mem d.right_not_mem

/-- **The box separation contradiction**: a box separating region `A` for two boundary darts —
`cutEdges A ⊆ cutEdges (liftFinset F)`, with `d`'s primal edge in `cutEdges A` and `e`'s primal
edge not in `cutEdges A` — cannot coexist with `d.left` reaching `e.left` inside `F` and `d.right`
reaching `e.right` outside `F` inside the box. The bond hypothesis's connectivity premises are
thus refuted by any such separating region. -/
theorem false_of_box_separating_region_boundaryDart (hFΛ : F ⊆ Λ) {A : Finset (↑Λ : Type _)}
    (d e : BoundaryDart F) (hdr : d.right ∈ Λ) (her : e.right ∈ Λ)
    (hsub : cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) A ⊆
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (Ambient.liftFinset F hFΛ))
    (hd_cross : s(⟨d.left, hFΛ d.left_mem⟩, ⟨d.right, hdr⟩) ∈
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) A)
    (he_ncross : s(⟨e.left, hFΛ e.left_mem⟩, ⟨e.right, her⟩) ∉
      cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) A)
    (hin : ReachableWithin (latticeGraph 2) F d.left e.left)
    (hout : ReachableOutsideInBox F hFΛ ⟨d.right, hdr⟩ ⟨e.right, her⟩) : False :=
  not_separated_of_inside_outside_reachable hsub hd_cross he_ncross
    (boundaryDart_box_adj_left_right e (hFΛ e.left_mem) her)
    (reachableWithin_box_liftFinset_of_reachableWithin hFΛ (hFΛ d.left_mem) (hFΛ e.left_mem) hin)
    hout

end IsingModel
