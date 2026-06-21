import IsingModel.Peierls.PlanarBondReduction
import IsingModel.Peierls.PlanarBondDischarge
import IsingModel.Peierls.BondConnectivityBridge
import IsingModel.Peierls.ContourInjective
import IsingModel.Peierls.DartCutChar

/-!
# Unconditional edge-connectivity of a filled droplet's dual cut (FV §3.7.2)

With `planarBondHypothesis` discharged, the dual cut of a filled connected neighbour-closed droplet
is edge-connected **unconditionally**: the inside connectivity comes from the connected droplet
(`#4181`), and the outside connectivity is needed only for boundary-dart right endpoints — which are
neighbours of the droplet, hence box vertices (`NeighbourClosed`), so the box-confined complement
connectivity of a filled region (`reachableWithin_compl_of_isFilled`) suffices.

* `boundaryDart_right_mem_of_neighbourClosed` — a boundary dart's right endpoint is a box vertex.
* `reachableOutside_boundaryDart_right_of_isFilled` — the local outside connectivity at right
  endpoints.
* `dartReachable_of_bond_boundary_hC` (+ `dualCut*` wrappers) — the bond route with `hC` weakened
  to boundary right endpoints.
* `dualCutInBox_isEdgeConnected_filled` — the unconditional filled-droplet edge-connectivity.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {Λ : Finset (Fin 2 → ℤ)}

/-- **A boundary dart's right endpoint is a box vertex**: for a neighbour-closed droplet `S`, the
right site of a boundary dart of `S.image val` (a lattice neighbour of its left site `∈ S`) lies in
`Λ`. -/
theorem boundaryDart_right_mem_of_neighbourClosed {S : Finset (↑Λ : Type _)}
    (hne : NeighbourClosed Λ S) (d : BoundaryDart (S.image Subtype.val)) : d.right ∈ Λ := by
  obtain ⟨x, hxS, hxv⟩ := Finset.mem_image.mp d.left_mem
  exact hne x hxS d.right (hxv ▸ leftSite_adj_rightSite d.tail d.dir)

/-- **Local outside connectivity at boundary right endpoints**: for a filled neighbour-closed
droplet, any two boundary-dart right endpoints are connected outside `S.image val`. -/
theorem reachableOutside_boundaryDart_right_of_isFilled {S : Finset (↑Λ : Type _)} {g : ↑Λ}
    (hne : NeighbourClosed Λ S)
    (hfill : IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S)
    (d e : BoundaryDart (S.image Subtype.val)) :
    ReachableOutside (S.image Subtype.val) d.right e.right := by
  have hdΛ := boundaryDart_right_mem_of_neighbourClosed hne d
  have heΛ := boundaryDart_right_mem_of_neighbourClosed hne e
  have hdS : (⟨d.right, hdΛ⟩ : (↑Λ : Type _)) ∉ S := fun h =>
    d.right_not_mem (Finset.mem_image_of_mem _ h)
  have heS : (⟨e.right, heΛ⟩ : (↑Λ : Type _)) ∉ S := fun h =>
    e.right_not_mem (Finset.mem_image_of_mem _ h)
  exact reachableOutside_of_box_compl (reachableWithin_compl_of_isFilled hfill hdS heS)

variable {F : Finset (Fin 2 → ℤ)}

/-- **Bond route with `hC` weakened to boundary right endpoints**: `DartReachable` from the bond
hypothesis, the inside connectivity, and outside connectivity at boundary right endpoints. -/
theorem dartReachable_of_bond_boundary_hC (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ d e : BoundaryDart F, ReachableOutside F d.right e.right)
    (d e : BoundaryDart F) : DartReachable F d e :=
  hbond d e (hF _ d.left_mem _ e.left_mem) (hC d e)

/-- **Whole dual cut edge-connected from the boundary-`hC` bond route**. -/
theorem dartDualCut_isEdgeConnected_of_bond_boundary_hC (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ d e : BoundaryDart F, ReachableOutside F d.right e.right) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_dartReachable (dartReachable_of_bond_boundary_hC hbond hF hC)

/-- **Subtype-lifted dual cut edge-connected from the boundary-`hC` bond route**. -/
theorem dualCutSub_isEdgeConnected_of_bond_boundary_hC (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ d e : BoundaryDart F, ReachableOutside F d.right e.right) :
    IsEdgeConnected (dualCutSub F) := by
  apply isEdgeConnected_of_image_map_subtype
  rw [dualCutSub_image_map_val]
  exact dartDualCut_isEdgeConnected_of_bond_boundary_hC hbond hF hC

/-- **Common-box dual cut edge-connected from the boundary-`hC` bond route**. -/
theorem dualCutInBox_isEdgeConnected_of_bond_boundary_hC {Λd : Finset (Fin 2 → ℤ)}
    (hsub : dualSupport F ⊆ Λd) (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ d e : BoundaryDart F, ReachableOutside F d.right e.right) :
    IsEdgeConnected (dualCutInBox hsub) :=
  isEdgeConnected_image_map (dualCutSub_isEdgeConnected_of_bond_boundary_hC hbond hF hC)

/-- **The dual cut of a filled connected neighbour-closed droplet is edge-connected**
(unconditionally): the bond hypothesis is `planarBondHypothesis`, the inside connectivity is the
connected droplet, and the boundary `hC` is the filled complement connectivity. -/
theorem dualCutInBox_isEdgeConnected_filled {Λd : Finset (Fin 2 → ℤ)} {S : Finset (↑Λ : Type _)}
    {g : ↑Λ} (hsub : dualSupport (S.image Subtype.val) ⊆ Λd)
    (hne : NeighbourClosed Λ S)
    (hconn : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    (hfill : IsFilled (Ambient.inducedGraph (latticeGraph 2) Λ) g S) :
    IsEdgeConnected (dualCutInBox hsub) :=
  dualCutInBox_isEdgeConnected_of_bond_boundary_hC hsub (planarBondHypothesis _)
    (fun _ ha _ hb => reachableWithin_ambient_image_of_isConnectedDroplet hconn ha hb)
    (reachableOutside_boundaryDart_right_of_isFilled hne hfill)

end IsingModel
