import IsingModel.Peierls.PlanarBondSeparationBridge
import IsingModel.Peierls.PlanarBondReduction
import IsingModel.Peierls.ComplConnected

/-!
# Box-to-ambient connectivity bridges (FV §3.7.2)

The discharged `planarBondHypothesis` feeds the contour count through `dartReachable_of_bond`, which
consumes inside connectivity `ReachableWithin (latticeGraph 2) F` and outside connectivity
`ReachableOutside F` on the *ambient* lattice. The filled-droplet connectivity facts
(`IsConnectedDroplet`, `reachableWithin_compl_of_isFilled`) are stated on the *box* induced graph.
This file bridges the two: a box-confined reachability lifts to the ambient `latticeGraph 2`.

* `box_val_not_mem_image_of_not_mem` — a box vertex outside `S` has its value outside `S.image val`.
* `reachableWithin_ambient_image_of_box` — box inside-reachability lifts to the ambient lattice.
* `reachableOutside_of_box_compl` — box complement-reachability lifts to ambient `ReachableOutside`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {Λ : Finset (Fin 2 → ℤ)} {S : Finset (↑Λ : Type _)}

/-- **A box vertex outside `S` has its value outside `S.image val`** (by injectivity of `val`). -/
theorem box_val_not_mem_image_of_not_mem {a : (↑Λ : Type _)} (ha : a ∉ S) :
    a.val ∉ S.image Subtype.val := by
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨x, hx, hxv⟩ := hmem
  exact ha (Subtype.val_injective hxv ▸ hx)

/-- **Box inside-reachability lifts to ambient**: a `ReachableWithin` walk on the
induced box graph staying inside `S` lifts to a `ReachableWithin (latticeGraph 2) (S.image val)`
walk between the underlying lattice points. -/
theorem reachableWithin_ambient_image_of_box {a b : (↑Λ : Type _)}
    (h : ReachableWithin (Ambient.inducedGraph (latticeGraph 2) Λ) S a b) :
    ReachableWithin (latticeGraph 2) (S.image Subtype.val) a.val b.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ⟨inducedLattice_adj_iff.mp hbc.1,
      Finset.mem_image_of_mem _ hbc.2.1, Finset.mem_image_of_mem _ hbc.2.2⟩

/-- **Box complement-reachability lifts to ambient outside-reachability**: a `ReachableWithin` walk
on the induced box graph staying in `univ \ S` lifts to a `ReachableOutside (S.image val)` walk. -/
theorem reachableOutside_of_box_compl {a b : (↑Λ : Type _)}
    (h : ReachableWithin (Ambient.inducedGraph (latticeGraph 2) Λ) (Finset.univ \ S) a b) :
    ReachableOutside (S.image Subtype.val) a.val b.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨inducedLattice_adj_iff.mp hbc.1, ?_, ?_⟩
    · exact box_val_not_mem_image_of_not_mem (Finset.mem_sdiff.mp hbc.2.1).2
    · exact box_val_not_mem_image_of_not_mem (Finset.mem_sdiff.mp hbc.2.2).2

/-- **Inside connectivity from a box connected droplet**: if `S` is a connected droplet in the box
graph, then any two points of `S.image val` are reachable inside `S.image val` on the ambient
lattice — the `hF` input of `dartReachable_of_bond` for the region `S.image val`. -/
theorem reachableWithin_ambient_image_of_isConnectedDroplet
    (hS : IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) Λ) S)
    {a b : Fin 2 → ℤ} (ha : a ∈ S.image Subtype.val) (hb : b ∈ S.image Subtype.val) :
    ReachableWithin (latticeGraph 2) (S.image Subtype.val) a b := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact reachableWithin_ambient_image_of_box (hS x hx y hy)

end IsingModel
