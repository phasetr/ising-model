import IsingModel.Peierls.ConnectedDroplet
import IsingModel.AmbientLattice.Defs.Core

/-!
# Transferring connectivity from a box droplet to its image (FV §3.7.2)

The within-`F` connectivity input is supplied by transferring connectivity from the box. A droplet
`S : Finset ↑Λ` reachable within `Ambient.inducedGraph G Λ` maps, under `Subtype.val`, to vertices
reachable within the image `S.image Subtype.val` in the ambient graph `G`
(`reachableWithin_image_val`); hence a connected droplet in the box yields a within-image-connected
set in the ambient lattice (`reachableWithin_image_of_isConnectedDroplet`). With
`G = latticeGraph 2`
this is exactly the `F`-connectivity `hreach` input for `F = S.image Subtype.val`.

* `reachableWithin_image_val` — reachability transfers along `Subtype.val`.
* `reachableWithin_image_of_isConnectedDroplet` — a box connected droplet is image-connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Reachability transfers along `Subtype.val`**: a within-`S` path in `Ambient.inducedGraph G Λ`
maps to a within-`S.image Subtype.val` path in `G`. -/
theorem reachableWithin_image_val {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Λ : Finset V)
    (S : Finset ↑Λ) {x y : ↑Λ}
    (h : ReachableWithin (Ambient.inducedGraph G Λ) S x y) :
    ReachableWithin G (S.image Subtype.val) (x : V) (y : V) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hedge ih =>
    obtain ⟨hadj, ha, hb⟩ := hedge
    exact ih.tail ⟨hadj, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩

/-- **A box connected droplet is image-connected**: if `S` is a connected droplet in
`Ambient.inducedGraph G Λ`, then any two vertices of `S.image Subtype.val` are image-reachable. -/
theorem reachableWithin_image_of_isConnectedDroplet {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (Λ : Finset V) (S : Finset ↑Λ)
    (hS : IsConnectedDroplet (Ambient.inducedGraph G Λ) S)
    (a : V) (ha : a ∈ S.image Subtype.val) (b : V) (hb : b ∈ S.image Subtype.val) :
    ReachableWithin G (S.image Subtype.val) a b := by
  obtain ⟨x, hxS, hxa⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hyS, hyb⟩ := Finset.mem_image.mp hb
  subst hxa; subst hyb
  exact reachableWithin_image_val G Λ S (hS x hxS y hyS)

end IsingModel
