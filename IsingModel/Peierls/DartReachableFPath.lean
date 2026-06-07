import IsingModel.Peierls.DartDualReachable
import IsingModel.Peierls.ConnectedDroplet

/-!
# F-path induction for dual-cut dart reachability (FV §3.7.2)

PR #3748 reduced edge-connectedness of the dual cut `dartDualCut F` to **pairwise**
`DartReachable` on boundary darts, with the bridge being the weak shared-vertex relation
`edgeAdjacentIn` (not `SameOrbit`/`ContactMove`). This file supplies the **path-induction
interface** that turns reachability *inside the region* `F` into `DartReachable`, the shape needed
by the F-path / shared-vertex shadow argument for a connected, filled region.

Concretely, given an assignment `φ` of an *anchor* boundary dart to each site of `F`, a walk inside
`F` (`ReachableWithin G F`) is transported, edge by edge, into a `DartReachable` chain between the
endpoint anchors. The transport is purely the reflexive–transitive closure structure of both
relations; the geometric obligation that the route reduces to is the **per-`F`-edge local step**
`hstep` (equivalently, the per-edge shared-vertex *shadow* `hshadow`). Adding the per-dart anchoring
hypothesis `hanchor` (each dart reaches the anchor of its own left site) then yields pairwise
reachability for any connected `F`, hence `IsEdgeConnected (dartDualCut F)`.

What is **not** done here: neither the anchor map `φ`, the per-edge shadow step `hstep`, nor
the per-dart anchoring `hanchor` is constructed. The per-edge step is the local F-path shadow
input; the anchoring hypothesis is a same-left-site reachability input that may still require
nontrivial wedge/arc geometry. This file isolates those abstract obligations, lowering the global
`dartDualCut_isEdgeConnected_of_connected_filled` target to named hypotheses instead of invoking
single-orbitness.

* `dartReachable_of_reachableWithin` — lift an in-`F` walk to a `DartReachable` chain of anchors,
  given a per-edge `DartReachable` step.
* `dartReachable_of_reachableWithin_shadow` — the same, with the per-edge step packaged as a
  shared dual vertex (the "shadow" form), discharged through `dartReachable_of_shared`.
* `dartReachable_of_anchored` — anchoring + per-edge step + `F`-connectivity give pairwise
  reachability of *all* boundary darts.
* `dartDualCut_isEdgeConnected_of_anchored` — the resulting edge-connectedness of the dual cut.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)} {G : SimpleGraph (Fin 2 → ℤ)}

/-- **Reachability within `F`, reindexed on the subtype of sites of `F`**.  This is the same
walk relation as `ReachableWithin G F`, but with endpoints carrying their membership proofs, so
anchor maps only need to be defined on sites that actually lie in `F`. -/
def ReachableWithinSubtype (G : SimpleGraph (Fin 2 → ℤ)) (F : Finset (Fin 2 → ℤ))
    (a b : {x : Fin 2 → ℤ // x ∈ F}) : Prop :=
  Relation.ReflTransGen (fun x y : {x : Fin 2 → ℤ // x ∈ F} => G.Adj x.1 y.1) a b

/-- Convert the ambient `ReachableWithin` relation to the subtype-indexed version. -/
theorem reachableWithinSubtype_of_reachableWithin {a b : Fin 2 → ℤ} (ha : a ∈ F)
    (hb : b ∈ F) (h : ReachableWithin G F a b) :
    ReachableWithinSubtype G F ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl =>
      rw [show (⟨a, hb⟩ : {x : Fin 2 → ℤ // x ∈ F}) = ⟨a, ha⟩ by ext; rfl]
      exact Relation.ReflTransGen.refl
  | tail _ hcd ih =>
      exact (ih hcd.2.1).tail hcd.1

/-- **Lift a subtype-indexed in-`F` walk to a `DartReachable` chain of anchors**: if `φ`
assigns to each site of `F` a boundary dart and consecutive adjacent sites get `DartReachable`
anchors (`hstep`), then a walk `a ⇝ b` inside `F` gives `DartReachable F (φ a) (φ b)`.
This is the path-induction core: it folds the reflexive–transitive walk in `F` into a
`DartReachable` chain through `DartReachable.trans`, reducing the global goal to the per-edge
step `hstep`. -/
theorem dartReachable_of_reachableWithinSubtype
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, G.Adj a.1 b.1 →
      DartReachable F (φ a) (φ b))
    {a b : {x : Fin 2 → ℤ // x ∈ F}} (h : ReachableWithinSubtype G F a b) :
    DartReachable F (φ a) (φ b) := by
  induction h with
  | refl => exact DartReachable.refl (φ a)
  | tail _ hcd ih => exact ih.trans (hstep _ _ hcd)

/-- **Lift an ambient in-`F` walk to a `DartReachable` chain of anchors**: this is the
`ReachableWithin G F` wrapper around `dartReachable_of_reachableWithinSubtype`. -/
theorem dartReachable_of_reachableWithin
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, G.Adj a.1 b.1 →
      DartReachable F (φ a) (φ b))
    {a b : Fin 2 → ℤ} (ha : a ∈ F) (hb : b ∈ F) (h : ReachableWithin G F a b) :
    DartReachable F (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) :=
  dartReachable_of_reachableWithinSubtype φ hstep
    (reachableWithinSubtype_of_reachableWithin ha hb h)

/-- **Shadow form of the path lift**: the per-edge obligation is given as a shared dual vertex of
the two anchors' dual edges. Each step is discharged by `dartReachable_of_shared`, so an in-`F` walk
lifts to `DartReachable F (φ a) (φ b)`. This is the precise "local adjacent-site shadow step" the
F-path argument supplies edge by edge. -/
theorem dartReachable_of_reachableWithin_shadow
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hshadow : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, G.Adj a.1 b.1 →
      ∃ v : Fin 2 → ℤ, v ∈ s((φ a).tail, (φ a).head) ∧
        v ∈ s((φ b).tail, (φ b).head))
    {a b : Fin 2 → ℤ} (ha : a ∈ F) (hb : b ∈ F) (h : ReachableWithin G F a b) :
    DartReachable F (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) :=
  dartReachable_of_reachableWithin φ
    (fun a b hab => by
      obtain ⟨_, hv1, hv2⟩ := hshadow a b hab
      exact dartReachable_of_shared hv1 hv2)
    ha hb h

/-- **Anchoring + per-edge step + `F`-connectivity give pairwise reachability**: if every boundary
dart reaches the anchor of its own left site (`hanchor`), adjacent `F`-sites have `DartReachable`
anchors (`hstep`), and `F` is connected (`hconn`), then any two boundary darts are reachable. The
route is `d ⇝ φ(d.left) ⇝ φ(e.left) ⇝ e`: the outer steps are `hanchor`, the middle is the
path lift along an `F`-walk between the two left sites. This isolates the global reachability
into explicit obligations: same-left-site anchoring `hanchor` and one-`F`-edge transport `hstep`. -/
theorem dartReachable_of_anchored
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hanchor : ∀ d : BoundaryDart F, DartReachable F d (φ ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, G.Adj a.1 b.1 →
      DartReachable F (φ a) (φ b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin G F a b)
    (d e : BoundaryDart F) : DartReachable F d e := by
  have hpath : DartReachable F (φ ⟨d.left, d.left_mem⟩) (φ ⟨e.left, e.left_mem⟩) :=
    dartReachable_of_reachableWithin φ hstep d.left_mem e.left_mem
      (hconn d.left d.left_mem e.left e.left_mem)
  exact (hanchor d).trans (hpath.trans (hanchor e).symm)

/-- **Edge-connectedness of the dual cut from anchoring data**: combining
`dartReachable_of_anchored` with the dart-interface reduction
`dartDualCut_isEdgeConnected_of_dartReachable` (#3748). This is the target-shaped reduction: it
produces `IsEdgeConnected (dartDualCut F)` from the data `(φ, hanchor, hstep)` plus
`F`-connectivity. It does not construct the data; in particular, `hanchor` remains the
same-left-site reachability input that the later geometric analysis must justify. -/
theorem dartDualCut_isEdgeConnected_of_anchored
    (φ : {x : Fin 2 → ℤ // x ∈ F} → BoundaryDart F)
    (hanchor : ∀ d : BoundaryDart F, DartReachable F d (φ ⟨d.left, d.left_mem⟩))
    (hstep : ∀ a b : {x : Fin 2 → ℤ // x ∈ F}, G.Adj a.1 b.1 →
      DartReachable F (φ a) (φ b))
    (hconn : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin G F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_dartReachable
    (fun d e => dartReachable_of_anchored φ hanchor hstep hconn d e)

end IsingModel
