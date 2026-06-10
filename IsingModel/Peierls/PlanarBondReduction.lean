import IsingModel.Peierls.DualCutInBox
import IsingModel.Peierls.DartDualReachable

/-!
# Edge-connectivity of the dual cut from the planar bond lemma (FV §3.7.2)

This file is the **convergent re-foundation** of the Peierls edge-connectivity crux. The whole
conditional `m*(β) > 0` argument needs only that the common-box dual cut `dualCutInBox` of a
finite **filled, connected** droplet `F ⊆ ℤ²` is edge-connected. We isolate that statement on a
single genuine hard input — the *planar bond lemma* — and discharge everything else.

The planar bond lemma is the statement that two boundary darts whose **inside endpoints are
connected inside `F`** and whose **outside endpoints are connected in the complement** have
edge-connected dual edges:

    hbond : ReachableWithin (latticeGraph 2) F d.left e.left →
            ReachableOutside F d.right e.right →
            DartReachable F d e

This is the genuine discrete-Jordan separation content (the only remaining open obligation); it is
supplied here as an explicit hypothesis. Given it, together with
* `hF` — connectivity of `F` (supplied upstream by `isConnectedDroplet_filledRegion`), and
* `hC` — connectivity of the complement (supplied by `reachableWithin_compl_of_isFilled`),

the dual cut is edge-connected at every layer (`dartDualCut`, `dualCutSub`, `dualCutInBox`), via the
already-proved `dartDualCut_isEdgeConnected_of_dartReachable` and the subtype/image bridges.

This replaces the non-converging `rayExitAnchorDartMap` first-exit anchor route (#3747–#3895): the
first-exit index is discontinuous across a vertical step, so `hstep`/`hanchor` disguise the global
Jordan fact as an infinite regress of local case-splits. The bond lemma is the correct factoring —
it cleanly separates the (easy, already-proved) connectivity inputs from the single planar core.

* `dartDualCut_isEdgeConnected_of_bond` — whole-cut edge-connectivity from `hbond`, `hF`, `hC`.
* `dualCutSub_isEdgeConnected_of_bond` — its subtype-lift.
* `dualCutInBox_isEdgeConnected_of_bond` — the common-box form consumed by `PeierlsContourCount`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Reachability in the complement of `F`**: `x` reaches `y` by a chain of `latticeGraph 2`
adjacencies staying outside `F`. Unlike `ReachableWithin` this avoids a `Finset` ambient (the
complement of a finite `F` in the infinite lattice `Fin 2 → ℤ` is not a `Finset`), so it carries no
`Fintype` requirement. -/
def ReachableOutside (F : Finset (Fin 2 → ℤ)) (x y : Fin 2 → ℤ) : Prop :=
  Relation.ReflTransGen (fun a b => (latticeGraph 2).Adj a b ∧ a ∉ F ∧ b ∉ F) x y

/-- Complement reachability is reflexive. -/
@[refl] theorem ReachableOutside.refl (x : Fin 2 → ℤ) : ReachableOutside F x x :=
  Relation.ReflTransGen.refl

/-- Complement reachability is transitive. -/
theorem ReachableOutside.trans {x y z : Fin 2 → ℤ} (h₁ : ReachableOutside F x y)
    (h₂ : ReachableOutside F y z) : ReachableOutside F x z :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Complement reachability is symmetric (the underlying complement-adjacency relation is). -/
theorem ReachableOutside.symm {x y : Fin 2 → ℤ} (h : ReachableOutside F x y) :
    ReachableOutside F y x :=
  Relation.ReflTransGen.symmetric
    (fun _ _ hab => ⟨hab.1.symm, hab.2.2, hab.2.1⟩) h

/-- A single complement edge gives complement reachability. -/
theorem ReachableOutside.of_adj {x y : Fin 2 → ℤ} (hadj : (latticeGraph 2).Adj x y)
    (hx : x ∉ F) (hy : y ∉ F) : ReachableOutside F x y :=
  Relation.ReflTransGen.single ⟨hadj, hx, hy⟩

/-- **The planar bond hypothesis**: every two boundary darts whose inside endpoints are connected
inside `F` and whose outside endpoints are connected in the complement of `F` have reachable dual
edges. This is the single genuine discrete-Jordan obligation; the connectivity premises it consumes
are both already available for filled connected droplets. -/
def PlanarBondHypothesis (F : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ d e : BoundaryDart F,
    ReachableWithin (latticeGraph 2) F d.left e.left →
    ReachableOutside F d.right e.right →
    DartReachable F d e

/-- **Pairwise dart reachability from the planar bond lemma**: feeding the bond hypothesis the
`F`-connectivity of the inside endpoints and the complement-connectivity of the outside endpoints
yields reachability of every pair of boundary darts. -/
theorem dartReachable_of_bond
    (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ a, a ∉ F → ∀ b, b ∉ F → ReachableOutside F a b)
    (d e : BoundaryDart F) : DartReachable F d e :=
  hbond d e (hF _ d.left_mem _ e.left_mem) (hC _ d.right_not_mem _ e.right_not_mem)

/-- **Whole dual cut edge-connected from the planar bond lemma**: the ambient dual cut `dartDualCut`
is edge-connected once the bond hypothesis and the two connectivity inputs are supplied. -/
theorem dartDualCut_isEdgeConnected_of_bond
    (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ a, a ∉ F → ∀ b, b ∉ F → ReachableOutside F a b) :
    IsEdgeConnected (dartDualCut F) :=
  dartDualCut_isEdgeConnected_of_dartReachable (dartReachable_of_bond hbond hF hC)

/-- **The subtype-lifted dual cut is edge-connected from the planar bond lemma**. -/
theorem dualCutSub_isEdgeConnected_of_bond
    (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ a, a ∉ F → ∀ b, b ∉ F → ReachableOutside F a b) :
    IsEdgeConnected (dualCutSub F) := by
  apply isEdgeConnected_of_image_map_subtype
  rw [dualCutSub_image_map_val]
  exact dartDualCut_isEdgeConnected_of_bond hbond hF hC

/-- **The common-box dual cut is edge-connected from the planar bond lemma**: the form consumed by
`PeierlsContourCount` for the contour bound. -/
theorem dualCutInBox_isEdgeConnected_of_bond {Λd : Finset (Fin 2 → ℤ)}
    (hsub : dualSupport F ⊆ Λd)
    (hbond : PlanarBondHypothesis F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, ReachableWithin (latticeGraph 2) F a b)
    (hC : ∀ a, a ∉ F → ∀ b, b ∉ F → ReachableOutside F a b) :
    IsEdgeConnected (dualCutInBox hsub) :=
  isEdgeConnected_image_map (dualCutSub_isEdgeConnected_of_bond hbond hF hC)

end IsingModel
