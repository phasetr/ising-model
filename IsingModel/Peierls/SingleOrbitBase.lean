import IsingModel.Peierls.SameOrbit
import IsingModel.Peierls.DartPrimalCutCard

/-!
# Boundary darts have faithful site coordinates (FV §3.7.2)

A boundary dart is recovered from its left and right sites: the difference `left - right =
(turnLeft dir).vec` fixes the direction, and the left site then fixes the tail. Thus the map
`d ↦ (d.left, d.right)` is injective, and two darts with the same sites are equal — hence in the
same orbit. This is the base case of the boundary-slide argument toward the single-orbit (discrete
Jordan single-curve) property: the slide tracks a dart by its two sites, so faithful site
coordinates are what make the inductive step well defined.

* `BoundaryDart.left_sub_right` — `d.left - d.right = (turnLeft d.dir).vec`.
* `BoundaryDart.dir_eq_of_left_right` — equal sites give equal directions.
* `BoundaryDart.ext_of_left_right` — equal sites give equal darts.
* `BoundaryDart.left_ne_right` — the two sites of a dart are distinct.
* `BoundaryDart.siteMap` / `BoundaryDart.siteMap_injective` — the site-pair embedding is injective.
* `BoundaryDart.sameOrbit_of_left_right_eq` — equal sites give same-orbit darts.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The site difference of a dart is its left normal**: `d.left - d.right = (turnLeft d.dir).vec`.
The right site is one step back along the left normal from the left site. -/
theorem BoundaryDart.left_sub_right (d : BoundaryDart F) :
    d.left - d.right = (Dir2.turnLeft d.dir).vec := by
  have h : d.right = d.left - (Dir2.turnLeft d.dir).vec := rfl
  rw [h]; abel

/-- **Equal sites give equal directions**: the left normal `(turnLeft dir).vec` is determined by
`left - right`, and `turnLeft`/`vec` are injective. -/
theorem BoundaryDart.dir_eq_of_left_right {d e : BoundaryDart F}
    (hL : d.left = e.left) (hR : d.right = e.right) : d.dir = e.dir := by
  have hvec : (Dir2.turnLeft d.dir).vec = (Dir2.turnLeft e.dir).vec := by
    rw [← d.left_sub_right, ← e.left_sub_right, hL, hR]
  exact Dir2.turnLeft_injective (Dir2.vec_injective hvec)

/-- **A boundary dart is determined by its two sites**: if `d.left = e.left` and `d.right = e.right`
then `d = e`. -/
theorem BoundaryDart.ext_of_left_right {d e : BoundaryDart F}
    (hL : d.left = e.left) (hR : d.right = e.right) : d = e := by
  have hdir : d.dir = e.dir := BoundaryDart.dir_eq_of_left_right hL hR
  have htail : d.tail = e.tail := by
    change leftSite d.tail d.dir = leftSite e.tail e.dir at hL
    rw [← hdir] at hL
    exact leftSite_injective_tail d.dir hL
  exact BoundaryDart.ext' htail hdir

/-- **The two sites of a dart are distinct**: the left site lies in `F`, the right site does not. -/
theorem BoundaryDart.left_ne_right (d : BoundaryDart F) : d.left ≠ d.right := by
  intro h
  apply d.right_not_mem
  have hmem : d.left ∈ F := d.left_mem
  rwa [h] at hmem

/-- The **site-pair coordinates** of a boundary dart. -/
def BoundaryDart.siteMap (d : BoundaryDart F) : (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  (d.left, d.right)

/-- **The site-pair embedding is injective**: a dart is faithfully recorded by its two sites. -/
theorem BoundaryDart.siteMap_injective :
    Function.Injective (BoundaryDart.siteMap (F := F)) := by
  intro d e h
  exact BoundaryDart.ext_of_left_right (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **Equal sites give same-orbit darts** (base case of the boundary slide): darts with identical
left and right sites are equal, hence trivially in the same orbit. -/
theorem BoundaryDart.sameOrbit_of_left_right_eq {d e : BoundaryDart F}
    (hL : d.left = e.left) (hR : d.right = e.right) : d.SameOrbit e := by
  have h := BoundaryDart.ext_of_left_right hL hR
  subst h
  exact BoundaryDart.SameOrbit.refl d

end IsingModel
