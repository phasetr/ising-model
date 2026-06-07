import IsingModel.Peierls.SingleOrbitDegTwoPairing
import IsingModel.Peierls.SingleOrbitFaceDeg

/-!
# The degree-four crossing of the contour (FV §3.7.2)

At a **degree-four** dual vertex (`squareSplitCount F c = 4`) all four sides of the unit square are
cut and the four corner sites strictly alternate across `F` (a checkerboard crossing). Under the
left-hand traversal rule the contour **rounds the corner**: the left turn is always valid there
(`validAt_head_turnLeft_of_squareSplitCount_eq_four`), so `nextDart` takes the left turn
(`nextDart_dir_eq_turnLeft_of_squareSplitCount_eq_four`). This is the corner-rounding convention
that keeps the contour from crossing itself, the degree-four case of the discrete-Jordan argument.

* `cutDirs_eq_univ_of_squareSplitCount_eq_four` — every direction is cut at a degree-four vertex.
* `validAt_head_turnLeft_iff` — the left turn is valid iff the straight left site is outside `F`.
* `validAt_head_turnLeft_of_squareSplitCount_eq_four` — at a crossing the left turn is valid.
* `nextDart_dir_eq_turnLeft_of_squareSplitCount_eq_four` — `nextDart` rounds the corner left.
* `nextDart_pairs_squareSplitCount_four` — the degree-four local pairing bundle.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, Figure 3.11, p. 111 (corner-rounding rule); pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Every direction is cut at a degree-four vertex**: `cutDirs F c = univ`. -/
theorem cutDirs_eq_univ_of_squareSplitCount_eq_four (F : Finset (Fin 2 → ℤ)) (c : Fin 2 → ℤ)
    (h : squareSplitCount F c = 4) : cutDirs F c = Finset.univ := by
  have hcard : (cutDirs F c).card = 4 := by
    rw [cutDirs, ← squareSplitCount_eq_card_cut_dirs]; exact h
  exact Finset.eq_univ_of_card _ (by rw [hcard]; decide)

/-- **The left turn is valid iff the straight left site is outside `F`.** The left turn's left site
is the incoming left site (always in `F`), and its right site is the straight-ahead left site. -/
theorem validAt_head_turnLeft_iff {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    ValidAt F d.head d.dir.turnLeft ↔ leftSite d.head d.dir ∉ F := by
  have e1 := leftSite_head_turnLeft d.tail d.dir
  have e2 := rightSite_head_turnLeft_eq_leftSite_head d.tail d.dir
  unfold ValidAt
  rw [show d.head = d.tail + d.dir.vec from rfl, e1, e2]
  exact ⟨fun h => h.2, fun h => ⟨d.left_mem, h⟩⟩

/-- **At a degree-four crossing the left turn is valid**. The checkerboard alternation of the four
corner sites, together with the incoming dart's validity, forces the straight-ahead left site at the
head out of `F`. -/
theorem validAt_head_turnLeft_of_squareSplitCount_eq_four {F : Finset (Fin 2 → ℤ)}
    (d : BoundaryDart F) (hdeg : squareSplitCount F d.head = 4) :
    ValidAt F d.head d.dir.turnLeft := by
  obtain ⟨t, δ, hlm, hrm⟩ := d
  rw [validAt_head_turnLeft_iff]
  simp only [BoundaryDart.head] at hdeg ⊢
  obtain ⟨hA, hB, hC⟩ := (squareSplitCount_eq_four_iff F (t + δ.vec)).1 hdeg
  fin_cases δ <;>
    simp_all [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2, decide_eq_decide]

/-- **`nextDart` rounds the corner left at a degree-four crossing**. -/
theorem nextDart_dir_eq_turnLeft_of_squareSplitCount_eq_four {F : Finset (Fin 2 → ℤ)}
    (d : BoundaryDart F) (hdeg : squareSplitCount F d.head = 4) :
    d.nextDart.dir = d.dir.turnLeft := by
  classical
  have hL := validAt_head_turnLeft_of_squareSplitCount_eq_four d hdeg
  unfold BoundaryDart.nextDart
  rw [dif_pos hL]

/-- **The degree-four local pairing**: at a crossing the incoming dart shares its orbit with its
successor, which starts at the head and turns left. -/
theorem nextDart_pairs_squareSplitCount_four {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F)
    (hdeg : squareSplitCount F d.head = 4) :
    d.SameOrbit d.nextDart ∧ d.nextDart.tail = d.head ∧ d.nextDart.dir = d.dir.turnLeft :=
  ⟨d.sameOrbit_nextDart, d.nextDart_tail,
    nextDart_dir_eq_turnLeft_of_squareSplitCount_eq_four d hdeg⟩

end IsingModel
