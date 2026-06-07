import IsingModel.Peierls.SingleOrbitCutDirDart
import IsingModel.Peierls.SingleOrbitFaceCard
import IsingModel.Peierls.NextDart
import IsingModel.Peierls.SameOrbit
import IsingModel.Peierls.DartDualCutCard

/-!
# The degree-two pairing of the contour (FV §3.7.2)

At a **degree-two** dual vertex (`squareSplitCount F c = 2`) the contour passes through without
branching: of the two incident cut directions one is the reverse `d.dir + 2` of the incoming dart
`d` (the edge
back to `d.tail`) and the other is the direction `d.nextDart.dir` of the outgoing dart, so
`cutDirs F d.head = {d.dir + 2, d.nextDart.dir}` (`cutDirs_head_eq_of_squareSplitCount_eq_two`). The
incoming and outgoing darts therefore share a `nextDart` orbit
(`BoundaryDart.sameOrbit_nextDart`). This is the local pairing that, vertex by vertex, glues the
boundary darts into the cycles of the contour — the degree-two case of the discrete-Jordan argument.

* `dir_add_two_mem_cutDirs_head` — the incoming dart's reverse is a cut direction at its head.
* `nextDart_dir_cases` / `nextDart_dir_mem_cutDirs_head` — the successor turns and cuts.
* `nextDart_dir_ne_dir_add_two` — the successor never reverses the incoming dart.
* `cutDirs_head_eq_of_squareSplitCount_eq_two` — the degree-two cut set is exactly the pair.
* `BoundaryDart.sameOrbit_nextDart` — a dart shares its orbit with its successor.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **A dart shares its orbit with its successor** under `nextDart`. -/
theorem BoundaryDart.sameOrbit_nextDart {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.SameOrbit d.nextDart :=
  ⟨1, rfl⟩

/-- **The incoming dart's reverse is a cut direction at its head**: `d.dir + 2 ∈ cutDirs F d.head`.
The reversed dart `(d.head + (d.dir + 2).vec, (d.dir + 2) + 2)` is just `d` itself (back at
`d.tail` in direction `d.dir`), which is valid. -/
theorem dir_add_two_mem_cutDirs_head {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.dir + 2 ∈ cutDirs F d.head := by
  apply mem_cutDirs_of_validAt_reverse
  have ht : d.head + (d.dir + 2).vec = d.tail := by
    rw [BoundaryDart.head, Dir2.vec_add_two]; abel
  have hd : d.dir + 2 + 2 = d.dir := by
    have h4 : (2 + 2 : Dir2) = 0 := by decide
    rw [add_assoc, h4, add_zero]
  rw [ht, hd]
  exact ⟨d.left_mem, d.right_not_mem⟩

/-- **The successor's direction** is one of the left turn, straight ahead, or right turn. -/
theorem nextDart_dir_cases {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.nextDart.dir = d.dir.turnLeft ∨ d.nextDart.dir = d.dir ∨
      d.nextDart.dir = d.dir.turnRight := by
  classical
  unfold BoundaryDart.nextDart
  by_cases hL : ValidAt F d.head d.dir.turnLeft
  · rw [dif_pos hL]; exact Or.inl rfl
  · rw [dif_neg hL]
    by_cases hS : ValidAt F d.head d.dir
    · rw [dif_pos hS]; exact Or.inr (Or.inl rfl)
    · rw [dif_neg hS]; exact Or.inr (Or.inr rfl)

/-- **The successor's direction is a cut direction at the incoming head**, since the successor is a
valid dart whose tail is that head. -/
theorem nextDart_dir_mem_cutDirs_head {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.nextDart.dir ∈ cutDirs F d.head := by
  have h := dir_mem_cutDirs_tail d.nextDart
  rwa [BoundaryDart.nextDart_tail] at h

/-- **The successor never reverses the incoming dart**: `d.nextDart.dir ≠ d.dir + 2`. The successor
turns left, goes straight, or turns right (`d.dir + 1, d.dir, d.dir + 3`), none of which is the
reverse `d.dir + 2`. -/
theorem nextDart_dir_ne_dir_add_two {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F) :
    d.nextDart.dir ≠ d.dir + 2 := by
  rcases nextDart_dir_cases d with h | h | h
  · rw [h, Dir2.turnLeft, ne_eq, add_right_inj]; decide
  · rw [h]; intro hc
    nth_rewrite 1 [← add_zero d.dir] at hc
    exact absurd (add_left_cancel hc) (by decide)
  · rw [h, Dir2.turnRight, ne_eq, add_right_inj]; decide

/-- **The degree-two cut set is exactly the incoming-reverse / outgoing pair**: at a dual vertex of
degree two, `cutDirs F d.head = {d.dir + 2, d.nextDart.dir}`. -/
theorem cutDirs_head_eq_of_squareSplitCount_eq_two {F : Finset (Fin 2 → ℤ)} (d : BoundaryDart F)
    (hdeg : squareSplitCount F d.head = 2) :
    cutDirs F d.head = {d.dir + 2, d.nextDart.dir} := by
  have hcard : (cutDirs F d.head).card = 2 := by
    rw [cutDirs, ← squareSplitCount_eq_card_cut_dirs]; exact hdeg
  have hne : d.dir + 2 ≠ d.nextDart.dir := fun h => nextDart_dir_ne_dir_add_two d h.symm
  have hsub : ({d.dir + 2, d.nextDart.dir} : Finset Dir2) ⊆ cutDirs F d.head := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [h]; exact dir_add_two_mem_cutDirs_head d
    · rw [h]; exact nextDart_dir_mem_cutDirs_head d
  have hpair : ({d.dir + 2, d.nextDart.dir} : Finset Dir2).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcard.trans hpair.symm))).symm

end IsingModel
