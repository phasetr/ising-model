import IsingModel.Peierls.SingleOrbitFan
import IsingModel.Peierls.DartOrbit
import IsingModel.Peierls.ConnectedDroplet
import IsingModel.Peierls.GridEdge2

/-!
# Left site stays `F`-reachable across one step (FV §3.7.2)

As `nextDart` advances, the **left site stays inside `F` and reachable within `F`**, regardless of
the turn taken. A left turn keeps the left site fixed (reflexive); a straight step advances it by
one lattice edge inside `F` (single step); a right turn moves it by two edges through the head
sites, both forced into `F` (`leftSite_head_mem_of_not_turnLeft`,
`rightSite_head_mem_of_not_turnLeft_not_straight`, extracted from the validity propagation of
`right_valid_of_not_left_not_straight`). The combined `reachableWithin_left_nextDart` says the left
site of `nextDart d` is always `F`-reachable from `d.left` — by induction, every dart on the forward
orbit has its left site in the single `F`-component of `d.left`, the `F`-side half of the orbit
component invariant feeding `sameOrbit_of_left_right_reachable`.

(The complement-side counterpart is *not* uniformly local — a left turn lacks a forced complement
bridge — and is handled separately via contact-pair chains, not via this orbit-step invariant.)

* `leftSite_head_mem_of_not_turnLeft` / `rightSite_head_mem_of_not_turnLeft_not_straight` — forced
  `F`-membership at the head.
* `adj_leftSite_rightSite` — the two sites at a tail/direction are lattice-adjacent.
* `reachableWithin_left_nextDart_of_{turnLeft,straight,turnRight}` — the per-case bridge.
* `reachableWithin_left_nextDart` — the combined per-step `F`-reachability.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A failed left turn forces the head's straight left site into `F`** (extracted from the
validity propagation of `right_valid_of_not_left_not_straight`). -/
theorem leftSite_head_mem_of_not_turnLeft (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) : leftSite d.head d.dir ∈ F := by
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead] at hL ⊢
  have e1 := leftSite_head_turnLeft d.tail d.dir
  have e2 := rightSite_head_turnLeft_eq_leftSite_head d.tail d.dir
  unfold ValidAt at hL
  have s1 : leftSite (d.tail + d.dir.vec) d.dir.turnLeft ∈ F := e1 ▸ d.left_mem
  have s2 : rightSite (d.tail + d.dir.vec) d.dir.turnLeft ∈ F := by
    by_contra hc; exact hL ⟨s1, hc⟩
  exact e2 ▸ s2

/-- **A failed left turn and straight step force the head's straight right site into `F`**. -/
theorem rightSite_head_mem_of_not_turnLeft_not_straight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    rightSite d.head d.dir ∈ F := by
  have s3 := leftSite_head_mem_of_not_turnLeft d hL
  have hhead : d.head = d.tail + d.dir.vec := rfl
  rw [hhead] at hS s3 ⊢
  unfold ValidAt at hS
  by_contra hc
  exact hS ⟨s3, hc⟩

/-- **The two sites at a tail and direction are lattice-adjacent**. -/
theorem adj_leftSite_rightSite (t : Fin 2 → ℤ) (δ : Dir2) :
    (latticeGraph 2).Adj (leftSite t δ) (rightSite t δ) := by
  obtain ⟨k, hk | hk⟩ := leftSite_rightSite_adjacent t δ
  · rw [hk]; exact (GridEdge2.latticeGraph_adj_add_unitVec2 _ k).symm
  · rw [hk]; exact GridEdge2.latticeGraph_adj_add_unitVec2 _ k

/-- **Left turn: the left site is unchanged**, hence `F`-reachable (reflexively). -/
theorem reachableWithin_left_nextDart_of_turnLeft (d : BoundaryDart F)
    (hL : ValidAt F d.head d.dir.turnLeft) :
    ReachableWithin (latticeGraph 2) F d.left d.nextDart.left := by
  rw [left_nextDart_of_turnLeft d hL]
  exact Relation.ReflTransGen.refl

/-- **Straight step: the left site advances by one `F`-edge**. -/
theorem reachableWithin_left_nextDart_of_straight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ValidAt F d.head d.dir) :
    ReachableWithin (latticeGraph 2) F d.left d.nextDart.left := by
  rw [left_nextDart_of_straight d hL hS]
  have he : leftSite d.head d.dir = d.left + d.dir.vec := by
    change leftSite (d.tail + d.dir.vec) d.dir = leftSite d.tail d.dir + d.dir.vec
    rw [leftSite_add]
  have hadj : (latticeGraph 2).Adj d.left (leftSite d.head d.dir) := by
    rw [he]; exact latticeGraph_adj_dirVec d.left d.dir
  exact Relation.ReflTransGen.single ⟨hadj, d.left_mem, hS.1⟩

/-- **Right turn: the left site moves two `F`-edges through the head sites**. -/
theorem reachableWithin_left_nextDart_of_turnRight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    ReachableWithin (latticeGraph 2) F d.left d.nextDart.left := by
  rw [left_nextDart_of_turnRight d hL hS]
  have hmidF : leftSite d.head d.dir ∈ F := leftSite_head_mem_of_not_turnLeft d hL
  have hrF : rightSite d.head d.dir ∈ F := rightSite_head_mem_of_not_turnLeft_not_straight d hL hS
  have he : leftSite d.head d.dir = d.left + d.dir.vec := by
    change leftSite (d.tail + d.dir.vec) d.dir = leftSite d.tail d.dir + d.dir.vec
    rw [leftSite_add]
  have hadj1 : (latticeGraph 2).Adj d.left (leftSite d.head d.dir) := by
    rw [he]; exact latticeGraph_adj_dirVec d.left d.dir
  have hadj2 : (latticeGraph 2).Adj (leftSite d.head d.dir) (rightSite d.head d.dir) :=
    adj_leftSite_rightSite d.head d.dir
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single ⟨hadj1, d.left_mem, hmidF⟩) ⟨hadj2, hmidF, hrF⟩

/-- **The left site is always `F`-reachable across one `nextDart` step** (all three turn cases). -/
theorem reachableWithin_left_nextDart (d : BoundaryDart F) :
    ReachableWithin (latticeGraph 2) F d.left d.nextDart.left := by
  by_cases hL : ValidAt F d.head d.dir.turnLeft
  · exact reachableWithin_left_nextDart_of_turnLeft d hL
  · by_cases hS : ValidAt F d.head d.dir
    · exact reachableWithin_left_nextDart_of_straight d hL hS
    · exact reachableWithin_left_nextDart_of_turnRight d hL hS

end IsingModel
