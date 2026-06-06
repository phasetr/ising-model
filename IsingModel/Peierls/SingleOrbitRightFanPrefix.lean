import IsingModel.Peierls.SingleOrbitRightFan
import IsingModel.Peierls.SingleOrbitFanPrefix

/-!
# Right-fan prefix rotation and completeness (FV §3.7.2)

Dual to `SingleOrbitFanPrefix`/`SingleOrbitFanComplete`: a **right-fan prefix** of length `n` at `d`
is a run of `n` consecutive `nextDart` steps each taking the right turn (neither the left turn nor
going straight valid). Each step keeps the right site fixed, so the prefix rotates the dart around
the fixed right site: `right_eq_iterate_of_rightFanPrefix` (the right site is unchanged),
`dir_eq_iterate_of_rightFanPrefix` (the direction rotated right `n` times),
`left_eq_iterate_of_rightFanPrefix` (the resulting left site). The rotation pins the endpoint:
`eq_iterate_of_rightFanPrefix_of_dir_eq` and `sameOrbit_of_rightFanPrefix_dir_eq`. This is the
complement-side counterpart of the left-fan rotation, needed for the "vary in-site" contact step.

* `BoundaryDart.RightFanPrefix` — `n` consecutive right turns; with `_zero`/`_of_le`/`_succ`.
* `dir_nextDart_of_turnRight` — a right turn rotates the direction right.
* `right_eq_iterate_of_rightFanPrefix` / `dir_eq_iterate_of_rightFanPrefix` /
  `left_eq_iterate_of_rightFanPrefix` — rotation around the fixed right site.
* `eq_iterate_of_rightFanPrefix_of_dir_eq` / `sameOrbit_of_rightFanPrefix_dir_eq` — completeness.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A right-fan prefix of length `n`**: each of the first `n` `nextDart` steps from `d` takes the
right turn (neither the left turn nor going straight is valid). -/
def BoundaryDart.RightFanPrefix (d : BoundaryDart F) (n : ℕ) : Prop :=
  ∀ k < n,
    ¬ ValidAt F (BoundaryDart.nextDart^[k] d).head (BoundaryDart.nextDart^[k] d).dir.turnLeft ∧
      ¬ ValidAt F (BoundaryDart.nextDart^[k] d).head (BoundaryDart.nextDart^[k] d).dir

/-- **The empty right-fan prefix** is vacuous. -/
theorem rightFanPrefix_zero (d : BoundaryDart F) : d.RightFanPrefix 0 :=
  fun k hk => absurd hk (Nat.not_lt_zero k)

/-- **A right-fan prefix restricts to shorter lengths**. -/
theorem rightFanPrefix_of_le (d : BoundaryDart F) {m n : ℕ} (hmn : m ≤ n)
    (h : d.RightFanPrefix n) : d.RightFanPrefix m :=
  fun k hk => h k (lt_of_lt_of_le hk hmn)

/-- **Extending a right-fan prefix by one valid right turn**. -/
theorem rightFanPrefix_succ (d : BoundaryDart F) {n : ℕ} (h : d.RightFanPrefix n)
    (hL : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir.turnLeft)
    (hS : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head (BoundaryDart.nextDart^[n] d).dir) :
    d.RightFanPrefix (n + 1) := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
  · exact h k hlt
  · subst heq; exact ⟨hL, hS⟩

/-- **A right turn rotates the direction right**: `d.nextDart.dir = d.dir.turnRight`. -/
theorem dir_nextDart_of_turnRight (d : BoundaryDart F)
    (hL : ¬ ValidAt F d.head d.dir.turnLeft) (hS : ¬ ValidAt F d.head d.dir) :
    d.nextDart.dir = d.dir.turnRight := by
  rw [nextDart_eq_turnRight d hL hS]

/-- **A right-fan prefix keeps the right site fixed**: rotating right around `d.right`. -/
theorem right_eq_iterate_of_rightFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.RightFanPrefix n) : (BoundaryDart.nextDart^[n] d).right = d.right := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hL, hS⟩ := h m (Nat.lt_succ_self m)
    rw [right_nextDart_of_turnRight (BoundaryDart.nextDart^[m] d) hL hS]
    exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk))

/-- **A right-fan prefix rotates the direction right** `n` times:
`(nextDart^[n] d).dir = turnRight^[n] d.dir`. -/
theorem dir_eq_iterate_of_rightFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.RightFanPrefix n) :
    (BoundaryDart.nextDart^[n] d).dir = (Dir2.turnRight^[n]) d.dir := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨hL, hS⟩ := h m (Nat.lt_succ_self m)
    rw [dir_nextDart_of_turnRight (BoundaryDart.nextDart^[m] d) hL hS,
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- **The left site after a right-fan prefix**: the right site plus the rotated left normal. -/
theorem left_eq_iterate_of_rightFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.RightFanPrefix n) :
    (BoundaryDart.nextDart^[n] d).left =
      d.right + (Dir2.turnLeft ((Dir2.turnRight^[n]) d.dir)).vec := by
  have h1 : (BoundaryDart.nextDart^[n] d).left =
      (BoundaryDart.nextDart^[n] d).right
        + (Dir2.turnLeft (BoundaryDart.nextDart^[n] d).dir).vec := by
    have hx := (BoundaryDart.nextDart^[n] d).left_sub_right
    rw [← hx]; abel
  rw [h1, right_eq_iterate_of_rightFanPrefix d h, dir_eq_iterate_of_rightFanPrefix d h]

/-- **A right-fan prefix is pinned by its rotation**: if `e` shares the right site with `d` and its
direction is `d.dir` rotated right `n` times, with the first `n` steps right turns, then
`nextDart^[n] d = e`. -/
theorem eq_iterate_of_rightFanPrefix_of_dir_eq (d e : BoundaryDart F) {k : ℕ}
    (h : d.RightFanPrefix k) (hR : e.right = d.right)
    (hdir : e.dir = (Dir2.turnRight^[k]) d.dir) : BoundaryDart.nextDart^[k] d = e := by
  apply BoundaryDart.ext_of_left_right
  · rw [left_eq_iterate_of_rightFanPrefix d h]
    have he : e.left = e.right + (Dir2.turnLeft e.dir).vec := by
      have hx := e.left_sub_right; rw [← hx]; abel
    rw [he, hR, hdir]
  · rw [right_eq_iterate_of_rightFanPrefix d h]; exact hR.symm

/-- **Same right site, right-rotated darts share an orbit**. -/
theorem sameOrbit_of_rightFanPrefix_dir_eq (d e : BoundaryDart F) {k : ℕ}
    (h : d.RightFanPrefix k) (hR : e.right = d.right)
    (hdir : e.dir = (Dir2.turnRight^[k]) d.dir) : d.SameOrbit e :=
  ⟨k, eq_iterate_of_rightFanPrefix_of_dir_eq d e h hR hdir⟩

end IsingModel
