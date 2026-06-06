import IsingModel.Peierls.SingleOrbitFan

/-!
# Left-fan prefix rotation (FV §3.7.2)

A **left-fan prefix** of length `n` at a dart `d` is a run of `n` consecutive `nextDart` steps each
taking the left turn. By `left_nextDart_of_turnLeft` every such step keeps the left site fixed, so
the whole prefix rotates the dart around the fixed left site: `left_eq_iterate_of_leftFanPrefix`
(the left site is unchanged) and `dir_eq_iterate_of_leftFanPrefix` (the direction is rotated left
`n` times). The right site then follows (`right_eq_iterate_of_leftFanPrefix`). The general bridge
`sameOrbit_of_iterate_left_right_eq` converts agreement of sites after `n` steps into a same-orbit
conclusion. Together these realise the fan rotation feeding `sameOrbit_of_left_right_reachable`.

* `BoundaryDart.LeftFanPrefix` — `n` consecutive left turns from `d`.
* `left_eq_iterate_of_leftFanPrefix` / `dir_eq_iterate_of_leftFanPrefix` — rotation around the site.
* `right_eq_iterate_of_leftFanPrefix` — the resulting right site.
* `sameOrbit_of_iterate_left_right_eq` — sites agree after `n` steps ⟹ same orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A left-fan prefix of length `n`**: each of the first `n` `nextDart` steps from `d` takes the
left turn (its head admits a valid left turn). -/
def BoundaryDart.LeftFanPrefix (d : BoundaryDart F) (n : ℕ) : Prop :=
  ∀ k < n, ValidAt F (BoundaryDart.nextDart^[k] d).head (BoundaryDart.nextDart^[k] d).dir.turnLeft

/-- **A left-fan prefix keeps the left site fixed**: rotating left around `d.left`. -/
theorem left_eq_iterate_of_leftFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.LeftFanPrefix n) : (BoundaryDart.nextDart^[n] d).left = d.left := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hstep := h m (Nat.lt_succ_self m)
    rw [left_nextDart_of_turnLeft (BoundaryDart.nextDart^[m] d) hstep]
    exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk))

/-- **A left-fan prefix rotates the direction left** `n` times:
`(nextDart^[n] d).dir = turnLeft^[n] d.dir`. -/
theorem dir_eq_iterate_of_leftFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.LeftFanPrefix n) :
    (BoundaryDart.nextDart^[n] d).dir = (Dir2.turnLeft^[n]) d.dir := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hstep := h m (Nat.lt_succ_self m)
    rw [dir_nextDart_of_turnLeft (BoundaryDart.nextDart^[m] d) hstep,
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- **The right site after a left-fan prefix**: it is the fixed left site minus the rotated left
normal. -/
theorem right_eq_iterate_of_leftFanPrefix (d : BoundaryDart F) {n : ℕ}
    (h : d.LeftFanPrefix n) :
    (BoundaryDart.nextDart^[n] d).right =
      d.left - (Dir2.turnLeft ((Dir2.turnLeft^[n]) d.dir)).vec := by
  change (BoundaryDart.nextDart^[n] d).left
      - (Dir2.turnLeft (BoundaryDart.nextDart^[n] d).dir).vec
      = d.left - (Dir2.turnLeft ((Dir2.turnLeft^[n]) d.dir)).vec
  rw [left_eq_iterate_of_leftFanPrefix d h, dir_eq_iterate_of_leftFanPrefix d h]

/-- **Sites agreeing after `n` steps give same orbit**: if the `n`-th forward iterate of `d` shares
both sites with `e`, then `d` and `e` are in the same orbit (the iterate equals `e`). -/
theorem sameOrbit_of_iterate_left_right_eq (d e : BoundaryDart F) (n : ℕ)
    (hL : (BoundaryDart.nextDart^[n] d).left = e.left)
    (hR : (BoundaryDart.nextDart^[n] d).right = e.right) : d.SameOrbit e :=
  (d.sameOrbit_iterate n).trans (BoundaryDart.sameOrbit_of_left_right_eq hL hR)

end IsingModel
