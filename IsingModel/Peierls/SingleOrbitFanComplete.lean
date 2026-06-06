import IsingModel.Peierls.SingleOrbitFanPrefix

/-!
# Left-fan prefix completeness (FV §3.7.2)

The forward left-fan rotation (`SingleOrbitFanPrefix`) is pinned down: a left-fan prefix is
determined, up to its endpoint, by the rotation it performs. If a dart `e` sits at the **same left
site** as `d` and its direction is `d.dir` rotated left `k` times, and the first `k` steps from `d`
are all left turns, then the `k`-th forward iterate of `d` is exactly `e`
(`eq_iterate_of_leftFanPrefix_of_dir_eq`) — because both sites then agree
(`left_eq_iterate`, `right_eq_iterate`) and a dart is determined by its sites. Hence such `d` and
`e` are in the same orbit (`sameOrbit_of_leftFanPrefix_dir_eq`). The structural lemmas
`leftFanPrefix_zero` / `leftFanPrefix_of_le` / `leftFanPrefix_succ` give the prefix order.

* `leftFanPrefix_zero` / `leftFanPrefix_of_le` / `leftFanPrefix_succ` — prefix structure.
* `eq_iterate_of_leftFanPrefix_of_dir_eq` — the rotation pins the endpoint.
* `sameOrbit_of_leftFanPrefix_dir_eq` — same-site, rotated darts are in one orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The empty left-fan prefix** is vacuous. -/
theorem leftFanPrefix_zero (d : BoundaryDart F) : d.LeftFanPrefix 0 :=
  fun k hk => absurd hk (Nat.not_lt_zero k)

/-- **A left-fan prefix restricts to shorter lengths**. -/
theorem leftFanPrefix_of_le (d : BoundaryDart F) {m n : ℕ} (hmn : m ≤ n)
    (h : d.LeftFanPrefix n) : d.LeftFanPrefix m :=
  fun k hk => h k (lt_of_lt_of_le hk hmn)

/-- **Extending a left-fan prefix by one valid left turn**. -/
theorem leftFanPrefix_succ (d : BoundaryDart F) {n : ℕ} (h : d.LeftFanPrefix n)
    (hstep : ValidAt F (BoundaryDart.nextDart^[n] d).head
      (BoundaryDart.nextDart^[n] d).dir.turnLeft) :
    d.LeftFanPrefix (n + 1) := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
  · exact h k hlt
  · subst heq; exact hstep

/-- **A left-fan prefix is pinned by its rotation**: if `e` is at the same left site as `d` with
direction `d.dir` rotated left `k` times, and the first `k` steps from `d` are left turns, then the
`k`-th forward iterate of `d` is exactly `e`. -/
theorem eq_iterate_of_leftFanPrefix_of_dir_eq (d e : BoundaryDart F) {k : ℕ}
    (hfan : d.LeftFanPrefix k) (hL : e.left = d.left)
    (hdir : e.dir = (Dir2.turnLeft^[k]) d.dir) : BoundaryDart.nextDart^[k] d = e := by
  apply BoundaryDart.ext_of_left_right
  · rw [left_eq_iterate_of_leftFanPrefix d hfan]; exact hL.symm
  · rw [right_eq_iterate_of_leftFanPrefix d hfan]
    change d.left - (Dir2.turnLeft ((Dir2.turnLeft^[k]) d.dir)).vec
      = e.left - (Dir2.turnLeft e.dir).vec
    rw [hL, hdir]

/-- **Same-site, rotated darts share an orbit**: under the hypotheses of
`eq_iterate_of_leftFanPrefix_of_dir_eq`, `d` and `e` are in the same orbit. -/
theorem sameOrbit_of_leftFanPrefix_dir_eq (d e : BoundaryDart F) {k : ℕ}
    (hfan : d.LeftFanPrefix k) (hL : e.left = d.left)
    (hdir : e.dir = (Dir2.turnLeft^[k]) d.dir) : d.SameOrbit e :=
  ⟨k, eq_iterate_of_leftFanPrefix_of_dir_eq d e hfan hL hdir⟩

end IsingModel
