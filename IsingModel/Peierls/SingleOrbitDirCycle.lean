import IsingModel.Peierls.Dir2

/-!
# The left turn is a 4-cycle on directions (FV §3.7.2)

`Dir2` is `Fin 4` and `turnLeft` is `· + 1`, a 4-cycle on the directions. Hence any target direction
is reached from any starting direction by fewer than four left turns
(`Dir2.exists_turnLeft_iterate_lt_four`). This is the rotational backbone of the wedge argument: a
left fan can be aimed at any of the four lattice directions in at most three steps.

* `Dir2.exists_turnLeft_iterate_lt_four` — every direction is reached in `< 4` left turns.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

/-- **Every direction is reached in fewer than four left turns**: for any `dir δ`, there is `k < 4`
with `turnLeft^[k] dir = δ`. -/
theorem Dir2.exists_turnLeft_iterate_lt_four (dir δ : Dir2) :
    ∃ k : ℕ, k < 4 ∧ (Dir2.turnLeft^[k]) dir = δ := by
  fin_cases dir <;> fin_cases δ <;>
    first
      | exact ⟨0, by norm_num, by decide⟩
      | exact ⟨1, by norm_num, by decide⟩
      | exact ⟨2, by norm_num, by decide⟩
      | exact ⟨3, by norm_num, by decide⟩

end IsingModel
