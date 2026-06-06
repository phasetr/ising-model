import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Pushing a pointwise upper bound through the liminf (FV §3.7.2)

A real sequence `a` bounded above by `1` and satisfying `1 - a n ≤ M` for every `n` has
`1 - liminf a ≤ M`: the lower bound `1 - M ≤ a n` lifts to `1 - M ≤ liminf a` (the upper bound `1`
supplies the coboundedness `Filter.le_liminf_of_le` needs). This is the abstract step taking the
per-stage Peierls bound to the infinite-volume liminf.

* `one_sub_liminf_le` — `1 - liminf a ≤ M`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Filter

/-- **A pointwise bound pushes through the liminf**: if `1 - a n ≤ M` and `a n ≤ 1` for all `n`,
then `1 - liminf a ≤ M`. -/
theorem one_sub_liminf_le {a : ℕ → ℝ} {M : ℝ} (hle : ∀ n, 1 - a n ≤ M) (hub : ∀ n, a n ≤ 1) :
    1 - liminf a atTop ≤ M := by
  have hge : ∀ n, 1 - M ≤ a n := fun n => by linarith [hle n]
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop a :=
    isCoboundedUnder_ge_of_eventually_le (x := 1) atTop (Eventually.of_forall hub)
  have hliminf_ge : 1 - M ≤ liminf a atTop :=
    le_liminf_of_le hcobdd (Eventually.of_forall hge)
  linarith

end IsingModel
