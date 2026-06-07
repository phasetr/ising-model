import IsingModel.Peierls.DartOfCut

/-!
# A crossed edge carries a boundary dart (FV §3.7.2)

`edgeCrosses F s(a,b)` holds exactly when one of `a, b` lies in `F` and the other does not. Either
way the adjacent pair is a genuine cut edge, so it is the primal cut edge of some boundary dart
(`exists_dart_of_edgeCrosses`), orienting it with `F` on the left. This packages
`exists_dart_of_cut`
in the symmetric `edgeCrosses` form, the bridge from the contour's cut sides (counted by
`squareSplitCount`) to the boundary darts whose orbits the single-orbit argument tracks.

* `exists_dart_of_edgeCrosses` — a crossed lattice edge is the cut edge of a boundary dart.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **A crossed edge carries a boundary dart**: if `a, b` are adjacent and `edgeCrosses F s(a,b)`,
then some boundary dart of `F` has primal cut edge `s(a,b)`. -/
theorem exists_dart_of_edgeCrosses (F : Finset (Fin 2 → ℤ)) {a b : Fin 2 → ℤ}
    (hadj : (latticeGraph 2).Adj a b) (hcross : edgeCrosses F s(a, b) = true) :
    ∃ d : BoundaryDart F, primalCutEdge d.tail d.dir = s(a, b) := by
  rw [edgeCrosses, Sym2.lift_mk] at hcross
  by_cases ha : a ∈ F
  · by_cases hb : b ∈ F
    · simp [ha, hb] at hcross
    · exact exists_dart_of_cut hadj ha hb
  · by_cases hb : b ∈ F
    · obtain ⟨d, hd⟩ := exists_dart_of_cut hadj.symm hb ha
      exact ⟨d, by rw [hd]; exact Sym2.eq_swap⟩
    · simp [ha, hb] at hcross

end IsingModel
