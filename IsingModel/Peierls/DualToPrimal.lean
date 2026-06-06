import IsingModel.Peierls.DartDualCutCard

/-!
# The dual edge determines the primal cut edge (FV §3.7.2)

A boundary dart crosses one primal cut edge `primalCutEdge tail dir = s(leftSite, rightSite)`. We
show this primal edge depends only on the dart's *dual* edge `s(tail, head)`, independent of
orientation: the reverse dart swaps left and right sites, but the unordered primal edge is
unchanged (`rightSite_reverse` complements `leftSite_reverse`). Hence the primal cut of a region is
the image of its dual cut under a well-defined map — the bridge from dual-cut equality to primal-cut
equality used in the contour injectivity.

* `rightSite_reverse` — the reverse dart's right site is the original left site.
* `primalCutEdge_congr_of_dualEdge_eq` — equal dual edges give equal primal cut edges.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Reverse right site**: the right site of the opposite dart along the same edge is the original
left site. -/
theorem rightSite_reverse (t : Fin 2 → ℤ) (δ : Dir2) :
    rightSite (t + δ.vec) (δ + 2) = leftSite t δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.neg_apply,
        Pi.add_apply, Pi.sub_apply, Matrix.cons_val])

/-- **The dual edge determines the primal cut edge**: if two darts share a dual edge
`s(tail, head)` (in either orientation) then they cross the same primal cut edge. -/
theorem primalCutEdge_congr_of_dualEdge_eq {t₁ t₂ : Fin 2 → ℤ} {δ₁ δ₂ : Dir2}
    (h : s(t₁, t₁ + δ₁.vec) = s(t₂, t₂ + δ₂.vec)) :
    primalCutEdge t₁ δ₁ = primalCutEdge t₂ δ₂ := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- same orientation: equal tails and heads force equal directions
    have hvec : δ₁.vec = δ₂.vec := by
      rw [h1] at h2
      exact add_left_cancel h2
    rw [h1, Dir2.vec_injective hvec]
  · -- reverse orientation: left and right sites swap, the unordered primal edge is unchanged
    have hvec : δ₁.vec = -δ₂.vec := by
      rw [h1] at h2
      funext i
      have hi := congrFun h2 i
      simp only [Pi.add_apply, Pi.neg_apply] at hi ⊢
      omega
    have hdir : δ₁ = δ₂ + 2 := Dir2.vec_injective (by rw [hvec, Dir2.vec_add_two])
    rw [primalCutEdge, primalCutEdge, h1, hdir, leftSite_reverse, rightSite_reverse, Sym2.eq_swap]

end IsingModel
