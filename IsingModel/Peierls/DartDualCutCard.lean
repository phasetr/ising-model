import IsingModel.Peierls.DualCutConnected
import IsingModel.Peierls.DartBijection

/-!
# Cardinality of the dual cut (FV §3.7.2)

The dual-edge map `d ↦ s(d.tail, d.head)` is injective on the boundary darts of `F`: each dual
edge is crossed by exactly one valid dart, because the reverse orientation would put the region
`F` on the right rather than the left. Hence the dual cut has the same cardinality as the dart
type `BoundaryDart F` — the size `r` fed into the volume-independent contour count.

* `Dir2.vec_injective`, `Dir2.vec_add_two`, `leftSite_reverse` — direction/site geometry.
* `dartDualEdge_injective` — the dual-edge map is injective.
* `dartDualCut_card` — `|dartDualCut F| = |BoundaryDart F|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The direction vector is injective**. -/
theorem Dir2.vec_injective : Function.Injective Dir2.vec := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | (exfalso
         have h0 := congrFun h 0
         have h1 := congrFun h 1
         simp [Dir2.vec, unitVec2, Pi.neg_apply, Matrix.cons_val] at h0 h1)

/-- **The opposite direction negates the vector**: `(δ + 2).vec = -δ.vec`. -/
theorem Dir2.vec_add_two (δ : Dir2) : (δ + 2).vec = -δ.vec := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [Dir2.vec, unitVec2, Pi.neg_apply, Matrix.cons_val])

/-- **Reverse left site**: the left site of the opposite dart along the same edge is the original
right site. -/
theorem leftSite_reverse (t : Fin 2 → ℤ) (δ : Dir2) :
    leftSite (t + δ.vec) (δ + 2) = rightSite t δ := by
  fin_cases δ <;>
    (funext i; fin_cases i <;>
      simp [leftSite, rightSite, Dir2.vec, Dir2.turnLeft, unitVec2, Pi.neg_apply,
        Pi.add_apply, Pi.sub_apply, Matrix.cons_val])

/-- **The dual-edge map is injective on boundary darts**: each dual edge is crossed by a unique
valid dart (the reverse orientation would put `F` on the right). -/
theorem dartDualEdge_injective :
    Function.Injective (fun d : BoundaryDart F => s(d.tail, d.head)) := by
  intro d e h
  simp only at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- same orientation: equal tails and heads force equal directions
    have hvec : d.dir.vec = e.dir.vec := by
      have hd : d.head = d.tail + d.dir.vec := rfl
      have he : e.head = e.tail + e.dir.vec := rfl
      rw [hd, he, h1] at h2
      exact add_left_cancel h2
    exact BoundaryDart.ext' h1 (Dir2.vec_injective hvec)
  · -- reverse orientation: `F` would lie on both sides, contradiction
    exfalso
    have hvec : d.dir.vec = -e.dir.vec := by
      have hd : d.head = d.tail + d.dir.vec := rfl
      have he : e.head = e.tail + e.dir.vec := rfl
      rw [hd, h1, he] at h2
      funext i
      have hi := congrFun h2 i
      simp only [Pi.add_apply, Pi.neg_apply] at hi ⊢
      omega
    have hdir : d.dir = e.dir + 2 := Dir2.vec_injective (by rw [hvec, Dir2.vec_add_two])
    have hkey : leftSite d.tail d.dir = rightSite e.tail e.dir := by
      rw [show d.tail = e.tail + e.dir.vec from h1, hdir]
      exact leftSite_reverse e.tail e.dir
    exact e.right_not_mem (hkey ▸ d.left_mem)

/-- **The dual cut has the cardinality of the dart type**. -/
theorem dartDualCut_card : (dartDualCut F).card = (Finset.univ : Finset (BoundaryDart F)).card := by
  classical
  rw [dartDualCut, Finset.card_image_of_injective _ dartDualEdge_injective]

end IsingModel
