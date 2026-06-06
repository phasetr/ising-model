import IsingModel.Peierls.DartPrimalCut
import IsingModel.Peierls.DartCutChar

/-!
# Cardinality of the primal cut (FV §3.7.2)

The primal-cut-edge map `d ↦ primalCutEdge d.tail d.dir` is injective on the boundary darts of `F`:
two darts crossing the same primal edge with the same orientation are equal (the edge plus
orientation determines the dart), and the reverse orientation would put the region `F` on both
sides. Hence `|dartPrimalCut F| = |BoundaryDart F| = |dartDualCut F|` — the primal cut, the dual
cut, and the dart count all have the common size `r`.

* `leftSite_injective_tail` — `leftSite · dir` is injective in the tail.
* `dartPrimalEdge_injective`, `dartPrimalCut_card`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The left site is the tail shifted by a direction-dependent constant. -/
theorem leftSite_eq_tail_add (t : Fin 2 → ℤ) (dir : Dir2) :
    leftSite t dir = t + leftSite 0 dir := by
  fin_cases dir <;>
    (funext j; fin_cases j <;>
      simp [leftSite, unitVec2, Pi.add_apply])

/-- `leftSite · dir` is injective in the tail (for a fixed direction). -/
theorem leftSite_injective_tail (dir : Dir2) : Function.Injective (fun t => leftSite t dir) := by
  intro a b hab
  have h : a + leftSite 0 dir = b + leftSite 0 dir := by
    rw [← leftSite_eq_tail_add, ← leftSite_eq_tail_add]; exact hab
  exact add_right_cancel h

/-- **The primal-cut-edge map is injective on boundary darts**. -/
theorem dartPrimalEdge_injective :
    Function.Injective (fun d : BoundaryDart F => primalCutEdge d.tail d.dir) := by
  intro d e h
  simp only [primalCutEdge] at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- same orientation: the edge with its `F`-side determines the dart
    have hvec : (Dir2.turnLeft d.dir).vec = (Dir2.turnLeft e.dir).vec := by
      have h2' : leftSite d.tail d.dir - (Dir2.turnLeft d.dir).vec
          = leftSite e.tail e.dir - (Dir2.turnLeft e.dir).vec := h2
      rw [h1] at h2'
      funext j
      have hj := congrFun h2' j
      simp only [Pi.sub_apply] at hj ⊢
      omega
    have hdir : d.dir = e.dir := Dir2.turnLeft_injective (Dir2.vec_injective hvec)
    rw [hdir] at h1
    exact BoundaryDart.ext' (leftSite_injective_tail e.dir h1) hdir
  · -- reverse orientation: `leftSite d = rightSite e ∈ F` and `∉ F`
    exact absurd (h1 ▸ d.left_mem) e.right_not_mem

/-- **The primal cut has the cardinality of the dart type**. -/
theorem dartPrimalCut_card :
    (dartPrimalCut F).card = (Finset.univ : Finset (BoundaryDart F)).card := by
  classical
  rw [dartPrimalCut, Finset.card_image_of_injective _ dartPrimalEdge_injective]

end IsingModel
