import IsingModel.Peierls.DartBijection
import IsingModel.Peierls.DartFinite

/-!
# `nextDart` is a bijection (FV §3.7.2)

`nextDart` is surjective on the finite type `BoundaryDart F`: every dart `e` is the successor of a
predecessor dart, constructed by the reverse priority. By the three cases of
`validAt_prev_candidates_iff`, the predecessor's forward step (via the `nextDart_eq_*` reductions)
returns exactly `e`. A surjective endofunction of a finite type is bijective, so `nextDart` is a
permutation of the darts — every dart lies on a closed orbit, the contour cycle.

* `nextDart_surjective` — every dart has a predecessor under `nextDart`.
* `nextDart_bijective` — `nextDart` is a bijection on `BoundaryDart F`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **`nextDart` is surjective**: every dart `e` is the `nextDart` of its predecessor, built by
the reverse priority. -/
theorem nextDart_surjective : Function.Surjective (BoundaryDart.nextDart (F := F)) := by
  intro e
  obtain ⟨hR, hS, hL⟩ := validAt_prev_candidates_iff e
  have hLeftInv : ¬ ValidAt F e.tail e.dir.turnLeft := by
    rintro ⟨_, hr⟩; rw [rightSite_turnLeft] at hr; exact hr e.left_mem
  by_cases h₁ : leftSite e.tail e.dir.turnLeft ∈ F
  · by_cases h₂ : leftSite e.tail e.dir.turnLeft.turnLeft ∈ F
    · -- predecessor turns left; its forward step takes the right turn back to `e`
      have pf := hL.mpr h₂
      refine ⟨⟨e.tail - e.dir.turnLeft.vec, e.dir.turnLeft, pf.1, pf.2⟩, ?_⟩
      have hhd : (⟨e.tail - e.dir.turnLeft.vec, e.dir.turnLeft, pf.1, pf.2⟩ :
          BoundaryDart F).head = e.tail := by
        change e.tail - e.dir.turnLeft.vec + e.dir.turnLeft.vec = e.tail; abel
      have hc1 : ¬ ValidAt F (⟨e.tail - e.dir.turnLeft.vec, e.dir.turnLeft, pf.1, pf.2⟩ :
          BoundaryDart F).head (e.dir.turnLeft).turnLeft := by
        rw [hhd]; rintro ⟨_, hr⟩; rw [rightSite_turnLeft] at hr; exact hr h₁
      have hc2 : ¬ ValidAt F (⟨e.tail - e.dir.turnLeft.vec, e.dir.turnLeft, pf.1, pf.2⟩ :
          BoundaryDart F).head e.dir.turnLeft := by rw [hhd]; exact hLeftInv
      rw [nextDart_eq_turnRight _ hc1 hc2]
      exact BoundaryDart.ext' hhd (by simp [Dir2.turnLeft_turnRight])
    · -- predecessor goes straight; its forward step goes straight back to `e`
      have pf := hS.mpr ⟨h₁, h₂⟩
      refine ⟨⟨e.tail - e.dir.vec, e.dir, pf.1, pf.2⟩, ?_⟩
      have hhd : (⟨e.tail - e.dir.vec, e.dir, pf.1, pf.2⟩ : BoundaryDart F).head = e.tail := by
        change e.tail - e.dir.vec + e.dir.vec = e.tail; abel
      have hc1 : ¬ ValidAt F (⟨e.tail - e.dir.vec, e.dir, pf.1, pf.2⟩ :
          BoundaryDart F).head e.dir.turnLeft := by rw [hhd]; exact hLeftInv
      have hc2 : ValidAt F (⟨e.tail - e.dir.vec, e.dir, pf.1, pf.2⟩ :
          BoundaryDart F).head e.dir := by
        rw [hhd]; exact ⟨e.left_mem, e.right_not_mem⟩
      rw [nextDart_eq_straight _ hc1 hc2]
      exact BoundaryDart.ext' hhd rfl
  · -- predecessor turns right; its forward step takes the left turn back to `e`
    have pf := hR.mpr h₁
    refine ⟨⟨e.tail - e.dir.turnRight.vec, e.dir.turnRight, pf.1, pf.2⟩, ?_⟩
    have hhd : (⟨e.tail - e.dir.turnRight.vec, e.dir.turnRight, pf.1, pf.2⟩ :
        BoundaryDart F).head = e.tail := by
      change e.tail - e.dir.turnRight.vec + e.dir.turnRight.vec = e.tail; abel
    have hc1 : ValidAt F (⟨e.tail - e.dir.turnRight.vec, e.dir.turnRight, pf.1, pf.2⟩ :
        BoundaryDart F).head (e.dir.turnRight).turnLeft := by
      rw [hhd, Dir2.turnRight_turnLeft]; exact ⟨e.left_mem, e.right_not_mem⟩
    rw [nextDart_eq_turnLeft _ hc1]
    exact BoundaryDart.ext' hhd (by simp [Dir2.turnRight_turnLeft])

/-- **`nextDart` is a bijection** on the finite type of boundary darts (surjective endofunction of
a finite type). Hence the dart orbits are pure cycles — the contour traversal closes up. -/
theorem nextDart_bijective : Function.Bijective (BoundaryDart.nextDart (F := F)) :=
  haveI : Finite (BoundaryDart F) := Finite.of_fintype _
  ⟨Finite.injective_iff_surjective.mpr nextDart_surjective, nextDart_surjective⟩

end IsingModel
