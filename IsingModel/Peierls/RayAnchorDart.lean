import IsingModel.Peierls.RayExit
import IsingModel.Peierls.DualCutConnected

/-!
# The ray-exit anchor dart (FV §3.7.2)

At a `+e₀` exit point `a` of `F` (`a ∈ F`, `a + e₀ ∉ F`), the boundary dart with `tail = a - e₁`,
`dir = e₁` crosses the cut edge `{a, a + e₀}` and has *head* exactly `a`; hence its dual edge
`s(a - e₁, a)` contains `a`. Composed with the ray first-exit, this pins the dual cut to the fixed
anchor vertex `ray0 i k`: some dual cut edge passes through `ray0 i k`.

* `exists_e0_exit_anchor_dart` — a `+e₀` exit gives a dart whose dual edge contains the exit point.
* `exists_ray_anchor_dartDualCut` — the dual cut of a finite `F ∋ i` passes through some `ray0 i k`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The `+e₀` exit anchor dart**: at a `+e₀` exit point `a`, some boundary dart of `F` has `a` on
its dual edge `s(tail, head)` (indeed `head = a`). -/
theorem exists_e0_exit_anchor_dart {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    ∃ d : BoundaryDart F, a ∈ s(d.tail, d.head) := by
  have hL : leftSite (a - unitVec2 1) 1 = a := by
    funext j; fin_cases j <;> simp [leftSite, unitVec2, Pi.sub_apply]
  have hR : rightSite (a - unitVec2 1) 1 = a + unitVec2 0 := by
    funext j; fin_cases j <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2,
      Pi.add_apply, Pi.sub_apply]
  refine ⟨⟨a - unitVec2 1, 1, by rw [hL]; exact ha, by rw [hR]; exact hb⟩, ?_⟩
  have hhead : (BoundaryDart.head ⟨a - unitVec2 1, 1, by rw [hL]; exact ha,
      by rw [hR]; exact hb⟩ : Fin 2 → ℤ) = a := by
    change (a - unitVec2 1) + Dir2.vec 1 = a
    funext j; fin_cases j <;> simp [Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply]
  rw [hhead]
  exact Sym2.mem_mk_right _ _

/-- **The dual cut passes through a ray anchor**: for a finite `F` containing `i`, some dual cut
edge contains a ray point `ray0 i k`. -/
theorem exists_ray_anchor_dartDualCut {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} (hi : i ∈ F) :
    ∃ k, ∃ e ∈ dartDualCut F, ray0 i k ∈ e := by
  classical
  obtain ⟨k, hk1, hk2⟩ := exists_first_exit hi
  rw [ray0_succ] at hk2
  obtain ⟨d, hd⟩ := exists_e0_exit_anchor_dart hk1 hk2
  refine ⟨k, s(d.tail, d.head), ?_, hd⟩
  rw [dartDualCut]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

end IsingModel
