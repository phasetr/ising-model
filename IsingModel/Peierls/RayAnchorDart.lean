import IsingModel.Peierls.RayExit
import IsingModel.Peierls.DualCutConnected

/-!
# The ray-exit anchor dart (FV §3.7.2)

At a `+e₀` exit point `a` of `F` (`a ∈ F`, `a + e₀ ∉ F`), the boundary dart with
`tail = a - e₁`,
`dir = e₁` crosses the cut edge `{a, a + e₀}` and has *head* exactly `a`; hence its dual edge
`s(a - e₁, a)` contains `a`. Composed with the ray first-exit, this pins the dual cut to the fixed
anchor vertex `ray0 i k`: some dual cut edge passes through `ray0 i k`.

* `e0ExitAnchorDart` — the concrete dart at a `+e₀` exit.
* `exists_e0_exit_anchor_dart` — a `+e₀` exit gives a dart whose dual edge contains the
  exit point.
* `exists_ray_anchor_dartDualCut` — the dual cut of a finite `F ∋ i` passes through some
  `ray0 i k`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The concrete `+e₀` exit anchor dart**: at a `+e₀` exit point `a`, take the
dual dart with `tail = a - e₁` and `dir = e₁`. -/
def e0ExitAnchorDart {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) : BoundaryDart F :=
  have hL : leftSite (a - unitVec2 1) 1 = a := by
    funext j; fin_cases j <;> simp [leftSite, unitVec2, Pi.sub_apply]
  have hR : rightSite (a - unitVec2 1) 1 = a + unitVec2 0 := by
    funext j; fin_cases j <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2,
      Pi.add_apply, Pi.sub_apply]
  ⟨a - unitVec2 1, 1, by rw [hL]; exact ha, by rw [hR]; exact hb⟩

/-- **The concrete `+e₀` exit dart starts at `a - e₁`**. -/
@[simp] theorem e0ExitAnchorDart_tail {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    (e0ExitAnchorDart ha hb).tail = a - unitVec2 1 :=
  rfl

/-- **The concrete `+e₀` exit dart points in direction `e₁`**. -/
@[simp] theorem e0ExitAnchorDart_dir {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    (e0ExitAnchorDart ha hb).dir = 1 :=
  rfl

/-- **The concrete `+e₀` exit dart has head equal to the exit point**. -/
@[simp] theorem e0ExitAnchorDart_head {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    (e0ExitAnchorDart ha hb).head = a := by
  change (a - unitVec2 1) + Dir2.vec 1 = a
  funext j; fin_cases j <;> simp [Dir2.vec, unitVec2, Pi.add_apply, Pi.sub_apply]

/-- **The concrete `+e₀` exit dart's dual edge contains the exit point**. -/
theorem e0ExitAnchorDart_anchor_mem {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    a ∈ s((e0ExitAnchorDart ha hb).tail, (e0ExitAnchorDart ha hb).head) := by
  rw [e0ExitAnchorDart_head]
  exact Sym2.mem_mk_right _ _

/-- **The `+e₀` exit anchor dart**: at a `+e₀` exit point `a`, some boundary dart of
`F` has `a` on its dual edge `s(tail, head)` (indeed `head = a`). -/
theorem exists_e0_exit_anchor_dart {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    ∃ d : BoundaryDart F, a ∈ s(d.tail, d.head) := by
  exact ⟨e0ExitAnchorDart ha hb, e0ExitAnchorDart_anchor_mem ha hb⟩

/-- **The dual cut passes through a ray anchor**: for a finite `F` containing `i`, some dual cut
edge contains a ray point `ray0 i k`. -/
theorem exists_ray_anchor_dartDualCut {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    (hi : i ∈ F) :
    ∃ k, ∃ e ∈ dartDualCut F, ray0 i k ∈ e := by
  classical
  obtain ⟨k, hk1, hk2⟩ := exists_first_exit hi
  rw [ray0_succ] at hk2
  obtain ⟨d, hd⟩ := exists_e0_exit_anchor_dart hk1 hk2
  refine ⟨k, s(d.tail, d.head), ?_, hd⟩
  rw [dartDualCut]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ d)

end IsingModel
