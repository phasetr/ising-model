import IsingModel.Peierls.RayAnchorDart
import IsingModel.Peierls.DualCutInBox

/-!
# The ray-exit anchor in the common box (FV §3.7.2)

Lifting the ambient ray anchor to the count-ready common-box dual cut: for a finite
box-droplet `F ∋ i`, some edge of `dualCutInBox` contains the subtype anchor vertex
`⟨ray0 i k, _⟩`. The anchor vertex automatically lies in the box, since it is the head
of a boundary dart, hence in
`dualSupport F ⊆ Λd`.

* `exists_e0_exit_anchor_dart_head` — the `+e₀` exit dart has head exactly the exit point.
* `exists_ray_anchor_dualCutInBox` — the common-box dual cut passes through a ray anchor vertex.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The `+e₀` exit dart has head equal to the exit point**. -/
theorem exists_e0_exit_anchor_dart_head {F : Finset (Fin 2 → ℤ)} {a : Fin 2 → ℤ}
    (ha : a ∈ F) (hb : a + unitVec2 0 ∉ F) :
    ∃ d : BoundaryDart F, d.head = a := by
  exact ⟨e0ExitAnchorDart ha hb, e0ExitAnchorDart_head ha hb⟩

/-- **The common-box dual cut passes through a ray anchor**: for a finite box droplet `F ∋ i` with
`dualSupport F ⊆ Λd`, there is a step count `k`, with `ray0 i k ∈ Λd`, and an edge of
`dualCutInBox` containing the subtype anchor vertex `⟨ray0 i k, _⟩`. -/
theorem exists_ray_anchor_dualCutInBox {Λd F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    (hi : i ∈ F) (hsub : dualSupport F ⊆ Λd) :
    ∃ k, ∃ hz : ray0 i k ∈ Λd, ∃ e ∈ dualCutInBox hsub,
      (⟨ray0 i k, hz⟩ : ↑Λd) ∈ e := by
  classical
  obtain ⟨k, hk1, hk2⟩ := exists_first_exit hi
  rw [ray0_succ] at hk2
  obtain ⟨d, hdhead⟩ := exists_e0_exit_anchor_dart_head hk1 hk2
  have hheadΛ : d.head ∈ Λd := hsub (head_mem_dualSupport d)
  have hz : ray0 i k ∈ Λd := hdhead ▸ hheadΛ
  refine ⟨k, hz, s(supportIncl hsub (dartTailSub d), supportIncl hsub (dartHeadSub d)), ?_, ?_⟩
  · -- the subtype edge of `d` lies in `dualCutInBox`
    rw [dualCutInBox]
    have h1 : s(dartTailSub d, dartHeadSub d) ∈ dualCutSub F := by
      rw [dualCutSub]; exact Finset.mem_image_of_mem _ (Finset.mem_univ d)
    have h2 := Finset.mem_image_of_mem (Sym2.map (supportIncl hsub)) h1
    rwa [Sym2.map_mk] at h2
  · -- the anchor vertex `⟨ray0 i k, hz⟩` is `supportIncl (dartHeadSub d)`, on the edge
    have hvtx : (⟨ray0 i k, hz⟩ : ↑Λd) = supportIncl hsub (dartHeadSub d) := by
      apply Subtype.ext
      simp only [supportIncl, dartHeadSub, hdhead]
    rw [hvtx]
    exact Sym2.mem_mk_right _ _

end IsingModel
