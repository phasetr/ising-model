import IsingModel.Peierls.RayAnchorBox
import IsingModel.Peierls.RayExitBound

/-!
# The bounded ray anchor (FV §3.7.2)

Combining the ray anchor (`exists_ray_anchor_dualCutInBox`) with the first-exit distance bound
(`firstExit_lt_dartDualCut_card`) at a *single* first-exit index `k`: a finite box droplet `F ∋ i`
has an anchor `ray0 i k` on its common-box dual cut with `k < |dualCutInBox|`. This is the input to
the contour count's anchor-cover, pinning each droplet to one of the `r` fixed ray anchors
`z_0, …, z_{r-1}`.

* `exists_ray_anchor_lt_card` — anchor at `ray0 i k` with `k < |dualCutInBox|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The bounded ray anchor**: a finite box droplet `F ∋ i` has an anchor `ray0 i k` on its
common-box dual cut with `k < |dualCutInBox|`. -/
theorem exists_ray_anchor_lt_card {Λd F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ}
    (hi : i ∈ F) (hsub : dualSupport F ⊆ Λd) :
    ∃ k, k < (dualCutInBox hsub).card ∧ ∃ hz : ray0 i k ∈ Λd,
      ∃ e ∈ dualCutInBox hsub, (⟨ray0 i k, hz⟩ : ↑Λd) ∈ e := by
  classical
  obtain ⟨k, hbelow, hk2⟩ := exists_first_exit_below hi
  have hk1 : ray0 i k ∈ F := hbelow k le_rfl
  refine ⟨k, ?_, ?_⟩
  · -- `k < |dartDualCut F| = |dualCutInBox|`
    have hlt := firstExit_lt_dartDualCut_card hbelow
    rwa [dualCutInBox_card, ← dartDualCut_card]
  · -- the anchor at `ray0 i k`, exactly as in `exists_ray_anchor_dualCutInBox`
    rw [ray0_succ] at hk2
    obtain ⟨d, hdhead⟩ := exists_e0_exit_anchor_dart_head hk1 hk2
    have hheadΛ : d.head ∈ Λd := hsub (head_mem_dualSupport d)
    have hz : ray0 i k ∈ Λd := hdhead ▸ hheadΛ
    refine ⟨hz, s(supportIncl hsub (dartTailSub d), supportIncl hsub (dartHeadSub d)), ?_, ?_⟩
    · rw [dualCutInBox]
      have h1 : s(dartTailSub d, dartHeadSub d) ∈ dualCutSub F := by
        rw [dualCutSub]; exact Finset.mem_image_of_mem _ (Finset.mem_univ d)
      have h2 := Finset.mem_image_of_mem (Sym2.map (supportIncl hsub)) h1
      rwa [Sym2.map_mk] at h2
    · have hvtx : (⟨ray0 i k, hz⟩ : ↑Λd) = supportIncl hsub (dartHeadSub d) := by
        apply Subtype.ext
        simp only [supportIncl, dartHeadSub, hdhead]
      rw [hvtx]
      exact Sym2.mem_mk_right _ _

end IsingModel
