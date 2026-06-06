import IsingModel.Peierls.RayAnchorBound

/-!
# The ray anchor set (FV §3.7.2)

The fixed set of `r` ray anchors `z_0, …, z_{r-1}` pinning every size-`r` contour. As a `Finset`
over the dual box subtype it has at most `r` elements, and every finite box droplet `F ∋ i` whose
dual cut has size `r` is anchored within it. This supplies the anchor set `Z`, the cover, and
the bound `|Z| ≤ r` of the contour count assembly `contour_count_le`.

* `rayAnchorSet` — the `r` ray anchors in the dual box.
* `rayAnchorSet_card_le`, `mem_rayAnchorSet`, `rayAnchorSet_cover`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λd F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {r : ℕ}

/-- The **ray anchor set**: the dual-box vertices that equal `ray0 i k` for some `k < r`. -/
noncomputable def rayAnchorSet (Λd : Finset (Fin 2 → ℤ)) (i : Fin 2 → ℤ) (r : ℕ) :
    Finset ↑Λd :=
  Λd.attach.filter (fun z => ∃ k, k < r ∧ (z : Fin 2 → ℤ) = ray0 i k)

/-- A ray point `ray0 i k` (`k < r`, in the box) is an anchor. -/
theorem mem_rayAnchorSet {k : ℕ} (hk : k < r) (hz : ray0 i k ∈ Λd) :
    (⟨ray0 i k, hz⟩ : ↑Λd) ∈ rayAnchorSet Λd i r := by
  rw [rayAnchorSet, Finset.mem_filter]
  exact ⟨Finset.mem_attach _ _, k, hk, rfl⟩

/-- **The anchor set has at most `r` elements**. -/
theorem rayAnchorSet_card_le : (rayAnchorSet Λd i r).card ≤ r := by
  classical
  calc (rayAnchorSet Λd i r).card
      = ((rayAnchorSet Λd i r).image (Subtype.val)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((Finset.range r).image (ray0 i)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_image] at hx ⊢
        obtain ⟨z, hzS, rfl⟩ := hx
        rw [rayAnchorSet, Finset.mem_filter] at hzS
        obtain ⟨k, hk, hval⟩ := hzS.2
        exact ⟨k, Finset.mem_range.mpr hk, hval.symm⟩
    _ ≤ (Finset.range r).card := Finset.card_image_le
    _ = r := Finset.card_range r

/-- **Every size-`r` droplet is anchored in the ray anchor set**. -/
theorem rayAnchorSet_cover (hi : i ∈ F) (hsub : dualSupport F ⊆ Λd)
    (hr : (dualCutInBox hsub).card = r) :
    ∃ z ∈ rayAnchorSet Λd i r, ∃ e ∈ dualCutInBox hsub, z ∈ e := by
  obtain ⟨k, hk, hz, e, he, hze⟩ := exists_ray_anchor_lt_card hi hsub
  rw [hr] at hk
  exact ⟨⟨ray0 i k, hz⟩, mem_rayAnchorSet hk hz, e, he, hze⟩

end IsingModel
