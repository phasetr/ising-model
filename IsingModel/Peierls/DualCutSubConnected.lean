import IsingModel.Peierls.DualSupport
import IsingModel.Peierls.DualCutConnected

/-!
# Edge-connectivity of the subtype-lifted dual cut (FV §3.7.2)

The ambient dual cut `dartDualCut F` is edge-connected given a single orbit
(`dartDualCut_isEdgeConnected_of_single_orbit`). Its subtype lift `dualCutSub F` is the same set
viewed over `↑(dualSupport F)`, related by `Sym2.map Subtype.val`. Edge-connectivity transfers
across this injective lift: a shared ambient vertex of two lifted edges automatically lies in the
support box, so it pulls back to a shared subtype vertex.

* `isEdgeConnected_of_image_map_subtype` — the general transfer lemma.
* `dualCutSub_image_map_val` — the lift's image is the ambient dual cut.
* `dualCutSub_isEdgeConnected_of_single_orbit` — the subtype cut is edge-connected given one orbit.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Edge-connectivity transfers from the image of a subtype lift**: if the image of `Y` under
`Sym2.map Subtype.val` is edge-connected, so is `Y`. A shared ambient vertex of two lifted edges
lies in the subtype (it is a coercion), so it pulls back. -/
theorem isEdgeConnected_of_image_map_subtype {V : Type*} [DecidableEq V] {Λ : Finset V}
    {Y : Finset (Sym2 ↑Λ)}
    (himg : IsEdgeConnected (Y.image (Sym2.map (Subtype.val : ↑Λ → V)))) :
    IsEdgeConnected Y := by
  classical
  set g : Sym2 ↑Λ → Sym2 V := Sym2.map (Subtype.val : ↑Λ → V) with hg
  have hginj : Function.Injective g := Sym2.map.injective Subtype.val_injective
  -- lift a reachability chain in the image back to `Y`
  intro e₁ he₁ e₂ he₂
  have hlift : ∀ {x : Sym2 V},
      Relation.ReflTransGen (edgeAdjacentIn (Y.image g)) (g e₁) x →
      ∃ b ∈ Y, x = g b ∧ Relation.ReflTransGen (edgeAdjacentIn Y) e₁ b := by
    intro x hreach
    induction hreach with
    | refl => exact ⟨e₁, he₁, rfl, Relation.ReflTransGen.refl⟩
    | tail _hch hyx ih =>
      obtain ⟨c, hc, hyc, hac⟩ := ih
      obtain ⟨-, hxmem, v, hvm, hvx⟩ := hyx
      rw [Finset.mem_image] at hxmem
      obtain ⟨d, hd, hdx⟩ := hxmem
      refine ⟨d, hd, hdx.symm, hac.tail ?_⟩
      -- build `edgeAdjacentIn Y c d`: the shared ambient vertex pulls back into `↑Λ`
      rw [hyc] at hvm
      rw [← hdx] at hvx
      rw [hg, Sym2.mem_map] at hvm hvx
      obtain ⟨w, hwc, rfl⟩ := hvm
      obtain ⟨w', hw'd, hw'⟩ := hvx
      exact ⟨hc, hd, w, hwc, by rwa [Subtype.val_injective hw'] at hw'd⟩
  have hreach := himg (g e₁) (Finset.mem_image_of_mem g he₁) (g e₂)
    (Finset.mem_image_of_mem g he₂)
  obtain ⟨b, _, hb, hchain⟩ := hlift hreach
  rwa [← hginj hb] at hchain

/-- **The image of the subtype-lifted dual cut is the ambient dual cut**. -/
theorem dualCutSub_image_map_val :
    (dualCutSub F).image (Sym2.map (Subtype.val : ↑(dualSupport F) → (Fin 2 → ℤ))) =
      dartDualCut F := by
  classical
  rw [dualCutSub, dartDualCut, Finset.image_image]
  rfl

/-- **The subtype-lifted dual cut is edge-connected given a single orbit**. -/
theorem dualCutSub_isEdgeConnected_of_single_orbit
    (hone : ∀ d e : BoundaryDart F, d.SameOrbit e) :
    IsEdgeConnected (dualCutSub F) := by
  apply isEdgeConnected_of_image_map_subtype
  rw [dualCutSub_image_map_val]
  exact dartDualCut_isEdgeConnected_of_single_orbit hone

end IsingModel
