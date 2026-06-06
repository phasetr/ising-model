import IsingModel.Peierls.DualCutInBox
import IsingModel.Peierls.DartPrimalCut

/-!
# Common-box dual cut determines the primal cut (FV §3.7.2)

The common-box dual cut `dualCutInBox` carries all the information of the ambient dual cut: mapping
it back down by `Sym2.map Subtype.val` recovers `dartDualCut F`. Hence equal common-box dual cuts
(over the same box) force equal ambient dual cuts, and therefore equal primal cuts
(`dartPrimalCut_eq_of_dartDualCut_eq`). This is the upper half of the contour injectivity chain.

* `dualCutInBox_image_map_val` — the common-box cut maps down to the ambient dual cut.
* `dartDualCut_eq_of_dualCutInBox_eq`, `dartPrimalCut_eq_of_dualCutInBox_eq`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F F₁ F₂ Λd : Finset (Fin 2 → ℤ)}

/-- **The common-box dual cut maps down to the ambient dual cut** under `Sym2.map Subtype.val`. -/
theorem dualCutInBox_image_map_val (hsub : dualSupport F ⊆ Λd) :
    (dualCutInBox hsub).image (Sym2.map (Subtype.val : ↑Λd → (Fin 2 → ℤ))) = dartDualCut F := by
  classical
  rw [dualCutInBox, Finset.image_image]
  have hcomp : (Sym2.map (Subtype.val : ↑Λd → (Fin 2 → ℤ))) ∘ (Sym2.map (supportIncl hsub))
      = Sym2.map (Subtype.val : ↑(dualSupport F) → (Fin 2 → ℤ)) := by
    funext x
    rw [Function.comp_apply, Sym2.map_map]
    rfl
  rw [hcomp]
  exact dualCutSub_image_map_val

/-- **Equal common-box dual cuts force equal ambient dual cuts**. -/
theorem dartDualCut_eq_of_dualCutInBox_eq {hsub₁ : dualSupport F₁ ⊆ Λd}
    {hsub₂ : dualSupport F₂ ⊆ Λd} (h : dualCutInBox hsub₁ = dualCutInBox hsub₂) :
    dartDualCut F₁ = dartDualCut F₂ := by
  rw [← dualCutInBox_image_map_val hsub₁, ← dualCutInBox_image_map_val hsub₂, h]

/-- **Equal common-box dual cuts force equal primal cuts**. -/
theorem dartPrimalCut_eq_of_dualCutInBox_eq {hsub₁ : dualSupport F₁ ⊆ Λd}
    {hsub₂ : dualSupport F₂ ⊆ Λd} (h : dualCutInBox hsub₁ = dualCutInBox hsub₂) :
    dartPrimalCut F₁ = dartPrimalCut F₂ :=
  dartPrimalCut_eq_of_dartDualCut_eq (dartDualCut_eq_of_dualCutInBox_eq h)

end IsingModel
