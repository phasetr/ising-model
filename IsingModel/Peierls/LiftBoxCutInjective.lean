import IsingModel.Peierls.LiftBoxCut
import IsingModel.Peierls.CutDeterminesRegion

/-!
# The lifted box cut is injective on box regions (FV §3.7.2)

Since `liftBoxCut Λ F = (cutEdges (box) F).image (Sym2.map Subtype.val)` and the subtype lift is
injective, equal lifted cuts force equal box cuts; the parity injectivity
(`eq_of_cutEdges_eq`) then forces equal regions, provided the box graph is preconnected and the
regions avoid a fixed ground vertex. This is the final link of the contour injectivity chain.

* `liftBoxCut_injOn` — `liftBoxCut Λ` is injective on `{F | g ∉ F}`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ : Finset (Fin 2 → ℤ)}

/-- **The lifted box cut is injective on regions avoiding a ground vertex** (in a preconnected box
graph): equal lifted cuts give equal box cuts (`Sym2.map Subtype.val` is injective), which the
parity argument turns into equal regions. -/
theorem liftBoxCut_injOn (hconn : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected)
    (g : ↑Λ) :
    Set.InjOn (liftBoxCut Λ) {F : Finset ↑Λ | g ∉ F} := by
  classical
  intro F₁ hF₁ F₂ hF₂ hlift
  have hcut : cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) F₁
      = cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) F₂ := by
    rw [liftBoxCut, liftBoxCut] at hlift
    exact Finset.image_injective (Sym2.map.injective Subtype.val_injective) hlift
  exact eq_of_cutEdges_eq hconn hF₁ hF₂ hcut

end IsingModel
