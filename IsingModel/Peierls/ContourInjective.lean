import IsingModel.Peierls.BoxBridge
import IsingModel.Peierls.LiftBoxCutInjective
import IsingModel.Peierls.DualCutInBoxInjective

/-!
# Contour injectivity: a droplet is determined by its dual cut (FV §3.7.2)

Assembling the three links — `dualCutInBox =⟹ dartPrimalCut =` (`DualCutInBoxInjective`),
`dartPrimalCut = liftBoxCut` under neighbour-closure (`BoxBridge`), and `liftBoxCut` injectivity
via the parity argument (`LiftBoxCutInjective`) — a neighbour-closed, ground-avoiding box droplet in
a preconnected box graph is uniquely determined by its common-box dual cut. This is the injectivity
input of the contour count capstone.

* `box_droplet_eq_of_dartPrimalCut_eq` — equal ambient primal cuts give equal box droplets.
* `box_droplet_eq_of_dualCutInBox_eq` — equal common-box dual cuts give equal box droplets.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ Λd : Finset (Fin 2 → ℤ)} {F₁ F₂ : Finset ↑Λ}

/-- A box region is **neighbour-closed** when every lattice neighbour of one of its vertices is
itself a box vertex. -/
def NeighbourClosed (Λ : Finset (Fin 2 → ℤ)) (F : Finset ↑Λ) : Prop :=
  ∀ a : ↑Λ, a ∈ F → ∀ b : Fin 2 → ℤ, (latticeGraph 2).Adj (↑a) b → b ∈ Λ

/-- **Equal ambient primal cuts give equal box droplets** (neighbour-closed, ground-avoiding,
preconnected box). -/
theorem box_droplet_eq_of_dartPrimalCut_eq
    (hconn : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected) {g : ↑Λ}
    (hcl₁ : NeighbourClosed Λ F₁) (hcl₂ : NeighbourClosed Λ F₂)
    (hg₁ : g ∉ F₁) (hg₂ : g ∉ F₂)
    (h : dartPrimalCut (F₁.image Subtype.val) = dartPrimalCut (F₂.image Subtype.val)) :
    F₁ = F₂ := by
  have hlift : liftBoxCut Λ F₁ = liftBoxCut Λ F₂ := by
    rw [← dartPrimalCut_image_val_eq_liftBoxCut hcl₁,
      ← dartPrimalCut_image_val_eq_liftBoxCut hcl₂, h]
  exact liftBoxCut_injOn hconn g hg₁ hg₂ hlift

/-- **Equal common-box dual cuts give equal box droplets**: the full contour injectivity. -/
theorem box_droplet_eq_of_dualCutInBox_eq
    (hconn : (Ambient.inducedGraph (latticeGraph 2) Λ).Preconnected) {g : ↑Λ}
    (hcl₁ : NeighbourClosed Λ F₁) (hcl₂ : NeighbourClosed Λ F₂)
    (hg₁ : g ∉ F₁) (hg₂ : g ∉ F₂)
    {hsub₁ : dualSupport (F₁.image Subtype.val) ⊆ Λd}
    {hsub₂ : dualSupport (F₂.image Subtype.val) ⊆ Λd}
    (h : dualCutInBox hsub₁ = dualCutInBox hsub₂) :
    F₁ = F₂ :=
  box_droplet_eq_of_dartPrimalCut_eq hconn hcl₁ hcl₂ hg₁ hg₂
    (dartPrimalCut_eq_of_dualCutInBox_eq h)

end IsingModel
