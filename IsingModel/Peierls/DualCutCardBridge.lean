import IsingModel.Peierls.DualCutInBox
import IsingModel.Peierls.DartPrimalCutCard
import IsingModel.Peierls.ContourInjective

/-!
# The dual-cut size equals the box cut size (FV §3.7.2)

Chaining the cardinality identities, the common-box dual cut of a neighbour-closed box droplet has
the same size as its box edge cut:
`|dualCutInBox| = |BoundaryDart| = |dartPrimalCut| = |liftBoxCut| = |cutEdges (box) S|`.
So the dual-cut size `r` fed into the contour count coincides with the Peierls bound's
`|cutEdges G S|`.

* `dualCutInBox_card_eq_cutEdges` — `|dualCutInBox| = |cutEdges (box) S|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **The common-box dual cut has the box cut size**: for a neighbour-closed box droplet `S`,
`|dualCutInBox| = |cutEdges (box) S|`. -/
theorem dualCutInBox_card_eq_cutEdges {Λ Λd : Finset (Fin 2 → ℤ)} {S : Finset ↑Λ}
    (hcl : NeighbourClosed Λ S) (hsub : dualSupport (S.image Subtype.val) ⊆ Λd) :
    (dualCutInBox hsub).card
      = (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) S).card := by
  rw [dualCutInBox_card, ← dartPrimalCut_card, dartPrimalCut_image_val_eq_liftBoxCut hcl,
    liftBoxCut_card]
  rfl

end IsingModel
