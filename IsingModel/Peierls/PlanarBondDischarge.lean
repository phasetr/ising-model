import IsingModel.Peierls.FixedRayRegion
import IsingModel.Peierls.DartDualComponentBoxIncidentEven
import IsingModel.Peierls.DualComponentSeparatesOfStokes
import IsingModel.Peierls.PlanarBondAssembly
import IsingModel.Peierls.CutCrossingParity

/-!
# Discharge of the planar bond hypothesis (FV §3.7.2)

This file closes the homological/parity programme: it proves the discrete-Jordan separation
`dual_component_separates_primal` unconditionally, and hence `PlanarBondHypothesis F` for every `F`.

The chain assembles the campaign: the box-primal image `B` of a dart's dual component is even at
every dual vertex (`dartDualComponentBoxPrimalEdges_dualIncident_even`); the fixed-ray region then
realises `B` as a cut (`cutEdges_fixedRayRegion_eq_of_square_even`); so every closed walk crosses
`B` an even number of times (`even_cutCrossings_iff`); the separation core
(`dual_component_separates_primal_of_even_closed_walk`) places `d`'s two sides on opposite sides of
the region; and the assembly `planarBondHypothesis_of_separates` discharges the bond hypothesis.

* `dual_component_separates_primal` — the discrete-Jordan separation, unconditionally.
* `planarBondHypothesis` — `PlanarBondHypothesis F` for every `F`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {F : Finset (Fin 2 → ℤ)}

/-- **The discrete-Jordan separation** (unconditional): `d.right` lies outside the region
`edgeSideComponentDart` built from `d`'s dual component. The dual component's box-primal image `B`
is even at every dual vertex, so the fixed-ray region realises it as a cut, every closed walk
crosses `B` evenly, and the separation core concludes. -/
theorem dual_component_separates_primal {Λ : Finset (Fin 2 → ℤ)} (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) :
    (⟨d.right, hRΛ d⟩ : (↑Λ : Type _)) ∉ edgeSideComponentDart hFΛ hRΛ d := by
  classical
  have hBedge : dartDualComponentBoxPrimalEdges hFΛ hRΛ d ⊆
      (Ambient.inducedGraph (latticeGraph 2) Λ).edgeFinset :=
    (dartDualComponentBoxPrimalEdges_subset_cutEdges_lift hFΛ hRΛ d).trans
      (Finset.filter_subset _ _)
  have hSquare := image_val_square_even_of_box_dualIncident_even hBedge
    (dartDualComponentBoxPrimalEdges_dualIncident_even hFΛ hRΛ d)
  have hcut := cutEdges_fixedRayRegion_eq_of_square_even
    (dartDualComponentBoxPrimalEdges hFΛ hRΛ d) hBedge hSquare
  refine dual_component_separates_primal_of_even_closed_walk hFΛ hRΛ d (fun w => ?_)
  have h := (even_cutCrossings_iff (Ambient.inducedGraph (latticeGraph 2) Λ)
    (fixedRayRegion Λ (dartDualComponentBoxPrimalEdges hFΛ hRΛ d)) w).mpr Iff.rfl
  unfold cutCrossings at h
  rwa [hcut] at h

/-- **The planar bond hypothesis holds for every region `F`** (unconditional). This discharges the
single open obligation isolated in `PlanarBondReduction.lean`, completing the FV §3.7.2 reduction
of the low-temperature Peierls contour count to a now-proved discrete-Jordan input. -/
theorem planarBondHypothesis (F : Finset (Fin 2 → ℤ)) : PlanarBondHypothesis F :=
  planarBondHypothesis_of_separates fun hFΛ hRΛ d => dual_component_separates_primal hFΛ hRΛ d

end IsingModel
