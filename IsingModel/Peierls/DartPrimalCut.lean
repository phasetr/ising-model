import IsingModel.Peierls.DualToPrimal
import IsingModel.Peierls.DualCutConnected

/-!
# The dual cut determines the primal cut (FV §3.7.2)

Each boundary dart crosses one primal cut edge; the **primal cut** `dartPrimalCut F` collects them.
Because the primal cut edge depends only on the dual edge
(`primalCutEdge_congr_of_dualEdge_eq`), two regions with the same dual cut have the same primal
cut. This is the middle link of the contour injectivity chain
`dartDualCut = ⟹ dartPrimalCut = ⟹ cutEdges = ⟹ F =`.

* `dartPrimalCut` — the primal cut as a finset.
* `dartPrimalCut_eq_of_dartDualCut_eq` — equal dual cuts give equal primal cuts.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F₁ F₂ : Finset (Fin 2 → ℤ)}

/-- The **primal cut** of `F`: every boundary dart's primal cut edge. -/
noncomputable def dartPrimalCut (F : Finset (Fin 2 → ℤ)) : Finset (Sym2 (Fin 2 → ℤ)) :=
  (Finset.univ : Finset (BoundaryDart F)).image (fun d => primalCutEdge d.tail d.dir)

/-- **One inclusion**: a dual-cut inclusion induces a primal-cut inclusion. -/
theorem dartPrimalCut_subset_of_dartDualCut_subset (h : dartDualCut F₁ ⊆ dartDualCut F₂) :
    dartPrimalCut F₁ ⊆ dartPrimalCut F₂ := by
  classical
  intro p hp
  rw [dartPrimalCut, Finset.mem_image] at hp
  obtain ⟨d₁, _, rfl⟩ := hp
  have hmem : s(d₁.tail, d₁.head) ∈ dartDualCut F₂ := by
    apply h
    rw [dartDualCut]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ d₁)
  rw [dartDualCut, Finset.mem_image] at hmem
  obtain ⟨d₂, _, hd₂⟩ := hmem
  rw [dartPrimalCut, Finset.mem_image]
  exact ⟨d₂, Finset.mem_univ d₂, primalCutEdge_congr_of_dualEdge_eq hd₂⟩

/-- **The dual cut determines the primal cut**: regions with equal dual cuts have equal primal
cuts. -/
theorem dartPrimalCut_eq_of_dartDualCut_eq (h : dartDualCut F₁ = dartDualCut F₂) :
    dartPrimalCut F₁ = dartPrimalCut F₂ :=
  Finset.Subset.antisymm
    (dartPrimalCut_subset_of_dartDualCut_subset h.subset)
    (dartPrimalCut_subset_of_dartDualCut_subset h.symm.subset)

end IsingModel
