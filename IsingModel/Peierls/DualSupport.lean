import IsingModel.Peierls.DartDualCutCard
import IsingModel.Peierls.DartOrbit
import IsingModel.AmbientLattice.Defs.Core

/-!
# The dual-cut support box and its subtype lift (FV §3.7.2)

To feed the dual cut into the volume-independent contour count
(`card_connected_edge_sets_inducedLatticeGraph_le`, which lives over a finite **subtype** `↑Λ`),
we restrict the ambient dual cut `dartDualCut F ⊆ Sym2 (Fin 2 → ℤ)` to the finite **support box**
`dualSupport F` collecting every dart's tail and head. The lifted cut `dualCutSub F` then sits
inside the induced lattice graph's edge finset and keeps the dart cardinality.

* `dualSupport` — the finite face support of the dual cut.
* `dualCutSub` — the dual cut lifted to `Sym2 ↑(dualSupport F)`.
* `dualCutSub_subset_edgeFinset` — it lies in the induced lattice graph.
* `dualCutSub_card` — `|dualCutSub F| = |BoundaryDart F|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The **dual-cut support box**: every boundary dart's tail and head. -/
noncomputable def dualSupport (F : Finset (Fin 2 → ℤ)) : Finset (Fin 2 → ℤ) :=
  (Finset.univ.image (fun d : BoundaryDart F => d.tail)) ∪
    (Finset.univ.image (fun d : BoundaryDart F => d.head))

/-- A dart's tail lies in the support box. -/
theorem tail_mem_dualSupport (d : BoundaryDart F) : d.tail ∈ dualSupport F := by
  rw [dualSupport]
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ d))

/-- A dart's head lies in the support box. -/
theorem head_mem_dualSupport (d : BoundaryDart F) : d.head ∈ dualSupport F := by
  rw [dualSupport]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ d))

/-- The tail of a dart as an element of the support subtype. -/
noncomputable def dartTailSub (d : BoundaryDart F) : ↑(dualSupport F) :=
  ⟨d.tail, tail_mem_dualSupport d⟩

/-- The head of a dart as an element of the support subtype. -/
noncomputable def dartHeadSub (d : BoundaryDart F) : ↑(dualSupport F) :=
  ⟨d.head, head_mem_dualSupport d⟩

/-- The **dual cut lifted to the support subtype**: every dart's dual edge as a `Sym2` over
`↑(dualSupport F)`. -/
noncomputable def dualCutSub (F : Finset (Fin 2 → ℤ)) : Finset (Sym2 ↑(dualSupport F)) :=
  (Finset.univ : Finset (BoundaryDart F)).image (fun d => s(dartTailSub d, dartHeadSub d))

/-- **The lifted dual cut lies in the induced lattice graph's edge finset**. -/
theorem dualCutSub_subset_edgeFinset :
    dualCutSub F ⊆ (Ambient.inducedGraph (latticeGraph 2) (dualSupport F)).edgeFinset := by
  classical
  intro e he
  rw [dualCutSub, Finset.mem_image] at he
  obtain ⟨d, _, rfl⟩ := he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Ambient.inducedGraph_apply]
  exact SimpleGraph.induce_adj.mpr d.tail_adj_head

/-- **The subtype-lifted dual-edge map is injective**. -/
theorem dartDualEdgeSub_injective :
    Function.Injective (fun d : BoundaryDart F => s(dartTailSub d, dartHeadSub d)) := by
  have hcomp : (fun d : BoundaryDart F => s(d.tail, d.head)) =
      (Sym2.map Subtype.val) ∘ (fun d => s(dartTailSub d, dartHeadSub d)) := by
    funext d
    simp [dartTailSub, dartHeadSub, Function.comp]
  exact Function.Injective.of_comp (hcomp ▸ dartDualEdge_injective)

/-- **The lifted dual cut keeps the dart cardinality**. -/
theorem dualCutSub_card :
    (dualCutSub F).card = (Finset.univ : Finset (BoundaryDart F)).card := by
  classical
  rw [dualCutSub, Finset.card_image_of_injective _ dartDualEdgeSub_injective]

end IsingModel
