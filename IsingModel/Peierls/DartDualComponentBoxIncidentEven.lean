import IsingModel.Peierls.DartDualCutEven
import IsingModel.Peierls.DartDualComponentBoxEulerian
import IsingModel.Peierls.DartDualCutCard

/-!
# The box-primal image of a dart's dual component is Eulerian (FV §3.7.2)

Transports the Eulerian (even-degree) property of a dart's dual component (`DartDualCutEven.lean`,
on the ambient dual edges `s(q.tail, q.head)`) to its box-primal image
`B = dartDualComponentBoxPrimalEdges`, measured by dual incidence (`c ∈ dualEdge (Sym2.map
Subtype.val e)`). Both `B` and the ambient dual component are images of the *same* reachable dart
finset (under injective maps `boxPrimalCutEdge` and `q ↦ s(q.tail, q.head)`), and the dual of a
box-primal edge is the corresponding ambient dual edge (`dualEdge_map_val_boxPrimalCutEdge`), so the
two incidence counts at any dual vertex agree.

* `dartDualComponentBoxPrimalEdges_dualIncident_card_eq` — the box-primal dual-incidence count at
  `c` equals the ambient dual component's incidence count.
* `dartDualComponentBoxPrimalEdges_dualIncident_even` — hence it is even at every dual vertex.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F Λ : Finset (Fin 2 → ℤ)}

/-- **The box-primal dual-incidence count equals the ambient incidence count**: filtering the
box-primal image `B` by the dual edges through `c` has the same cardinality as filtering the ambient
dual component by the edges through `c` (both reduce, via the injective image maps, to the reachable
darts whose dual edge passes through `c`). -/
theorem dartDualComponentBoxPrimalEdges_dualIncident_card_eq (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) (c : Fin 2 → ℤ) :
    ((dartDualComponentBoxPrimalEdges hFΛ hRΛ d).filter
        (fun e => c ∈ dualEdge (Sym2.map Subtype.val e))).card =
      ((dartDualComponentEdges F d).filter (fun e => c ∈ e)).card := by
  classical
  rw [dartDualComponentBoxPrimalEdges, Finset.filter_image,
    Finset.card_image_of_injective _ (BoundaryDart.boxPrimalCutEdge_injective hFΛ hRΛ),
    dartDualComponentEdges, Finset.filter_image,
    Finset.card_image_of_injective _ dartDualEdge_injective]
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [dualEdge_map_val_boxPrimalCutEdge hFΛ hRΛ q]

/-- **The box-primal image of a dart's dual component is Eulerian**: it has even dual-incidence
degree at every dual vertex `c`, by the card equality with the (even, by
`dartDualComponentEdges_incident_even`) ambient dual component. -/
theorem dartDualComponentBoxPrimalEdges_dualIncident_even (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F) (c : Fin 2 → ℤ) :
    Even (((dartDualComponentBoxPrimalEdges hFΛ hRΛ d).filter
      (fun e => c ∈ dualEdge (Sym2.map Subtype.val e))).card) := by
  rw [dartDualComponentBoxPrimalEdges_dualIncident_card_eq hFΛ hRΛ d c]
  exact dartDualComponentEdges_incident_even F d c

end IsingModel
