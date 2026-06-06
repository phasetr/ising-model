import IsingModel.Peierls.DualCut
import IsingModel.Peierls.FilledRegion
import IsingModel.AmbientLattice.Defs.Core

/-!
# Lifting the box cut to the ambient lattice (FV §3.7.2)

The Peierls cut `cutEdges (inducedGraph (latticeGraph 2) Λ) F` of a region `F` in the finite box
`Λ` lives in `Sym2 ↑Λ` (the box subtype), while the dual-edge machinery lives on the ambient
lattice `Sym2 (Fin 2 → ℤ)`. The inclusion `↑Λ ↪ Fin 2 → ℤ` lifts each box cut edge to an ambient
lattice edge (via `Sym2.map Subtype.val`); this is injective, so the lifted cut and its dual have
the same cardinality `r = |cutEdges F|` as the box cut.

* `liftBoxCut` — the box cut lifted to ambient lattice edges.
* `liftBoxCut_subset_lattice` — each lifted edge is a `latticeGraph 2` edge.
* `liftBoxCut_card`, `dualEdges_liftBoxCut_card` — cardinality preservation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {Λ : Finset (Fin 2 → ℤ)} {F : Finset ↑Λ}

/-- Adjacency in the induced 2D box graph is decidable (it reduces to ambient adjacency on the
underlying lattice points). -/
instance instDecidableInducedLatticeAdj (Λ : Finset (Fin 2 → ℤ)) :
    DecidableRel (Ambient.inducedGraph (latticeGraph 2) Λ).Adj :=
  fun a b => inferInstanceAs (Decidable ((latticeGraph 2).Adj a.val b.val))

/-- **The box cut lifted to the ambient lattice**: each cut edge of the induced box graph is
mapped to the corresponding ambient `latticeGraph 2` edge via the subtype inclusion. -/
noncomputable def liftBoxCut (Λ : Finset (Fin 2 → ℤ)) (F : Finset ↑Λ) :
    Finset (Sym2 (Fin 2 → ℤ)) :=
  (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) F).image (Sym2.map Subtype.val)

/-- **Lifted cut edges are lattice edges**: every edge of `liftBoxCut Λ F` lies in
`(latticeGraph 2).edgeSet`. -/
theorem liftBoxCut_subset_lattice :
    ∀ e ∈ liftBoxCut Λ F, e ∈ (latticeGraph 2).edgeSet := by
  intro e he
  rw [liftBoxCut, Finset.mem_image] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rw [cutEdges, Finset.mem_filter] at he0
  have hadj := (SimpleGraph.mem_edgeFinset).mp he0.1
  induction e0 with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at hadj
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact hadj

/-- **The lift preserves cardinality**: `Sym2.map Subtype.val` is injective (the inclusion is
injective), so the lifted cut has the same size as the box cut. -/
theorem liftBoxCut_card :
    (liftBoxCut Λ F).card = (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) F).card := by
  classical
  rw [liftBoxCut, Finset.card_image_of_injOn]
  exact fun a _ b _ hab => (Sym2.map.injective Subtype.val_injective) hab

/-- **The dual of the lifted cut has the same size `r`**: combining the lift cardinality with the
dual cardinality preservation. -/
theorem dualEdges_liftBoxCut_card :
    (dualEdges (liftBoxCut Λ F)).card =
      (cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) F).card := by
  rw [dualEdges_card liftBoxCut_subset_lattice, liftBoxCut_card]

end IsingModel
