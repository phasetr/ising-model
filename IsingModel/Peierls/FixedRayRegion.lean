import IsingModel.Peierls.RightRayVerticalParity
import IsingModel.Peierls.DartDualComponentBoxEulerian
import IsingModel.Peierls.PlanarBondSeparationBridge
import IsingModel.Peierls.DartOfCut

/-!
# The fixed-ray region realises an even edge set as a cut (FV §3.7.2)

Given a box `Λ` and an even edge set `B : Finset (Sym2 ↑Λ)` (even total `B`-membership around every
unit square), the rightward-ray parity defines a region whose edge cut is exactly `B`: this is the
finite-grid mod-2 planar duality `cutEdges S = B` that, via `even_cutCrossings_iff`, makes every
closed walk cross `B` an even number of times — the discrete-Stokes input the separation core needs.

* `fixedRayRegion` — `{v | the rightward ray from v crosses the ambient image of B oddly}`.
* `mem_image_val_pair_iff` — the box-edge / ambient-edge membership bridge.
* `fixedRayRegion_flip_iff_mem_of_adj` — across an edge, the region membership flips iff the edge is
  in `B` (the four axis directions via the horizontal/vertical ray-parity flips).
* `cutEdges_fixedRayRegion_eq_of_square_even` — `cutEdges (fixedRayRegion) = B`.
* `image_val_square_even_of_box_dualIncident_even` — the `hSquare` bridge from box incidence.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {Λ : Finset (Fin 2 → ℤ)}

/-- **The fixed-ray region**: vertices `v` whose rightward ray crosses the ambient image of `B` an
odd number of times. Its edge cut will be exactly `B`. -/
noncomputable def fixedRayRegion (Λ : Finset (Fin 2 → ℤ)) (B : Finset (Sym2 (↑Λ : Type _))) :
    Finset (↑Λ : Type _) := by
  classical
  exact Finset.univ.filter fun v => Odd (rightRayCount (B.image (Sym2.map Subtype.val)) v.val)

/-- **Membership in the fixed-ray region**. -/
theorem mem_fixedRayRegion_iff {B : Finset (Sym2 (↑Λ : Type _))} {v : (↑Λ : Type _)} :
    v ∈ fixedRayRegion Λ B ↔
      Odd (rightRayCount (B.image (Sym2.map Subtype.val)) v.val) := by
  classical
  unfold fixedRayRegion
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

/-- **Box-edge / ambient-edge membership bridge**: the ambient image edge `s(a.val, b.val)` lies in
`B.image (Sym2.map Subtype.val)` iff the box edge `s(a, b)` lies in `B` (by injectivity of
`Sym2.map Subtype.val`). -/
theorem mem_image_val_pair_iff (B : Finset (Sym2 (↑Λ : Type _))) (a b : (↑Λ : Type _)) :
    s(a.val, b.val) ∈ B.image (Sym2.map Subtype.val) ↔ s(a, b) ∈ B := by
  classical
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, hmap⟩
    have heq : e = s(a, b) :=
      Sym2.map.injective Subtype.val_injective (by rw [hmap, Sym2.map_mk])
    rwa [heq] at he
  · intro h
    exact ⟨s(a, b), h, by rw [Sym2.map_mk]⟩

/-- **Region flip across an edge ⟺ edge membership**: for adjacent box vertices `a, b`, the region
membership of `a` and `b` differs iff `s(a, b) ∈ B`. Each axis direction is the horizontal or
vertical ray-parity flip. -/
theorem fixedRayRegion_flip_iff_mem_of_adj {B : Finset (Sym2 (↑Λ : Type _))}
    (hSquare : ∀ c : Fin 2 → ℤ,
      Even (((B.image (Sym2.map Subtype.val)).filter
        (fun e => e ∈ primalSquareBoundaryEdges c)).card))
    {a b : (↑Λ : Type _)} (hadj : (latticeGraph 2).Adj a.val b.val) :
    ((a ∈ fixedRayRegion Λ B) ↔ ¬ b ∈ fixedRayRegion Λ B) ↔ s(a, b) ∈ B := by
  set Bimg := B.image (Sym2.map Subtype.val) with hBimg
  have psymm : ∀ m n : ℕ, (Odd m ↔ ¬ Odd n) ↔ (Odd n ↔ ¬ Odd m) := fun m n => by tauto
  simp only [mem_fixedRayRegion_iff, ← hBimg]
  rcases latticeGraph2_adj_cases hadj with h | h | h | h
  · rw [h, rightRayParity_xor_horizontal Bimg a.val, ← h]
    exact mem_image_val_pair_iff B a b
  · have ha : a.val = b.val + unitVec2 0 := by rw [h]; abel
    rw [ha, psymm, rightRayParity_xor_horizontal Bimg b.val, ← ha, Sym2.eq_swap]
    exact mem_image_val_pair_iff B a b
  · rw [h, rightRayParity_xor_vertical Bimg a.val hSquare, ← h]
    exact mem_image_val_pair_iff B a b
  · have ha : a.val = b.val + unitVec2 1 := by rw [h]; abel
    rw [ha, psymm, rightRayParity_xor_vertical Bimg b.val hSquare, ← ha, Sym2.eq_swap]
    exact mem_image_val_pair_iff B a b

/-- **The fixed-ray region's edge cut is `B`** (under the even square count): every box edge is
a cut edge of `fixedRayRegion` iff it lies in `B`. The finite-grid mod-2 planar duality. -/
theorem cutEdges_fixedRayRegion_eq_of_square_even (B : Finset (Sym2 (↑Λ : Type _)))
    (hBedge : B ⊆ (Ambient.inducedGraph (latticeGraph 2) Λ).edgeFinset)
    (hSquare : ∀ c : Fin 2 → ℤ,
      Even (((B.image (Sym2.map Subtype.val)).filter
        (fun e => e ∈ primalSquareBoundaryEdges c)).card)) :
    cutEdges (Ambient.inducedGraph (latticeGraph 2) Λ) (fixedRayRegion Λ B) = B := by
  classical
  ext e
  induction e with
  | h a b =>
    rw [mem_cutEdges_iff]
    constructor
    · rintro ⟨hadj, hflip⟩
      exact (fixedRayRegion_flip_iff_mem_of_adj hSquare (inducedLattice_adj_iff.mp hadj)).mp hflip
    · intro hmem
      have hadj : (Ambient.inducedGraph (latticeGraph 2) Λ).Adj a b :=
        SimpleGraph.mem_edgeFinset.mp (hBedge hmem)
      exact ⟨hadj, (fixedRayRegion_flip_iff_mem_of_adj hSquare
        (inducedLattice_adj_iff.mp hadj)).mpr hmem⟩

/-- **A box edge maps to a lattice edge**: the image of an induced-box edge under `Sym2.map
Subtype.val` is a `latticeGraph 2` edge. -/
theorem inducedEdge_map_val_mem_latticeEdgeSet {e0 : Sym2 (↑Λ : Type _)}
    (he0 : e0 ∈ (Ambient.inducedGraph (latticeGraph 2) Λ).edgeFinset) :
    Sym2.map Subtype.val e0 ∈ (latticeGraph 2).edgeSet := by
  induction e0 with
  | h p q =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he0
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact inducedLattice_adj_iff.mp he0

/-- **The `hSquare` bridge**: even box dual-incidence transports to even square count of the ambient
image (via `Finset.filter_image`, injectivity of `Sym2.map Subtype.val`, and
`primalSquareBoundaryEdges_count_even_of_dualIncident_even`). -/
theorem image_val_square_even_of_box_dualIncident_even {B : Finset (Sym2 (↑Λ : Type _))}
    (hBedge : B ⊆ (Ambient.inducedGraph (latticeGraph 2) Λ).edgeFinset)
    (hDualEven : ∀ c : Fin 2 → ℤ,
      Even ((B.filter (fun e => c ∈ dualEdge (Sym2.map Subtype.val e))).card)) :
    ∀ c : Fin 2 → ℤ,
      Even (((B.image (Sym2.map Subtype.val)).filter
        (fun e => e ∈ primalSquareBoundaryEdges c)).card) := by
  classical
  intro c
  refine primalSquareBoundaryEdges_count_even_of_dualIncident_even (fun e he => ?_) ?_
  · rw [Finset.mem_image] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact inducedEdge_map_val_mem_latticeEdgeSet (hBedge he0)
  · rw [Finset.filter_image,
      Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    exact hDualEven c

end IsingModel
