import IsingModel.Peierls.DartDualComponentBoxEulerian
import IsingModel.Peierls.DartOfCut
import IsingModel.Peierls.DartCutChar

/-!
# Primal edges around a dual vertex (FV §3.7.2)

Towards the fixed-ray region construction (`cutEdges S = B`), this file identifies the primal
lattice edges whose dual edge passes through a given dual vertex `c`: they are exactly the four
edges `primalCutEdge c dir`. Via this identification, the even dual-incidence degree of the
box-primal set `B` (`DartDualComponentBoxIncidentEven.lean`) becomes an even count of `B`-edges
around each dual vertex.

* `exists_dir_eq_of_mem_edgeSet` — a lattice edge through `c` is `s(c, c + dir.vec)` for some dir.
* `primalSquareBoundaryEdges` — the four primal edges `primalCutEdge c dir` at dual vertex `c`.
* `mem_primalSquareBoundaryEdges_iff_dualIncident` — `e ∈ primalSquareBoundaryEdges c ↔ c ∈
  dualEdge e` (for lattice edges `e`).
* `primalSquareBoundaryEdges_count_even_of_dualIncident_even` — an even dual-incidence count is an
  even count of `B`-edges in `primalSquareBoundaryEdges c`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **A lattice edge through `c` is an axis step from `c`**: if `e` is a `latticeGraph 2` edge with
`c ∈ e`, then `e = s(c, c + dir.vec)` for some direction `dir`. The four `Dir2` direction vectors
`(0,1,2,3).vec` are `±e₀, ±e₁` (definitionally), matching `latticeGraph2_adj_cases`. -/
theorem exists_dir_eq_of_mem_edgeSet {e : Sym2 (Fin 2 → ℤ)}
    (he : e ∈ (latticeGraph 2).edgeSet) {c : Fin 2 → ℤ} (hc : c ∈ e) :
    ∃ dir : Dir2, e = s(c, c + dir.vec) := by
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [Sym2.mem_iff] at hc
    rcases hc with rfl | rfl
    · rcases latticeGraph2_adj_cases he with h | h | h | h
      · exact ⟨0, by rw [h]; rfl⟩
      · exact ⟨2, by rw [h]; rfl⟩
      · exact ⟨1, by rw [h]; rfl⟩
      · exact ⟨3, by rw [h]; rfl⟩
    · rw [Sym2.eq_swap]
      rcases latticeGraph2_adj_cases he.symm with h | h | h | h
      · exact ⟨0, by rw [h]; rfl⟩
      · exact ⟨2, by rw [h]; rfl⟩
      · exact ⟨1, by rw [h]; rfl⟩
      · exact ⟨3, by rw [h]; rfl⟩

/-- **The primal edges around a dual vertex `c`**: the four edges `primalCutEdge c dir`. -/
noncomputable def primalSquareBoundaryEdges (c : Fin 2 → ℤ) : Finset (Sym2 (Fin 2 → ℤ)) :=
  (Finset.univ : Finset Dir2).image (fun dir => primalCutEdge c dir)

/-- **Membership in the square boundary is dual incidence**: a lattice edge `e` is one of the four
primal edges at `c` iff its dual edge passes through `c`. -/
theorem mem_primalSquareBoundaryEdges_iff_dualIncident {c : Fin 2 → ℤ}
    {e : Sym2 (Fin 2 → ℤ)} (he : e ∈ (latticeGraph 2).edgeSet) :
    e ∈ primalSquareBoundaryEdges c ↔ c ∈ dualEdge e := by
  classical
  rw [primalSquareBoundaryEdges, Finset.mem_image]
  constructor
  · rintro ⟨dir, _, rfl⟩
    rw [dualEdge_primalCutEdge]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  · intro hc
    obtain ⟨dir, hdir⟩ := exists_dir_eq_of_mem_edgeSet (dualEdge_mem_edgeSet e) hc
    have hpce : primalCutEdge c dir ∈ (latticeGraph 2).edgeSet := by
      rw [primalCutEdge, SimpleGraph.mem_edgeSet]; exact leftSite_adj_rightSite c dir
    refine ⟨dir, Finset.mem_univ dir, dualEdge_injOn hpce he ?_⟩
    rw [dualEdge_primalCutEdge, ← hdir]

/-- **Even dual incidence is an even square-boundary count**: if `B` consists of lattice edges and
has even dual-incidence degree at `c`, then the number of `B`-edges in `primalSquareBoundaryEdges c`
is even (the two filters coincide by the membership characterization). -/
theorem primalSquareBoundaryEdges_count_even_of_dualIncident_even
    {B : Finset (Sym2 (Fin 2 → ℤ))} (hBedge : ∀ e ∈ B, e ∈ (latticeGraph 2).edgeSet)
    {c : Fin 2 → ℤ} (hEven : Even ((B.filter (fun e => c ∈ dualEdge e)).card)) :
    Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges c)).card) := by
  classical
  have hfilter : B.filter (fun e => e ∈ primalSquareBoundaryEdges c) =
      B.filter (fun e => c ∈ dualEdge e) :=
    Finset.filter_congr fun e he => by
      rw [mem_primalSquareBoundaryEdges_iff_dualIncident (hBedge e he)]
  rw [hfilter]
  exact hEven

end IsingModel
