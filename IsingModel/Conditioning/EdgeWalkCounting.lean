import IsingModel.Conditioning.EdgeWalkExistence
import IsingModel.Conditioning.WalkCountDegreeBound

/-!
# Counting connected edge sets via closed walks (FV §3.7.3, eq. 3.49)

The counting injection of FV §3.7.3: a connected edge set of size `ℓ` containing a fixed
vertex `z` is mapped, via its FV-Lemma-3.38 closed walk (crossing each edge twice), to a
closed walk of length `2ℓ` from `z`. The map is injective (the walk's edge set recovers
the edge set), so

`#{connected C ∋ z, |C|=ℓ, C ⊆ G.edgeFinset} ≤ #{closed walks of length 2ℓ from z}`,

which for the induced lattice box graph is `≤ (2d)^{2ℓ}`. This is the counting bound
feeding the high-temperature `m*(β)=0` capstone (Issue #3613).

* `exists_closed_walk_in_supergraph` — the Lemma-3.38 walk transported into the ambient
  graph `G`.
* `card_connected_edge_sets_le` — the counting injection.
* `card_connected_edge_sets_inducedLatticeGraph_le` — the `(2d)^{2ℓ}` lattice bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [DecidableEq ι]

/-- **FV Lemma 3.38 in the ambient graph**: a connected edge set `C ⊆ G.edgeFinset` admits
a closed walk in `G` itself (not just in `fromEdgeSet ↑C`) from any incident vertex `z`,
with edge set `C` and length `2|C|`. Transports the `fromEdgeSet ↑C` walk along the
inclusion `fromEdgeSet ↑C ≤ G`. -/
theorem exists_closed_walk_in_supergraph {G : SimpleGraph ι} [Fintype G.edgeSet]
    (C : Finset (Sym2 ι))
    (hCG : C ⊆ G.edgeFinset) (hconn : IsEdgeConnected C) {z : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ C) (hz : z ∈ e₀) :
    ∃ w : G.Walk z z, w.edges.toFinset = C ∧ w.length = 2 * C.card := by
  classical
  have hnd : ∀ e ∈ C, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.mp (hCG he))
  obtain ⟨w, hwedges, hwlen⟩ := exists_closed_walk_of_edgeConnected C hnd hconn he₀ hz
  refine ⟨w.transfer G (fun e he => ?_), ?_, ?_⟩
  · have hin := w.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hin
    exact G.mem_edgeFinset.mp (hCG (by exact_mod_cast hin.1))
  · rw [SimpleGraph.Walk.edges_transfer]; exact hwedges
  · rw [SimpleGraph.Walk.length_transfer]; exact hwlen

/-- **Counting injection** (FV §3.7.3): for a finite family `S` of connected edge sets of
size `ℓ` containing `z` (inside `G.edgeFinset`), `#S` is at most the number of closed walks
of length `2ℓ` from `z`. Each `C` is sent to its FV-Lemma-3.38 closed walk, injectively
since `C` is the walk's edge set. -/
theorem card_connected_edge_sets_le {G : SimpleGraph ι} [Fintype ι] [Fintype G.edgeSet]
    [DecidableRel G.Adj] (z : ι) (ℓ : ℕ) (S : Finset (Finset (Sym2 ι)))
    (hS : ∀ C ∈ S, C ⊆ G.edgeFinset ∧ IsEdgeConnected C ∧ C.card = ℓ ∧ ∃ e ∈ C, z ∈ e) :
    S.card ≤ (G.finsetWalkLength (2 * ℓ) z z).card := by
  classical
  -- send each `C` to a closed walk of length `2ℓ` with edge set `C`
  set P : Finset (Sym2 ι) → Prop :=
    fun C => ∃ w : G.Walk z z, w.length = 2 * ℓ ∧ w.edges.toFinset = C with hP
  set f : Finset (Sym2 ι) → G.Walk z z :=
    fun C => if h : P C then Classical.choose h else SimpleGraph.Walk.nil with hf
  have hPC : ∀ C ∈ S, P C := by
    intro C hC
    obtain ⟨hCG, hconn, hcard, e, heC, hze⟩ := hS C hC
    obtain ⟨w, hwe, hwl⟩ := exists_closed_walk_in_supergraph C hCG hconn heC hze
    exact ⟨w, by rw [hwl, hcard], hwe⟩
  have hspec : ∀ C ∈ S, (f C).length = 2 * ℓ ∧ (f C).edges.toFinset = C := by
    intro C hC
    have h := hPC C hC
    rw [hf]; simp only [dif_pos h]
    exact Classical.choose_spec h
  refine Finset.card_le_card_of_injOn f (fun C hC => ?_) (fun C hC C' hC' heq => ?_)
  · exact SimpleGraph.mem_finsetWalkLength_iff.mpr (hspec C hC).1
  · rw [← (hspec C hC).2, ← (hspec C' hC').2, heq]

/-- **Lattice counting bound** (FV (3.49) `(2d)^{2ℓ}`): in the induced cubic-lattice box
graph, the number of connected edge sets of size `ℓ` containing the origin is at most
`(2d)^{2ℓ}`. -/
theorem card_connected_edge_sets_inducedLatticeGraph_le {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (z : ↑Λ) (ℓ : ℕ) (S : Finset (Finset (Sym2 ↑Λ)))
    (hS : ∀ C ∈ S, C ⊆ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset ∧
      IsEdgeConnected C ∧ C.card = ℓ ∧ ∃ e ∈ C, z ∈ e) :
    S.card ≤ (2 * d) ^ (2 * ℓ) := by
  classical
  refine (card_connected_edge_sets_le z ℓ S hS).trans ?_
  refine (Finset.single_le_sum (f := fun v =>
    ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).finsetWalkLength (2 * ℓ) z v).card)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)).trans ?_
  exact walksFromCount_inducedLatticeGraph_le Λ z (2 * ℓ)

end IsingModel
