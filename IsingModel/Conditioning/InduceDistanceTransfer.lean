import IsingModel.Conditioning.EdgeSetHandshake
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Distance transfer from an induced subgraph to the ambient graph

A walk in an induced subgraph maps to a walk in the ambient graph of the same length, so
the ambient distance is at most the induced distance. Specialised to the lattice graph,
`latticeDistance d a b ≤ (inducedGraph (latticeGraph d) Λ).dist a b`. This is the
subtype-to-ambient transfer needed to convert an induced-box distance bound into the
lattice `ℓ¹` distance, the geometric step of FV §3.7.3 `|C| ≥ n` (Issue #3613).

* `induceValHom` — the inclusion homomorphism `G.induce s →g G`.
* `dist_val_le_induce_dist` — `G.dist a b ≤ (G.induce s).dist a b` (reachable case).
* `latticeDistance_le_induce_dist` — the lattice specialisation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset SimpleGraph Ambient

variable {V : Type*}

/-- **The inclusion homomorphism** of an induced subgraph into the ambient graph: the
subtype projection `↑s → V` preserves adjacency (induced adjacency is the ambient
adjacency restricted to `s`). -/
def induceValHom (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => SimpleGraph.induce_adj.mp h

/-- **Ambient distance is bounded by induced distance**: if `a`, `b` are reachable in the
induced subgraph `G.induce s`, then `G.dist a b ≤ (G.induce s).dist a b` (the
distance-realising induced walk maps to an ambient walk of the same length). -/
theorem dist_val_le_induce_dist {G : SimpleGraph V} {s : Set V} {a b : ↑s}
    (h : (G.induce s).Reachable a b) :
    G.dist a.val b.val ≤ (G.induce s).dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc G.dist a.val b.val
      ≤ (p.map (induceValHom G s)).length := G.dist_le _
    _ = p.length := by rw [SimpleGraph.Walk.length_map]
    _ = (G.induce s).dist a b := hp

/-- **Lattice distance is bounded by induced-box distance**: for the lattice graph on a
finite box `Λ`, `latticeDistance d a b ≤ (inducedGraph (latticeGraph d) Λ).dist a b` when
`a`, `b` are reachable in the box. The subtype-to-ambient transfer of FV (3.49). -/
theorem latticeDistance_le_induce_dist {d : ℕ} {Λ : Finset (Fin d → ℤ)} {a b : ↑Λ}
    (h : (inducedGraph (latticeGraph d) Λ).Reachable a b) :
    latticeDistance d a.val b.val ≤ (inducedGraph (latticeGraph d) Λ).dist a b := by
  rw [← latticeGraph_dist_eq_latticeDistance]
  exact dist_val_le_induce_dist h

/-- **Lattice distance bound for the origin component** (FV (3.49)): on the induced box
graph, if the origin component has odd degree at `z`, then there is a second odd-degree
vertex `j ≠ z` with `latticeDistance d z.val j.val ≤ |componentOfZero X z|`. Composing the
handshake partner (`exists_dist_le_card_componentOfZero`) with the subtype-to-ambient
distance transfer — the component, reaching a far lattice site, must have many edges. -/
theorem latticeDistance_le_card_componentOfZero {d : ℕ} {Λ : Finset (Fin d → ℤ)}
    {X : Finset (Sym2 ↑Λ)}
    (hXG : X ⊆ (inducedGraph (latticeGraph d) Λ).edgeFinset)
    {z : ↑Λ} {e₀ : Sym2 ↑Λ} (he₀ : e₀ ∈ X) (hz : z ∈ e₀)
    (hzodd : Odd (((componentOfZero X z).filter (z ∈ ·)).card)) :
    ∃ j : ↑Λ, j ≠ z ∧ Odd (((componentOfZero X z).filter (j ∈ ·)).card)
      ∧ latticeDistance d z.val j.val ≤ (componentOfZero X z).card := by
  classical
  obtain ⟨j, hjz, hjodd, _hdist⟩ :=
    exists_dist_le_card_componentOfZero (inducedGraph (latticeGraph d) Λ) hXG he₀ hz hzodd
  -- reachability of `z`, `j` in the induced box graph, from component edge-connectedness
  have hCG : componentOfZero X z ⊆ (inducedGraph (latticeGraph d) Λ).edgeFinset :=
    (componentOfZero_subset X z).trans hXG
  obtain ⟨ej, hej⟩ := Finset.card_pos.mp hjodd.pos
  rw [Finset.mem_filter] at hej
  have hreachFE := reachable_fromEdgeSet_of_edgeConnected
    (isEdgeConnected_componentOfZero he₀ hz)
    (mem_componentOfZero_of_incident he₀ hz) hej.1 hz hej.2
  have hle : SimpleGraph.fromEdgeSet (↑(componentOfZero X z) : Set (Sym2 ↑Λ))
      ≤ inducedGraph (latticeGraph d) Λ := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    have : s(a, b) ∈ (inducedGraph (latticeGraph d) Λ).edgeFinset :=
      hCG (by exact_mod_cast hab.1)
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
  refine ⟨j, hjz, hjodd, ?_⟩
  calc latticeDistance d z.val j.val
      ≤ (inducedGraph (latticeGraph d) Λ).dist z j :=
        latticeDistance_le_induce_dist (hreachFE.mono hle)
    _ ≤ (componentOfZero X z).card := _hdist

end IsingModel
