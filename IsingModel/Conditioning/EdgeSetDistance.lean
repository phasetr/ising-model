import IsingModel.ClusterExpansion.Basic
import IsingModel.Conditioning.PlusOnePointConnectedBound
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distance bound for edge-connected edge sets

For an edge-connected edge set `X : Finset (Sym2 ι)`, any two vertices in its support are
reachable in the graph `fromEdgeSet X`, and the distance between them is at most `|X|`.
This is the graph-theoretic input to the FV §3.7.3 bound `|C| ≥ n` (a connected
component of the origin reaching the box boundary must have at least `n` edges), towards
the high-temperature `m*(β)=0` (Issue #3613).

* `reachable_fromEdgeSet_of_mem_edge` — vertices of a non-diagonal edge are reachable.
* `reachable_fromEdgeSet_of_reflTransGen` — edge-adjacency chains lift to reachability.
* `fromEdgeSet_dist_le_card` — the distance bound `dist u v ≤ |X|`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Vertices of an edge are reachable**: both endpoints of an edge `e ∈ X` are reachable
in `fromEdgeSet ↑X`. -/
theorem reachable_fromEdgeSet_of_mem_edge {X : Finset (Sym2 ι)} {e : Sym2 ι}
    (heX : e ∈ X) {a b : ι} (ha : a ∈ e) (hb : b ∈ e) :
    (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).Reachable a b := by
  by_cases hab : a = b
  · subst hab; exact SimpleGraph.Reachable.refl a
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, hab⟩
    have hee : e = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩
    rw [← hee]
    exact_mod_cast heX

omit [DecidableEq ι] in
/-- **Edge-adjacency chains lift to reachability**: if `e` and `f` are edge-connected in
`X` (a `ReflTransGen` chain of shared-vertex steps), then every vertex of `e` is reachable
from every vertex of `f` in `fromEdgeSet ↑X`. -/
theorem reachable_fromEdgeSet_of_reflTransGen {X : Finset (Sym2 ι)}
    {e f : Sym2 ι} (heX : e ∈ X)
    (hef : Relation.ReflTransGen (edgeAdjacentIn X) e f) :
    ∀ a ∈ e, ∀ b ∈ f, (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).Reachable a b := by
  induction hef with
  | refl =>
    intro a ha b hb
    exact reachable_fromEdgeSet_of_mem_edge heX ha hb
  | @tail g f' _ hgf ih =>
    intro a ha b hb
    obtain ⟨_, hfX, w, hwg, hwf⟩ := hgf
    exact (ih a ha w hwg).trans
      (reachable_fromEdgeSet_of_mem_edge hfX hwf hb)

omit [DecidableEq ι] in
/-- **Distance is bounded by the edge count**: if `u` and `v` are reachable in
`fromEdgeSet ↑X`, then their distance is at most `|X|` (a shortest path is a trail, so its
edges are distinct and lie in `X`). -/
theorem fromEdgeSet_dist_le_card {X : Finset (Sym2 ι)} {u v : ι}
    (h : (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).Reachable u v) :
    (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).dist u v ≤ X.card := by
  classical
  obtain ⟨w⟩ := h
  refine (SimpleGraph.dist_le w.bypass).trans ?_
  have hnodup : w.bypass.edges.Nodup := w.bypass_isPath.isTrail.edges_nodup
  have hsub : w.bypass.edges.toFinset ⊆ X := by
    intro e he
    rw [List.mem_toFinset] at he
    have hmem := w.bypass.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
    exact_mod_cast hmem.1
  calc w.bypass.length = w.bypass.edges.length := (SimpleGraph.Walk.length_edges _).symm
    _ = w.bypass.edges.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ X.card := Finset.card_le_card hsub

omit [DecidableEq ι] in
/-- **Reachability from edge-connectedness and incidence**: if `X` is edge-connected and
`u`, `v` are each incident to some edge of `X`, then `u` and `v` are reachable in
`fromEdgeSet ↑X`. -/
theorem reachable_fromEdgeSet_of_edgeConnected {X : Finset (Sym2 ι)}
    (hconn : IsEdgeConnected X) {eu ev : Sym2 ι} (heu : eu ∈ X) (hev : ev ∈ X)
    {u v : ι} (hu : u ∈ eu) (hv : v ∈ ev) :
    (SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι))).Reachable u v :=
  reachable_fromEdgeSet_of_reflTransGen heu (hconn eu heu ev hev) u hu v hv

omit [DecidableEq ι] in
/-- **Supergraph distance bound for an edge-connected set**: if `X ⊆ G.edgeFinset` is
edge-connected with `u`, `v` each incident to an edge of `X`, then `G.dist u v ≤ |X|`. -/
theorem dist_le_card_of_edgeConnected {X : Finset (Sym2 ι)} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (hXG : X ⊆ G.edgeFinset) (hconn : IsEdgeConnected X) {eu ev : Sym2 ι}
    (heu : eu ∈ X) (hev : ev ∈ X) {u v : ι} (hu : u ∈ eu) (hv : v ∈ ev) :
    G.dist u v ≤ X.card := by
  have hle : SimpleGraph.fromEdgeSet (↑X : Set (Sym2 ι)) ≤ G := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    have : s(a, b) ∈ G.edgeFinset := hXG (by exact_mod_cast hab.1)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    exact this
  have hreach := reachable_fromEdgeSet_of_edgeConnected hconn heu hev hu hv
  exact (hreach.dist_anti hle).trans (fromEdgeSet_dist_le_card hreach)

/-- **The origin component is a single edge-component**: when `X` has an edge `e₀` at `z`,
the vertex-component `componentOfZero X z` equals the edge-component `edgeComponent X e₀`
(all `z`-edges are edge-adjacent through `z`, so they share one component). -/
theorem componentOfZero_eq_edgeComponent {X : Finset (Sym2 ι)} {z : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ X) (hz : z ∈ e₀) :
    componentOfZero X z = edgeComponent X e₀ := by
  classical
  unfold componentOfZero
  refine Finset.Subset.antisymm (fun f hf => ?_) (fun f hf => ?_)
  · rw [Finset.mem_biUnion] at hf
    obtain ⟨g, hg, hfg⟩ := hf
    rw [Finset.mem_filter] at hg
    have he₀g : e₀ ∈ edgeComponent X g :=
      mem_edgeComponent.mpr ⟨he₀, Relation.ReflTransGen.single ⟨hg.1, he₀, z, hg.2, hz⟩⟩
    rwa [← edgeComponent_eq_of_mem he₀g]
  · rw [Finset.mem_biUnion]
    exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀, hz⟩, hf⟩

/-- **The origin component is edge-connected** (when nonempty at `z`). -/
theorem isEdgeConnected_componentOfZero {X : Finset (Sym2 ι)} {z : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ X) (hz : z ∈ e₀) :
    IsEdgeConnected (componentOfZero X z) := by
  rw [componentOfZero_eq_edgeComponent he₀ hz]
  exact isEdgeConnected_edgeComponent e₀

/-- **Distance bound for the origin component**: if `X ⊆ G.edgeFinset` has an edge at `z`
and `v` is incident to a component edge, then `G.dist z v ≤ |componentOfZero X z|`. The
geometric input to FV (3.49): a component reaching a far vertex must be large. -/
theorem dist_le_card_componentOfZero {X : Finset (Sym2 ι)} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (hXG : X ⊆ G.edgeFinset) {z : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ X) (hz : z ∈ e₀) {ev : Sym2 ι} (hev : ev ∈ componentOfZero X z) {v : ι}
    (hv : v ∈ ev) :
    G.dist z v ≤ (componentOfZero X z).card := by
  refine dist_le_card_of_edgeConnected G
    ((componentOfZero_subset X z).trans hXG)
    (isEdgeConnected_componentOfZero he₀ hz)
    (mem_componentOfZero_of_incident he₀ hz) hev hz hv

end IsingModel
