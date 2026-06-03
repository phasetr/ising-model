import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Mayer K_n root-component recurrence — root-component vertex set (GJ §18.4)

Foundations for the root-component bijection
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` underlying the Mayer Phase B identity
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` (#1499).

For an edge-subset `S`, `rootComponentFinset S r` is the vertex set of the
connected component of the root `r` in `fromEdgeSet ↑S`. This section sets up the
component-membership characterisation and the crossing-edge-free property used to
split `S` into its within-component and outside-component parts.
-/

namespace IsingModel

open Finset

open Classical in
/-- **Root-component vertex set**: the vertices in the connected component of `r`
in `fromEdgeSet ↑S`, i.e. `{v | C_S(v) = C_S(r)}`. The component `C` of vertex `0`
in the root-component decomposition of `S`. -/
noncomputable def rootComponentFinset {V : Type*} [Fintype V]
    (S : Finset (Sym2 V)) (r : V) : Finset V :=
  Finset.univ.filter (fun v =>
    (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk v
      = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r)

/-- **Membership in `rootComponentFinset`**: `v ∈ rootComponentFinset S r` iff `v`
and `r` lie in the same connected component of `fromEdgeSet ↑S`. -/
theorem mem_rootComponentFinset {V : Type*} [Fintype V]
    {S : Finset (Sym2 V)} {r v : V} :
    v ∈ rootComponentFinset S r ↔
      (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk v
        = (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V))).connectedComponentMk r := by
  classical
  simp [rootComponentFinset]

/-- **The root lies in its own component**: `r ∈ rootComponentFinset S r`. -/
theorem self_mem_rootComponentFinset {V : Type*} [Fintype V]
    (S : Finset (Sym2 V)) (r : V) :
    r ∈ rootComponentFinset S r := by
  rw [mem_rootComponentFinset]

/-- **Crossing-edge-free property**: for an edge `s(a,b) ∈ S` (with `a ≠ b`), the
endpoints `a` and `b` lie in the root component together — either both in
`rootComponentFinset S r` or both outside. Hence no edge of `S` joins the root
component to its complement, which is what makes the root-component split of `S`
multiplicative. From `connectedComponentMk_eq_of_mem`. -/
theorem mem_rootComponentFinset_iff_of_mem_edge {V : Type*} [Fintype V]
    {S : Finset (Sym2 V)} {r a b : V} (hab : s(a, b) ∈ S) (hne : a ≠ b) :
    a ∈ rootComponentFinset S r ↔ b ∈ rootComponentFinset S r := by
  rw [mem_rootComponentFinset, mem_rootComponentFinset,
      connectedComponentMk_eq_of_mem hab hne]

end IsingModel
