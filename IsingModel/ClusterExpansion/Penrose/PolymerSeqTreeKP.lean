import IsingModel.ClusterExpansion.Penrose.PolymerSeqTreeOrientation
import IsingModel.ClusterExpansion.PolymerActivityKP

/-!
# Parent-edge Kotecky--Preiss weight bound for the rooted-tree induction (GJ §18.5)

Combining the rooted-tree orientation (`PolymerSeqTreeOrientation`) with the
discharged Kotecky--Preiss hypothesis (`incompatibilityActivity_expWeighted_le_card_of_half`,
FV Theorem 5.4) gives the per-parent-edge bound that the tree-graph induction
applies along every edge of a spanning tree of the polymer-sequence
incompatibility graph.

For a tree subgraph `H ≤ polymerSeqIncompatibilityGraph ω` rooted at `r`:

* `polymerSeqTree_child_mem_incompatiblePolymers`: every non-root vertex's polymer
  `ω v` lies in the incompatibility neighbourhood `incompatiblePolymers G (ω (parent v))`
  of its parent (the orientation fact, in the `Finset` form the activity sum ranges over).
* `polymerSeqTree_childActivityWeight_le_parentCard`: hence at high temperature
  (`Δ²·e·|t| ≤ ½`) the `e`-weighted activity of `ω v` is bounded by the edge count of
  its parent polymer, `e^{|ω v|}·|t|^{|ω v|} ≤ |ω (parent v)|` — a single term of the
  Kotecky--Preiss sum dominated by its `|P|` bound.

These are the literal per-edge inputs of the rooted-tree induction that proves the
volume-uniform cluster-expansion convergence (FV Theorem 5.4 conclusion).

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- **A non-root vertex's polymer lies in its parent's incompatibility
neighbourhood.**  For a tree subgraph `H ≤ polymerSeqIncompatibilityGraph ω` of a
polymer sequence into `allPolymers G`, every non-root vertex `v` satisfies
`ω v ∈ incompatiblePolymers G (ω (parent v))` — the orientation fact recast in the
`Finset` over which the Kotecky--Preiss activity sum ranges. -/
theorem polymerSeqTree_child_mem_incompatiblePolymers (G : SimpleGraph ι)
    [Fintype G.edgeSet] (ω : α → Finset (Sym2 ι)) (hω : ∀ i, ω i ∈ allPolymers G)
    {H : SimpleGraph α} (hsub : H ≤ polymerSeqIncompatibilityGraph ω) (hH : H.IsTree)
    (r v : α) (hv : v ≠ r) :
    ω v ∈ incompatiblePolymers G (ω (Penrose.treeParent hH r v hv)) := by
  rw [incompatiblePolymers, Finset.mem_filter]
  exact ⟨hω v, (polymerSeqTree_parent_incompatible ω hsub hH r v hv).symm⟩

/-- **Parent-edge Kotecky--Preiss weight bound.**  At high temperature
(`Δ²·e·|t| ≤ ½`, `Δ = G.maxDegree`), the `e`-weighted activity of a non-root
vertex's polymer is bounded by the edge count of its parent polymer:
`e^{|ω v|}·|t|^{|ω v|} ≤ |ω (parent v)|`.  This is a single term of the
Kotecky--Preiss sum `∑_{Q ∼ ω (parent v)} e^{|Q|}|t|^{|Q|} ≤ |ω (parent v)|`
(`incompatibilityActivity_expWeighted_le_card_of_half`), selected by the
orientation membership above.  It is the per-edge input applied along every parent
edge of the rooted-tree induction. -/
theorem polymerSeqTree_childActivityWeight_le_parentCard (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (ω : α → Finset (Sym2 ι))
    (hω : ∀ i, ω i ∈ allPolymers G)
    {H : SimpleGraph α} (hsub : H ≤ polymerSeqIncompatibilityGraph ω) (hH : H.IsTree)
    (r v : α) (hv : v ≠ r) {t : ℝ}
    (hsmall : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) ≤ (1 / 2 : ℝ)) :
    Real.exp 1 ^ (ω v).card * |t| ^ (ω v).card
      ≤ ((ω (Penrose.treeParent hH r v hv)).card : ℝ) := by
  have hmem := polymerSeqTree_child_mem_incompatiblePolymers G ω hω hsub hH r v hv
  refine le_trans (Finset.single_le_sum
    (f := fun Q => Real.exp 1 ^ Q.card * |t| ^ Q.card)
    (fun Q _ => by positivity) hmem) ?_
  exact incompatibilityActivity_expWeighted_le_card_of_half G
    (hω (Penrose.treeParent hH r v hv)) hsmall

end IsingModel
