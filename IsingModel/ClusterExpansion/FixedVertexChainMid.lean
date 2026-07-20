import IsingModel.ClusterExpansion.FixedVertexChainMid.ActiveSumLeafPeel
import IsingModel.ClusterExpansion.FixedVertexChainMid.TailInductionCompleteTree
import IsingModel.ClusterExpansion.FixedVertexChainMid.PenroseTreeGeometric

/-!
# Fixed-vertex middle chain for the rooted Kotecky--Preiss bound (GJ §18.6)

This file supplies the root-filtered middle part of the fixed-vertex Route B chain.  The
root coordinate is kept inside the active-sum recursion all the way to the empty active
set, so the base root moment is over `rootedGasPolymers 𝓟 root` rather than over the whole
gas `𝓟`.  Everything is gas-parametrized over an abstract polymer set `𝓟` carrying
`PolymerGasData G 𝓟`, with a support-cardinality constant `c` (`|supp P| ≤ c·|P|`) threaded
through the leaf-peel step; the even gas (`allPolymers G`, `c = 1`) is recovered by thin
wrappers.

## Contents

The declarations live in three child modules, re-exported by this declaration-free facade:

* `FixedVertexChainMid.ActiveSumLeafPeel` — the root active vertex
  `rootedParentActiveRoot`, the fixed-root-filtered active gas sum
  `fixedVertexRootedGasParentActiveSum` and its empty-active-set base case, the
  erase/update recursion of the fixed-root peel bound, and the per-labelling leaf
  isolation and leaf-peel decomposition.
* `FixedVertexChainMid.TailInductionCompleteTree` — the tail leaf-peel inequality, the
  strong induction `fixedVertexRootedGasParentActiveSum_le_pow_mul_childCount_bound`, the
  `Fin (n+1)` labelling form of the univ fixed-root active sum, and the complete-tree
  bound by the weighted fixed-root peel bound.
* `FixedVertexChainMid.PenroseTreeGeometric` — the root-filtered Fubini swap of the
  Penrose tree sum, its combination with the complete-tree peel bound, and the headline
  fixed-root per-order geometric bound
  `fixedVertexGasRoot_termAbsSum_succ_le_div_mul_geometric`.
-/
