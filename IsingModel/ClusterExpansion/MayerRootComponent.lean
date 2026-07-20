import IsingModel.ClusterExpansion.MayerRootComponent.ComponentFiber
import IsingModel.ClusterExpansion.MayerRootComponent.FiberProduct
import IsingModel.ClusterExpansion.MayerRootComponent.FactorReindex
import IsingModel.ClusterExpansion.MayerRootComponent.RecurrenceClosedForm
import IsingModel.ClusterExpansion.MayerRootComponent.UrsellComplete

/-!
# Mayer K_n root-component recurrence — root-component vertex set (GJ §18.4)

Foundations for the root-component bijection
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` underlying the Mayer Phase B identity
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` (#1499).

For an edge-subset `S`, `rootComponentFinset S r` is the vertex set of the
connected component of the root `r` in `fromEdgeSet ↑S`. This section sets up the
component-membership characterisation and the crossing-edge-free property used to
split `S` into its within-component and outside-component parts.

## Contents

The declarations live in five child modules, re-exported by this declaration-free facade:

* `….MayerRootComponent.ComponentFiber` — the root-component vertex set
  `rootComponentFinset` and everything needed to characterise its fibre: component
  membership, self-membership, the crossing-edge-free membership criterion, the
  inside/outside edge-count split, the `supp` identification, the induced-graph identity,
  reachability confinement, inside connectivity, the fibre characterisation
  `rootComponentFinset_eq_iff` and the `C.sym2` / `Cᶜ.sym2` disjointness.
* `….MayerRootComponent.FiberProduct` — the inside/outside edge-subset families
  `insideConnectedEdgeSubsets` and `outsideEdgeSubsets` with their membership lemmas, the
  crossing-free bijection giving the per-fibre product factorisation, the real
  alternating-powerset dichotomy, and the fibrewise sum
  `allSignedSubgraphSum_eq_sum_fiber_product`.
* `….MayerRootComponent.FactorReindex` — evaluation of both factors of the fibre split as
  complete-graph sums: the outside factor as `D (K_{Cᶜ})` (powerset identification,
  alternating dichotomy, complement-cardinality criterion, subtype evaluation of `D`) and
  the inside factor as `c (K_C)` (the `Sym2.map` graph identity with its range and roundtrip
  lemmas).
* `….MayerRootComponent.RecurrenceClosedForm` — the assembled root-component recurrence over
  `K_n`, the surviving root-component sets, the collapse `c_n + (n-1) c_{n-1} = 0` and the
  closed form `c_n = (-1)^(n-1) (n-1)!`.
* `….MayerRootComponent.UrsellComplete` — the Ursell-coefficient consequences for a
  pairwise-incompatible polymer sequence, whose incompatibility graph is complete: the
  normalised connected-spanning signed sum form of `ursellCoefficient`, the completeness
  criterion, the transported closed form and the resulting value `ϕ^T (ω) = (-1)^(n-1) / n`.
-/
