import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhCore
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhExpTanh
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhSimonLieb
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhBridge

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor from a cubicTanhProfileBound family

Step 119 plan Step 5.7: concrete constructor for the abstract
`PseudoMassLatticeDistanceBridge` structure introduced in
`PseudoMass/HLSCorrelationCapstone.lean` (#3171). Given a family of anchored
`cubicTanhProfileBound` hypotheses (one per nonzero displacement) and a uniform
zero-anchored pseudo-mass lower bound `M_inf · d(0, w) ≤
pseudoMassFromParamsAtPair 0 w · r`, we produce the bridge as a single
`PseudoMassLatticeDistanceBridge` value, which can then be fed directly into
the HLS sum bound `tsum_correlationInfinite_pair_product_le_HLS_const`.

The lift from anchored to arbitrary distinct pairs uses translation invariance
of the ℤ^d Ising model under the cubic exhaustion: pair correlations only
depend on the displacement `z - x` via
`correlationInfinite_latticeGraph_pair_eq_twoPointFunction`, and lattice
distances on ℤ^d are translation invariant by `latticeDistance_translate_eq`.

This family-based constructor is kept as a compatibility interface for callers
that already have the all-displacement `cubicTanhProfileBound` family.  The
no-go facts in `CubicPseudoMassTanhProfileNoGo` show that this family cannot be
discharged in positive dimension with `0 < r`, `0 < β * J`, and
`β * J * (2 * d) < 1`; for the family-free high-temperature shape, use the
direct constructor together with the adjacent, bound, and active inputs packaged
in `HLSBridgeFromSimonLieb`.

The bridge constructor lives outside `IsingModel/PseudoMass/` to avoid an
import cycle: `LatticeMassPseudoMassTransferTanhPowDistCubicPair` (consumed
transitively via `CubicPseudoMassTanhProfileCubicPair`) imports
`IsingModel.PseudoMass`.

This module is a thin umbrella re-exporting the structural split across four
child modules:

- `HLSBridgeFromCubicTanhCore`: core translation reductions, the
  zero-anchored bound lift, the family-based bridge constructor, and the
  `pseudoMassG`-shaped atomic reductions.
- `HLSBridgeFromCubicTanhExpTanh`: `exp` / `tanh` correlation-upper-bound
  composers (Steps 5.7e/5.7f/5.7i).
- `HLSBridgeFromCubicTanhSimonLieb`: Simon-Lieb direct `bridge.bound`
  composers and quantifier lifts (Steps 5.7j–5.7n and the full trichotomy).
- `HLSBridgeFromCubicTanhBridge`: the all-pair active range and the direct
  `PseudoMassLatticeDistanceBridge` constructor (Steps 5.7o/5.7p).

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/
