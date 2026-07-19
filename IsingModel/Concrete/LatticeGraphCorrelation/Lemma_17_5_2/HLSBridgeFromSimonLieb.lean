import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebCore
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebTanh
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebVariants
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebCanonical

/-!
# Bridge-to-HLS sum bundle: Simon-Lieb + adjacent + ferromagnetic chain

Bundled GJ-proposition-size PR consolidating the structural chain from
Simon-Lieb / adjacent / ferromagnetic concrete analytic inputs to the HLS
sum bound `tsum_correlationInfinite_pair_product_le_HLS_const` (#3171).

Built on the atomic Step 5.7d-p building blocks (#3175-#3187):

- Step 5.7d/e (#3175/#3176): per-`w` exp/tanh → `bridge.bound` composers
- Step 5.7f/i (#3177/#3180): trichotomy `hbase` quantifier composers
- Step 5.7g/h (#3178/#3179): Simon-Lieb exp-form correlation bounds
- Step 5.7j-l (#3181-#3183): combined Simon-Lieb + adjacent per-`w` composers
- Step 5.7m/n (#3184/#3185): per-`w` to ∀ `w` ≠ 0 to all-pair lifts
- Step 5.7o (#3186): active range from `0 < β·J`
- Step 5.7p (#3187): direct `PseudoMassLatticeDistanceBridge` constructor
- Full trichotomy extension (#3373): adjacent/small/large Simon-Lieb bridge
  constructors and canonical entry points without the uniform small-regime
  premise

This file provides:

1. End-to-end `PseudoMassLatticeDistanceBridge` construction from Simon-Lieb
   + adjacent + ferromagnetic concrete inputs, including full trichotomy
   constructors.
2. HLS sum existential consumers at common anchor patterns.
3. Constant-form (explicit `K`) HLS sum consumers.
4. Per-pair specializations for downstream Lemma 17.5.2 finite-stage and
   sandwich machinery.
5. Canonical `canonical_*` entry points formerly housed in the retired
   `HLSBridgeSummary` wrapper module.

After the all-displacement `cubicTanhProfileBound` no-go facts, these direct
Simon-Lieb trichotomy constructors are the canonical family-free bridge route
in the positive-dimensional regime where `0 < r`, `0 < β * J`, and
`β * J * (2 * d) < 1` rule out the tanh-profile family.  They package the
adjacent correlation input together with the concrete bound and active-range
ingredients into `PseudoMassLatticeDistanceBridge` fields without assuming that
conditional family interface.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/
