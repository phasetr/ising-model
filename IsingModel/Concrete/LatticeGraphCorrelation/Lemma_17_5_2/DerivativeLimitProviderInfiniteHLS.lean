import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLSComparison
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLSRatioLower
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLSCompactBounds
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLSPathRate

/-!
# GJ §17.5 Lemma 17.5.2 capstone — provider-based infinite-HLS bridges

This module connects the derivative-limit provider to the infinite derivative
and infinite-HLS bridge layer below the larger finite-HLS assemblies.  The
substantive analytic theorem remains the proof of
`Lemma_17_5_2_DerivativeLimitProvider`; these entry points keep downstream
callers from naming the limiting derivative profile `g'`.

It is now split into four child modules for build speed; every previously
public declaration remains reachable transparently through the fully qualified
`IsingModel.Ambient` names re-exported by these imports:

* `DerivativeLimitProviderInfiniteHLSComparison` — shared concrete beta profile
  and the denominator-comparison / fixed-constant Lipschitz bridges.
* `DerivativeLimitProviderInfiniteHLSRatioLower` — high-temperature ratio-lower
  bridges.
* `DerivativeLimitProviderInfiniteHLSCompactBounds` — compact-ratio bridges.
* `DerivativeLimitProviderInfiniteHLSPathRate` — concrete infinite-HLS/path-rate
  upper-bound, sandwich, capstone and enlarged finite-HLS wrappers.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/
