import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteHLSConcreteProvider
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteHLSScalarProvider
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteHLSRatioLower
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteHLSCompactBounds

/-!
# GJ §17.5 Lemma 17.5.2 capstone — provider-based finite-HLS assemblies

This module connects the derivative-limit provider introduced for
Lemma 17.5.2 to the larger finite-HLS high-temperature assemblies.  The
substantive analytic theorem remains the proof of
`Lemma_17_5_2_DerivativeLimitProvider`; these entry points keep downstream
callers from naming the limiting derivative profile `g'`, including the
concrete finite-derivative-provider capstone route.

The assemblies are now split into four child modules for build speed; this
head is a declaration-free umbrella re-exporting all of them:

* `DerivativeLimitProviderFiniteHLSConcreteProvider` — concrete
  finite-derivative-provider capstone route;
* `DerivativeLimitProviderFiniteHLSScalarProvider` — uniform finite/scalar
  provider route;
* `DerivativeLimitProviderFiniteHLSRatioLower` — ratio-lower and
  uniform-correlation route;
* `DerivativeLimitProviderFiniteHLSCompactBounds` — compact ratio-bounds route.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/
