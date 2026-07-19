import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz.PseudoMassPowerBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz.AllRateBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz.CubicEnlargedSandwich
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz.NamedRateCapstones

/-!
# GJ §17.5 Lemma 17.5.2 capstone — interval Lipschitz bridges

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the finite-stage and infinite-volume HLS-constant interval Lipschitz
estimates for `β ↦ (h β)^(2α+1)`, plus the infinite-volume HLS-constant
derivative bound for the same target, all carrying the convolution inequality
from `lemma_17_5_2_hls_convolution_constant`.

This file is now an umbrella that re-exports its child modules:

* `Lipschitz.PseudoMassPowerBridges` — pseudo-mass power Lipschitz/derivative
  bridges.
* `Lipschitz.AllRateBridges` — all-rate upper-bound and sandwich bridges.
* `Lipschitz.CubicEnlargedSandwich` — cubic enlarged-HLS sandwich packages.
* `Lipschitz.NamedRateCapstones` — named-rate and profile-lower capstones.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/
