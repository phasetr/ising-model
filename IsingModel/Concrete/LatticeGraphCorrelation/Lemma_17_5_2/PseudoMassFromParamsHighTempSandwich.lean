import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsHighTempSandwichActiveRange
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsHighTempSandwichRatioBounds
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsHighTempSandwichCompactBounds
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsHighTempSandwichCapstone

/-!
# Concrete pseudo-mass high-temperature sandwich package for GJ Lemma 17.5.2

This module combines the concrete `pseudoMassFromParamsAtPair` compact
upper-bound package with the existing high-temperature decay-transfer bridge.
The result removes the lower-side `HasExponentialDecay` premise whenever the
endpoint concrete pseudo-mass is bounded by the transferred high-temperature
rate, or by the equivalent `pseudoMassG` profile comparison.

This file is a thin umbrella re-exporting the split children so that downstream
consumers keep importing the original path unchanged:

* `PseudoMassFromParamsHighTempSandwichActiveRange` — active-range foundation
  (shared hub `lemma_17_5_2_active_range_on_Icc_of_high_temp_pair`);
* `PseudoMassFromParamsHighTempSandwichRatioBounds` — compact-ratio-bound
  auto-active wrappers;
* `PseudoMassFromParamsHighTempSandwichCompactBounds` — compact-bound
  rate-comparison and profile-lower sandwiches with their auto-active wrappers;
* `PseudoMassFromParamsHighTempSandwichCapstone` — capstone packages.
-/
