import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.PointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.PointwiseDerivBounds
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.IccRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.IccLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.CorrelationMajorant

/-!
# Regularity of concrete pseudo-mass beta profiles

This module packages the continuity and differentiability inputs for the
concrete `pseudoMassFromParamsAtPair` beta profile.  These wrappers let callers
feed the localized Lemma 17.5.2 MVT/Lipschitz APIs using regularity of the
underlying infinite correlation profile plus active-range membership.

## Contents

The declarations live in five child modules, re-exported by this declaration-free facade:

* `….PseudoMassFromParamsRegularity.PointwiseRegularity` — the pointwise `ContinuousAt` and
  `DifferentiableAt` statements for the concrete `pseudoMassFromParamsAtPair` beta profile,
  transported through `pseudoMassExt`, together with the MVT-ready `HasDerivAt … (deriv …)`
  shape.
* `….PseudoMassFromParamsRegularity.PointwiseDerivBounds` — the implicit derivative formula
  coming from `pseudoMassG (m⁻ β) = correlationInfinite β`, the HLS power-derivative bound
  `(m⁻)^(2α) · |deriv m⁻| ≤ K / r`, and the power-chain derivative bound for
  `β ↦ (m⁻ β) ^ (2α + 1)`.
* `….PseudoMassFromParamsRegularity.IccRegularity` — the closed-interval (`Set.Icc β₁ β₂`)
  versions: `ContinuousOn`, the pointwise `HasDerivAt` package on the interval, the derivative
  formula on the interval, and the power-chain derivative bound on the interval.
* `….PseudoMassFromParamsRegularity.IccLipschitz` — the interval Lipschitz estimate for
  `β ↦ (m⁻ β) ^ (2α + 1)` and the GJ-aligned alias
  `gj_theorem_17_5_1_pseudoMass_pow_succ_lipschitz_on_Icc`.
* `….PseudoMassFromParamsRegularity.CorrelationMajorant` — the `m⁻` majorant
  `correlationInfinite ≤ 2 / (1 + (m⁻ · r) ^ α)` and its pair-product form, the Lebowitz IIIb
  cross-product input.  Independent of the other four children.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 (pp. 311–312).
-/
