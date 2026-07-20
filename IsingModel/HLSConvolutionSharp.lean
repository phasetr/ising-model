import IsingModel.HLSConvolutionSharp.ShellSumsIntegralComparison
import IsingModel.HLSConvolutionSharp.RadialRegionBounds
import IsingModel.HLSConvolutionSharp.ConstantReductionCapstone

/-!
# Sharp distance-dependent Hardy–Littlewood–Sobolev convolution bound on ℤ^d

This module builds toward the **sharp** (distance-decaying) HLS convolution bound
needed by the proof of Glimm–Jaffe Theorem 17.5.1 (continuity of the mass,
2nd ed. pp.~311--312):
`∑_z (1 + |x − z|)^{-α} (1 + |y − z|)^{-α} ≤ C · (1 + |x − y|)^{-(2α − d)}`
for `d < 2α`, in contrast to the existing *constant* bound
`discrete_hls_convolution_constant` (`PolyDecay.lean`, `∑ ≤ C`, no decay).

The foundational step is the **shell reorganization**: a radial nonnegative
`ℝ≥0∞` kernel summed over `ℤ^d` equals the sum over radii of
`(sphere cardinality) × (kernel value)`.  Working in `ℝ≥0∞` keeps the
reindexing summability-free (`ENNReal.tsum_fiberwise`).

Tracking issue: <https://github.com/phasetr/ising-model/issues/4320>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1, pp.~311--312.

## Contents

The declarations live in three child modules, re-exported by this declaration-free facade:

* `HLSConvolutionSharp.ShellSumsIntegralComparison` — the shell reorganization
  `tsum_radial_eq_tsum_shell` of a radial `ℝ≥0∞` sum over `ℤ^d` and its arbitrary-centre
  form, the shell-cardinality power reduction `latticeSphere_card_mul_rpow_le`, and the
  finite-interval integral comparisons `sum_Ioc_nat_rpow_le` (tail, `e < -1`) and
  `sum_Ioc_zero_nat_rpow_le` (head, `-1 < e`).
* `HLSConvolutionSharp.RadialRegionBounds` — the radial shell-sum and lattice `ℝ≥0∞` sum
  bounds over a ball (`α < d`) and over a tail (`d < 2α`), the resulting near-`x` and far
  region bounds of the sharp HLS convolution, and the three-region cover
  `tsum_conv_le_sum_regions` of the full convolution sum.
* `HLSConvolutionSharp.ConstantReductionCapstone` — the base-shift bounds
  `rpow_neg_half_le` / `rpow_pos_two_mul_le`, the real-valued near- and far-region
  constant reductions, and the headline sharp decay bound `hls_conv_sharp_decay`.
-/
