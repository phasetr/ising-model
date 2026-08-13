---
layout: default
title: Library map
---

[Back to the documentation home](index.md). The intended import direction is specified by the
[import-DAG layer contract](architecture-import-layers.md).

## Focused public modules

### Import guidance

`IsingModel.Concrete.LatticeGraphCorrelation` is a thin public re-export umbrella over its split
child modules.
New narrow APIs should prefer the dedicated child modules grouped below. These domain groups are
reading aids; import direction remains governed by the linked import-DAG contract.

## Concrete lattice wrappers

### Correlation, limits, and lattice mass

- `IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay` — Dedicated correlation-decay APIs.
- `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic` — Concrete anchored cubic
  pseudo-mass abbreviations, transport lemmas, and tanh-profile predicates.
- `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfile` — Concrete anchored cubic
  tanh-profile active-range and high-temperature lattice-mass bridge wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate` — Concrete anchored cubic
  named-rate lattice-mass, interval, and decay wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassClusterSummability` — Concrete
  anchored cubic named-rate cluster and product-summability wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassProductSum` — Concrete anchored cubic
  named-rate product-sum wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.Peierls` — Concrete Peierls along-exhaustion
  wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationMonotonicity` — Concrete
  finite-volume HNC, Gibbs-expectation, and correlation monotonicity/convergence wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeExtensions` — Concrete finite-volume
  extension graph comparison and correlation equality wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity` — Concrete
  Lambda-layer correlation and magnetization convergence / monotonicity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimits` — Concrete
  along-exhaustion correlation boundedness, eventuality, and infinite-volume limit wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.Translation` — Concrete finite-volume,
  along-exhaustion, and infinite-volume translation-invariance wrappers.

### Regularity and response functions

- `IsingModel.Concrete.LatticeGraphCorrelation.Regularity` — Concrete `HasDerivAt` wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.JointRegularity` — Concrete joint
  Continuous/Differentiable and pointwise joint wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.JointAnalyticity` — Concrete joint
  AnalyticAt/AnalyticOnNhd wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` — Concrete J-direction
  `correlationAlongExhaustion` pointwise wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity` — Concrete
  per-parameter `magnetizationAlongExhaustion` pointwise wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationConvergence` — Concrete magnetization
  convergence wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationRegularity` — Concrete magnetization
  regularity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityConvergence` — Concrete susceptibility
  convergence wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityLambda` — Concrete Lambda-layer
  susceptibility regularity and parameter-direction convergence wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity` — Concrete
  per-parameter `susceptibilityAlongExhaustion` pointwise wrappers.

### Partition functions and free energy

- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity` — Concrete
  partition/free-energy disjoint-union monotonicity and superadditivity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionExhaustionBounds` — Concrete
  partition-function along-exhaustion volume/parameter monotonicity, positivity, divergence, and
  infinite-volume free-energy positivity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyMonotonicity` — Concrete
  free-energy along-exhaustion, log partition-function along-exhaustion, and Lambda-layer
  partition-function parameter monotonicity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBounds` — Concrete
  partition/free-energy lower bounds, nonnegativity, infinite-volume bridges, and uniform-bound
  wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeEnergyBounds` — Concrete finite-volume
  Boltzmann-weight, Hamiltonian, partition-function, and free-energy bound wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCases` — Concrete free-energy closed
  forms, lower bounds, monotonicity, h-symmetry, absolute-field wrappers, and bottom-graph
  comparison wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedForms` — Concrete
  partition-function closed-form wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionSymmetry` — Concrete
  partition-function h-symmetry and absolute-field wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity` — Concrete
  per-parameter `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion` pointwise wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionRegularity` — Concrete
  partition-function regularity-at-zero-field wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergyAnalyticity` — Concrete free-energy
  per-direction analyticity wrappers.

### Polymer free energy and Mayer expansions

#### Polymer free energy

- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyAnalyticity` — Concrete
  `polymerFreeEnergy` analytic wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBasic` — Concrete basic
  `polymerFreeEnergy` at-zero / at-one / sandwich wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBounds` — Concrete
  `polymerFreeEnergy` regularity and bound wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyEpsilonSharpening` — Concrete
  epsilon nonnegativity and non-tanh `polymerFreeEnergy` sharpening wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyHighTemperatureBounds` — Concrete
  `vdPolymerFamilies_sum` high-temperature sandwich/monotone and `polymerFreeEnergy(tanh)`
  high-temperature bound wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhBounds` — Concrete
  `polymerFreeEnergy` tanh-bound, ferromagnetic, `HasDerivAt`, and `log(1 + eps)` wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhSharpening` — Concrete
  `polymerFreeEnergy` tanh sharpening and beta/J strict-mono wrappers.

#### Mayer identities and edge cases

- `IsingModel.Concrete.LatticeGraphCorrelation.MayerAnalyticity` — Concrete `mayerPartialSum` /
  `mayerExpansionTerm` analytic wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerBasicIdentities` — Concrete Mayer basic at-zero
  / at-one identity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerEdgeCases` — Concrete Mayer edge-case identity
  and `polymerFreeEnergy = mayerPartialSum` wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerExpansionEdgeCases` — Concrete Mayer expansion
  `n = 2`, no-polymer, edgeless, and absolute-bound wrappers.

#### Mayer positivity and summability

- `IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonInfrastructure` — Concrete Mayer epsilon
  infrastructure, first-term sign, and edgeless `allPolymers` wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonPositivity` — Concrete epsilon and
  `polymerFreeEnergy` positivity/zero iff wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerRecurrenceHasSum` — Concrete Mayer recurrence,
  `polymerFreeEnergy` `HasSum`, and `vdPolymerFamilies_sum - 1` tendsto-zero wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerStrictPositivity` — Concrete strict-monotonicity
  and strict-positivity wrappers under `allPolymers` nonempty hypotheses.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerTanhFerromagneticIff` — Concrete ferromagnetic
  tanh iff wrappers for `polymerFreeEnergy` and `vdPolymerFamilies_sum`.

#### Mayer regularity and vd-family analyticity

- `IsingModel.Concrete.LatticeGraphCorrelation.MayerTrivialCases` — Concrete Mayer
  trivial/no-polymer comparison wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerVdIff` — Concrete `vdPolymerFamilies_sum` iff
  characterization wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularity` — Concrete `mayerPartialSum` /
  `mayerExpansionTerm` / `vdPolymerFamilies_sum` regularity wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.VdPolymerFamiliesAnalyticity` — Concrete
  `vdPolymerFamilies_sum` / `log_vdPolymerFamilies_sum` analytic wrappers.

### High-temperature results

- `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperature` — Concrete high-temperature
  convergence and correction wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBounds` — Concrete high-temperature
  expansion and bound wrappers.
- `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureCapstones` — Concrete high-temperature
  partition-function/free-energy capstone wrappers.

## Ambient-lattice special cases

### Infinite-volume limits, joint regularity, and response functions

- `IsingModel.AmbientLattice.SpecialCases.InfiniteVolume` — Ambient infinite-volume special cases.
- `IsingModel.AmbientLattice.SpecialCases.JointRegularity` — Ambient along-exhaustion joint
  Continuous/Differentiable and pointwise joint wrappers.
- `IsingModel.AmbientLattice.SpecialCases.JointAnalyticity` — Ambient along-exhaustion joint
  AnalyticAt/AnalyticOnNhd wrappers.
- `IsingModel.AmbientLattice.SpecialCases.Magnetization` — Ambient along-exhaustion magnetization
  convergence and regularity wrappers.
- `IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence` — Ambient along-exhaustion
  susceptibility convergence wrappers.
- `IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity` — Faster targeted
  checks.

### Partition functions and free energy

- `IsingModel.AmbientLattice.SpecialCases.FreeEnergy` — Ambient free-energy special cases.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms` — Ambient along-exhaustion
  partition-function closed-form wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetry` — Ambient along-exhaustion
  partition-function h-symmetry and absolute-field wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity` — Ambient
  `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion` pointwise wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity` — Ambient
  `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion` Continuous and Differentiable
  wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity` — Ambient
  `partitionFunctionAlongExhaustion` regularity-at-zero-field wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticity` — Ambient
  `partitionFunctionAlongExhaustion` joint and general-h analyticity wrappers.
- `IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity` — Ambient
  `freeEnergyAlongExhaustion` per-direction analyticity wrappers.

### Polymer free energy and Mayer expansions

#### Polymer free energy

- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity` — Ambient along-exhaustion
  `polymerFreeEnergy` analytic wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic` — Ambient along-exhaustion basic
  `polymerFreeEnergy` at-zero / at-one / sandwich wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds` — Ambient along-exhaustion
  `polymerFreeEnergy` regularity and bound wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening` — Ambient
  along-exhaustion epsilon nonnegativity and non-tanh `polymerFreeEnergy` sharpening wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds` — Ambient
  along-exhaustion `vdPolymerFamilies_sum` high-temperature sandwich/monotone and
  `polymerFreeEnergy(tanh)` high-temperature bound wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds` — Ambient along-exhaustion
  `polymerFreeEnergy` tanh-bound, ferromagnetic, `HasDerivAt`, and `log(1 + eps)` wrappers.
- `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening` — Ambient
  along-exhaustion `polymerFreeEnergy` tanh sharpening and beta/J strict-mono wrappers.

#### Mayer identities and edge cases

- `IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity` — Ambient along-exhaustion
  `mayerPartialSum` / `mayerExpansionTerm` analytic wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities` — Ambient along-exhaustion Mayer
  basic at-zero / at-one identity wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases` — Ambient along-exhaustion Mayer edge-case
  identity and `polymerFreeEnergy = mayerPartialSum` wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases` — Ambient along-exhaustion Mayer
  expansion `n = 2`, no-polymer, edgeless, and absolute-bound wrappers.

#### Mayer positivity and summability

- `IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure` — Ambient along-exhaustion
  Mayer epsilon infrastructure, first-term sign, and edgeless `allPolymers` wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity` — Ambient along-exhaustion epsilon
  and `polymerFreeEnergy` positivity/zero iff wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerFilterConnected` — Ambient along-exhaustion Mayer
  filter-connected and epsilon-power wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum` — Ambient along-exhaustion Mayer
  recurrence, `polymerFreeEnergy` `HasSum`, and `vdPolymerFamilies_sum - 1` tendsto-zero wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity` — Ambient along-exhaustion
  strict-monotonicity and strict-positivity wrappers under `allPolymers` nonempty hypotheses.
- `IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff` — Ambient along-exhaustion
  ferromagnetic tanh iff wrappers for `polymerFreeEnergy` and `vdPolymerFamilies_sum`.

#### Mayer regularity and vd families

- `IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases` — Ambient along-exhaustion Mayer
  trivial/no-polymer comparison wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerVdBounds` — Ambient along-exhaustion
  `vdPolymerFamilies_sum` bound wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerVdIff` — Ambient along-exhaustion
  `vdPolymerFamilies_sum` iff characterization wrappers.
- `IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity` — Ambient along-exhaustion
  `mayerPartialSum` / `mayerExpansionTerm` / `vdPolymerFamilies_sum` regularity wrappers.
- `IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity` — Ambient along-exhaustion
  `vdPolymerFamilies_sum` / `log_vdPolymerFamilies_sum` analytic wrappers.

### High-temperature results

- `IsingModel.AmbientLattice.SpecialCases.HighTemperature` — Ambient along-exhaustion
  high-temperature convergence and correction wrappers.
- `IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds` — Ambient along-exhaustion
  high-temperature expansion and bound wrappers.
- `IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones` — Ambient along-exhaustion
  high-temperature partition-function/free-energy capstone wrappers.
