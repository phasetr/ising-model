---
layout: default
title: Library map
---

[Back to the documentation home](index.md). The intended import direction is specified by the
[import-DAG layer contract](architecture-import-layers.md).

## Focused public modules

> **Import note:** `IsingModel.Concrete.LatticeGraphCorrelation` is a thin
> public re-export umbrella over its split child modules. New narrow APIs
> should prefer dedicated child modules such as
> `IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay`,
> `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic` for
> concrete anchored cubic pseudo-mass abbreviations, transport lemmas, and
> tanh-profile predicates,
> `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfile` for
> concrete anchored cubic tanh-profile active-range and high-temperature
> lattice-mass bridge wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate` for
> concrete anchored cubic named-rate lattice-mass, interval, and decay wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassClusterSummability`
> for concrete anchored cubic named-rate cluster and product-summability
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassProductSum` for
> concrete anchored cubic named-rate product-sum wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.Peierls` for concrete Peierls
> along-exhaustion wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.Regularity` for concrete
> `HasDerivAt` wrappers, and
> `IsingModel.Concrete.LatticeGraphCorrelation.JointRegularity` for concrete
> joint Continuous/Differentiable and pointwise joint wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.JointAnalyticity` for concrete
> joint AnalyticAt/AnalyticOnNhd wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` for
> concrete J-direction `correlationAlongExhaustion` pointwise wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity`
> for concrete per-parameter `magnetizationAlongExhaustion` pointwise wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationConvergence` for
> concrete magnetization convergence wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationRegularity` for
> concrete magnetization regularity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityConvergence` for
> concrete susceptibility convergence wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityLambda` for
> concrete Lambda-layer susceptibility regularity and parameter-direction
> convergence wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationMonotonicity`
> for concrete finite-volume HNC, Gibbs-expectation, and correlation
> monotonicity/convergence wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeExtensions` for
> concrete finite-volume extension graph comparison and correlation equality
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity`
> for concrete Lambda-layer correlation and magnetization convergence /
> monotonicity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimits`
> for concrete along-exhaustion correlation boundedness, eventuality, and
> infinite-volume limit wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.Translation` for concrete
> finite-volume, along-exhaustion, and infinite-volume translation-invariance
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity`
> for concrete partition/free-energy disjoint-union monotonicity and
> superadditivity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionExhaustionBounds` for
> concrete partition-function along-exhaustion volume/parameter monotonicity,
> positivity, divergence, and infinite-volume free-energy positivity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyMonotonicity`
> for concrete free-energy along-exhaustion, log partition-function
> along-exhaustion, and Lambda-layer partition-function parameter monotonicity
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBounds` for
> concrete partition/free-energy lower bounds, nonnegativity,
> infinite-volume bridges, and uniform-bound wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeEnergyBounds` for
> concrete finite-volume Boltzmann-weight, Hamiltonian, partition-function, and
> free-energy bound wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCases` for
> concrete free-energy closed forms, lower bounds, monotonicity, h-symmetry,
> absolute-field wrappers, and bottom-graph comparison wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedForms` for
> concrete partition-function closed-form wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionSymmetry` for
> concrete partition-function h-symmetry and absolute-field wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity`
> for concrete per-parameter `partitionFunctionAlongExhaustion` /
> `freeEnergyAlongExhaustion` pointwise wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionRegularity`
> for concrete partition-function regularity-at-zero-field wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergyAnalyticity`
> for concrete free-energy per-direction analyticity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyAnalyticity`
> for concrete `polymerFreeEnergy` analytic wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBasic` for
> concrete basic `polymerFreeEnergy` at-zero / at-one / sandwich wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBounds` for
> concrete `polymerFreeEnergy` regularity and bound wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyEpsilonSharpening`
> for concrete epsilon nonnegativity and non-tanh `polymerFreeEnergy`
> sharpening wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyHighTemperatureBounds`
> for concrete `vdPolymerFamilies_sum` high-temperature sandwich/monotone and
> `polymerFreeEnergy(tanh)` high-temperature bound wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhBounds`
> for concrete `polymerFreeEnergy` tanh-bound, ferromagnetic, `HasDerivAt`,
> and `log(1 + eps)` wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhSharpening`
> for concrete `polymerFreeEnergy` tanh sharpening and beta/J strict-mono
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerAnalyticity` for concrete
> `mayerPartialSum` / `mayerExpansionTerm` analytic wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerBasicIdentities` for
> concrete Mayer basic at-zero / at-one identity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerEdgeCases` for concrete
> Mayer edge-case identity and `polymerFreeEnergy = mayerPartialSum` wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerExpansionEdgeCases` for
> concrete Mayer expansion `n = 2`, no-polymer, edgeless, and absolute-bound
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonInfrastructure` for
> concrete Mayer epsilon infrastructure, first-term sign, and edgeless
> `allPolymers` wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonPositivity` for
> concrete epsilon and `polymerFreeEnergy` positivity/zero iff wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerRecurrenceHasSum` for
> concrete Mayer recurrence, `polymerFreeEnergy` `HasSum`, and
> `vdPolymerFamilies_sum - 1` tendsto-zero wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerStrictPositivity` for
> concrete strict-monotonicity and strict-positivity wrappers under
> `allPolymers` nonempty hypotheses,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerTanhFerromagneticIff`
> for concrete ferromagnetic tanh iff wrappers for `polymerFreeEnergy` and
> `vdPolymerFamilies_sum`,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerTrivialCases` for concrete
> Mayer trivial/no-polymer comparison wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerVdIff` for concrete
> `vdPolymerFamilies_sum` iff characterization wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularity` for concrete
> `mayerPartialSum` / `mayerExpansionTerm` / `vdPolymerFamilies_sum`
> regularity wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.VdPolymerFamiliesAnalyticity`
> for concrete `vdPolymerFamilies_sum` / `log_vdPolymerFamilies_sum` analytic
> wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperature` for concrete
> high-temperature convergence and correction wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBounds` for
> concrete high-temperature expansion and bound wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureCapstones` for
> concrete high-temperature partition-function/free-energy capstone wrappers,
> `IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
> for concrete per-parameter `susceptibilityAlongExhaustion` pointwise wrappers,
> plus
> `IsingModel.AmbientLattice.SpecialCases.FreeEnergy` /
> `IsingModel.AmbientLattice.SpecialCases.InfiniteVolume`, and
> `IsingModel.AmbientLattice.SpecialCases.JointRegularity` for ambient
> along-exhaustion joint Continuous/Differentiable and pointwise joint wrappers,
> `IsingModel.AmbientLattice.SpecialCases.JointAnalyticity` for ambient
> along-exhaustion joint AnalyticAt/AnalyticOnNhd wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity` for ambient
> along-exhaustion `mayerPartialSum` / `mayerExpansionTerm` analytic wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities` for ambient
> along-exhaustion Mayer basic at-zero / at-one identity wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases` for ambient
> along-exhaustion Mayer edge-case identity and
> `polymerFreeEnergy = mayerPartialSum` wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases` for ambient
> along-exhaustion Mayer expansion `n = 2`, no-polymer, edgeless, and
> absolute-bound wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure` for
> ambient along-exhaustion Mayer epsilon infrastructure, first-term sign, and
> edgeless `allPolymers` wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity` for ambient
> along-exhaustion epsilon and `polymerFreeEnergy` positivity/zero iff wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerFilterConnected` for ambient
> along-exhaustion Mayer filter-connected and epsilon-power wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum` for ambient
> along-exhaustion Mayer recurrence, `polymerFreeEnergy` `HasSum`, and
> `vdPolymerFamilies_sum - 1` tendsto-zero wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity` for ambient
> along-exhaustion strict-monotonicity and strict-positivity wrappers under
> `allPolymers` nonempty hypotheses,
> `IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff` for
> ambient along-exhaustion ferromagnetic tanh iff wrappers for
> `polymerFreeEnergy` and `vdPolymerFamilies_sum`,
> `IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases` for ambient
> along-exhaustion Mayer trivial/no-polymer comparison wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerVdBounds` for ambient
> along-exhaustion `vdPolymerFamilies_sum` bound wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerVdIff` for ambient
> along-exhaustion `vdPolymerFamilies_sum` iff characterization wrappers,
> `IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity` for ambient
> along-exhaustion `mayerPartialSum` / `mayerExpansionTerm` /
> `vdPolymerFamilies_sum` regularity wrappers,
> `IsingModel.AmbientLattice.SpecialCases.Magnetization` for ambient
> along-exhaustion magnetization convergence and regularity wrappers,
> `IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence` for ambient
> along-exhaustion susceptibility convergence wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms` for
> ambient along-exhaustion partition-function closed-form wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetry` for ambient
> along-exhaustion partition-function h-symmetry and absolute-field wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity` for
> ambient along-exhaustion `polymerFreeEnergy` analytic wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic` for ambient
> along-exhaustion basic `polymerFreeEnergy` at-zero / at-one / sandwich wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds` for ambient
> along-exhaustion `polymerFreeEnergy` regularity and bound wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening`
> for ambient along-exhaustion epsilon nonnegativity and non-tanh
> `polymerFreeEnergy` sharpening wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds`
> for ambient along-exhaustion `vdPolymerFamilies_sum` high-temperature
> sandwich/monotone and `polymerFreeEnergy(tanh)` high-temperature bound
> wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds` for
> ambient along-exhaustion `polymerFreeEnergy` tanh-bound, ferromagnetic,
> `HasDerivAt`, and `log(1 + eps)` wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening`
> for ambient along-exhaustion `polymerFreeEnergy` tanh sharpening and beta/J
> strict-mono wrappers,
> `IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity` for
> ambient along-exhaustion `vdPolymerFamilies_sum` /
> `log_vdPolymerFamilies_sum` analytic wrappers,
> `IsingModel.AmbientLattice.SpecialCases.HighTemperature` for ambient
> along-exhaustion high-temperature convergence and correction wrappers,
> `IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds` for ambient
> along-exhaustion high-temperature expansion and bound wrappers,
> `IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones` for ambient
> along-exhaustion high-temperature partition-function/free-energy capstone
> wrappers,
> `IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity`
> for ambient `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion`
> pointwise wrappers, plus
> `IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity`
> for ambient `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion`
> Continuous and Differentiable wrappers, plus
> `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity`
> for ambient `partitionFunctionAlongExhaustion`
> regularity-at-zero-field wrappers, plus
> `IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticity`
> for ambient `partitionFunctionAlongExhaustion` joint and general-h
> analyticity wrappers, plus
> `IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity`
> for ambient `freeEnergyAlongExhaustion` per-direction analyticity
> wrappers, plus
> `IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity`
> for faster targeted checks.
