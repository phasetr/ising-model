import IsingModel.Concrete.LatticeGraphCorrelation.Legacy

/-!
# Concrete correlation umbrella for the ℤ^d Ising model

This module is intentionally a thin re-export. The compatibility shim
`IsingModel.Concrete.LatticeGraphCorrelation.Legacy` re-exports the split child
modules for older import paths. New narrow APIs should be added in dedicated
child modules and re-exported here only when they belong to the public concrete
correlation surface. For
concrete finite-volume graph, spin-algebra, bottom-graph, and Hamiltonian
symmetry wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeBasics` directly. For
concrete finite-volume HNC, Gibbs-expectation, and correlation monotonicity /
convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationMonotonicity`
directly. For concrete finite-volume extension graph comparison and
correlation equality wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeExtensions`
directly. For concrete Lambda-layer correlation and magnetization convergence /
monotonicity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity`
directly. For concrete along-exhaustion correlation boundedness, eventuality,
and infinite-volume limit wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimits`
directly. For concrete finite-volume, along-exhaustion, and infinite-volume
translation-invariance wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.Translation` directly. For
concrete partition/free-energy disjoint-union monotonicity and
superadditivity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity`
directly. For concrete partition-function along-exhaustion volume / parameter
monotonicity, positivity, divergence, and infinite-volume free-energy
positivity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionExhaustionBounds`
directly. For concrete free-energy along-exhaustion, log partition-function
along-exhaustion, and Lambda-layer partition-function parameter monotonicity
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyMonotonicity`
directly. For concrete partition/free-energy lower bounds, nonnegativity,
infinite-volume bridges, and uniform-bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBounds`
directly. For concrete finite-volume correlation and truncated-correlation
inequality, odd-vanishing, and trivial-slice wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationInequalities`
directly. For concrete infinite-volume GHS / Lebowitz two-point separation
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities`
directly. For
concrete finite-volume Boltzmann-weight, Hamiltonian, partition-function, and
free-energy bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeEnergyBounds`
directly. For concrete finite-volume Hamiltonian closed forms, direct
finite-volume energy / partition / free-energy bound wrappers, and spinProduct
helper wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.EnergyClosedForms`
directly. For
concrete direct finite-volume `partitionFunction` monotonicity, trivial-slice,
and negative-field symmetry wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumePartition` directly. For
concrete direct finite-volume `partitionFunction` absolute-field, positivity,
and ferromagnetic lower-bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumePartitionBounds`
directly. For
concrete correlation, magnetization, and truncated-correlation h-symmetry /
absolute-field wrappers, including finite-volume, along-exhaustion, and
infinite-volume susceptibility / magnetization abs-h wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry` directly. For
concrete §5.1 cluster-decay and high-temperature correlation-decay wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay` directly.
For concrete §17 `HasExponentialDecay` and `latticeMass` foundation wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation`
directly.
For concrete high-temperature lattice-mass, antitonicity, and tanh lower-bound
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature`
directly.
For concrete product-summability, critical inverse temperature, pseudo-mass
transfer, and below-critical cluster wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer`
directly.
For concrete finite-susceptibility and Lebowitz derivative wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative`
directly.
For concrete high-temperature Lipschitz, continuity, uniform convergence, and
a.e. differentiability wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz`
directly.
For concrete high-temperature zero-boundary, closed-interval, and half-open
continuity / locally uniform convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary`
directly.
For concrete `truncated2Infinite` high-temperature regularity wrappers (Step
185--187 / 239--240 / 241), import
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassTruncated2HighTemp`
directly.
For concrete anchored cubic pseudo-mass abbreviations, transport lemmas, and
tanh-profile predicates, import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic` directly.
For concrete anchored cubic tanh-profile active-range and high-temperature
lattice-mass bridge wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfile`
directly.
For concrete anchored cubic named-rate lattice-mass, interval, and decay
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate` directly.
For concrete anchored cubic pseudo-mass cluster and product-summability wrappers,
import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassClusterSummability`
directly.
For concrete anchored cubic pseudo-mass product-sum wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassProductSum` directly.
For concrete anchored cubic pseudo-mass capstone wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMass` directly.
For
concrete Peierls along-exhaustion wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.Peierls` directly. For
concrete free-energy per-direction analyticity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergyAnalyticity` directly.
For concrete Lambda-layer susceptibility regularity and parameter-direction
convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityLambda` directly.
For concrete `HasDerivAt` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.Regularity` directly. For
concrete joint `Continuous` / `Differentiable` / pointwise joint wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.JointRegularity`
directly. For concrete joint `AnalyticAt` / `AnalyticOnNhd` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.JointAnalyticity` directly. For
concrete Mayer `AnalyticAt` / `AnalyticOnNhd` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerAnalyticity` directly. For
concrete Mayer basic at-zero / at-one identity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerBasicIdentities` directly. For
concrete Mayer edge-case identity and `polymerFreeEnergy = mayerPartialSum`
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerEdgeCases` directly. For
concrete Mayer expansion `n = 2`, no-polymer, edgeless, and absolute-bound
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerExpansionEdgeCases` directly. For
concrete Mayer epsilon infrastructure, first-term sign, and edgeless
`allPolymers` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonInfrastructure`
directly. For concrete epsilon and `polymerFreeEnergy` positivity/zero iff
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonPositivity` directly.
For concrete Mayer filter-connected and epsilon-power wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerFilterConnected` directly.
For concrete Mayer recurrence, `polymerFreeEnergy` `HasSum`, and
`vdPolymerFamilies_sum - 1` tendsto-zero wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerRecurrenceHasSum`
directly. For
concrete strict-monotonicity and strict-positivity wrappers under
`allPolymers` nonempty hypotheses, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerStrictPositivity`
directly. For
concrete ferromagnetic tanh iff wrappers for `polymerFreeEnergy` and
`vdPolymerFamilies_sum`, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerTanhFerromagneticIff`
directly. For
concrete Mayer trivial/no-polymer comparison wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerTrivialCases` directly. For
concrete `vdPolymerFamilies_sum` bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerVdBounds` directly. For
concrete `vdPolymerFamilies_sum` iff characterization wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerVdIff` directly. For
concrete Mayer and `vdPolymerFamilies_sum` regularity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularity` directly. For
concrete β-direction `correlationAlongExhaustion` legacy-compatible regularity
names and J-direction `ContinuousAt` / `DifferentiableAt` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` directly. For
concrete per-parameter `magnetizationAlongExhaustion` pointwise wrappers,
import
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity`
directly. For concrete magnetization convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationConvergence` directly.
For concrete magnetization regularity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationRegularity` directly.
For concrete susceptibility convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityConvergence` directly.
For concrete free-energy closed forms, monotonicity, h-symmetry, and
bottom-graph comparison wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCases` directly.
For concrete partition-function closed-form wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedForms`
directly.
For concrete partition-function h-symmetry and absolute-field wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionSymmetry`
directly.
For concrete per-parameter `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity`
directly. For concrete partition-function regularity-at-zero-field wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionRegularity`
directly. For concrete partition/free-energy Continuous and Differentiable
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyRegularity`
directly. For concrete partition-function joint and general-h analyticity
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionGeneralAnalyticity`
directly. For concrete `polymerFreeEnergy` analytic wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyAnalyticity`
directly. For concrete basic `polymerFreeEnergy` at-zero / at-one / sandwich
wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBasic` directly.
For concrete `polymerFreeEnergy` regularity and bound wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBounds`
directly.
For concrete epsilon nonnegativity and non-tanh `polymerFreeEnergy`
sharpening wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyEpsilonSharpening`
directly.
For concrete `vdPolymerFamilies_sum` high-temperature sandwich/monotone and
`polymerFreeEnergy(tanh)` high-temperature bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyHighTemperatureBounds`
directly.
For concrete `polymerFreeEnergy` tanh-bound, ferromagnetic, `HasDerivAt`,
and `log(1 + eps)` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhBounds`
directly. For concrete `polymerFreeEnergy` tanh sharpening and beta/J
strict-mono wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhSharpening`
directly. For concrete `vdPolymerFamilies_sum` and
`log_vdPolymerFamilies_sum` analytic wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.VdPolymerFamiliesAnalyticity`
directly. For concrete high-temperature convergence and correction wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperature`
directly. For concrete high-temperature expansion and bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBounds` directly.
For concrete §18.3-§18.4 high-temperature partition-function and free-energy
expansion / closed-form / lower-bound / upper-bound / `lower_le_upper`
wrappers at `h = 0` (plus the
`correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A` consistency check),
import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansion`
directly. Sandwich / sharper-exp / ratio / deviation wrappers remain in
`HighTemperatureBounds`.
For concrete §18.3-§18.4 `correlationΛ_latticeGraph` basic high-temperature
wrappers at `h = 0` (pair nonneg, pair `≤ 1`, singleton / pair trivial-slice
vanishings at `J = 0` and `β = 0`, pair sandwich, singleton / pair
ferromagnetic, singleton `= 0 ∧ ≤ 1`, pair+singleton bundle), import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationBasic`
directly. For concrete §18.3-§18.4 sharper-exp upper-bound / sandwich /
complete-summary wrappers at `h = 0` (17 theorems for
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`
families with ferromagnetic variants), import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharper`
directly.
For concrete §18.7 high-temperature pair-correlation
exponential-decay capstones (five capstone families `tanh_pow_dist` /
`exp_rate_dist` / `exp_highTempExpRate_dist` / `exp_alpha_dist` /
`exp_alpha_dist_of_le_highTempExpRate` for `correlationΛ_latticeGraph`
and `correlationAlongExhaustion_latticeGraph`, plus ferromagnetic
variants -- 16 theorems), import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDecayCapstones`
directly. Some named-rate / monotone-rate ferromagnetic variants of
`exp_highTempExpRate_dist` remain in
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay`.
For concrete high-temperature partition-function/free-energy capstone wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureCapstones`
directly.
For concrete per-parameter `susceptibilityAlongExhaustion` pointwise wrappers
and legacy-compatible finite-stage susceptibility regularity names, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
directly.
-/
