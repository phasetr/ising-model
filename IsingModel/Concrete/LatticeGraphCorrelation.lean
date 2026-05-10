import IsingModel.Concrete.LatticeGraphCorrelation.Legacy

/-!
# Concrete correlation umbrella for the ℤ^d Ising model

This module is intentionally a thin re-export. The legacy monolithic
implementation lives in `IsingModel.Concrete.LatticeGraphCorrelation.Legacy`;
new narrow APIs should be added in dedicated child modules and re-exported
here only when they belong to the public concrete correlation surface. For
concrete finite-volume graph, spin-algebra, bottom-graph, and Hamiltonian
symmetry wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeBasics` directly. For
concrete finite-volume HNC, Gibbs-expectation, and correlation monotonicity /
convergence wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationMonotonicity`
directly. For concrete finite-volume correlation and truncated-correlation
inequality, odd-vanishing, and trivial-slice wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationInequalities`
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
absolute-field wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry` directly. For
concrete Peierls along-exhaustion wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.Peierls` directly. For
concrete free-energy per-direction analyticity wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergyAnalyticity` directly.
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
concrete J-direction `correlationAlongExhaustion` `ContinuousAt` /
`DifferentiableAt` wrappers, import
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
For concrete high-temperature partition-function/free-energy capstone wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureCapstones`
directly.
For concrete per-parameter `susceptibilityAlongExhaustion`
pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
directly.
-/
