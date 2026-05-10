import IsingModel.AmbientLattice.SpecialCases.Legacy

/-!
# Ambient-lattice special cases umbrella

This module is intentionally a thin re-export. The compatibility shim
`IsingModel.AmbientLattice.SpecialCases.Legacy` re-exports the split child
modules for older import paths. Non-analytic free-energy special cases live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergy`, and
general-graph free-energy per-direction analyticity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity`. Lightweight
infinite-volume aliases live in
`IsingModel.AmbientLattice.SpecialCases.InfiniteVolume`. General-graph joint
regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.JointRegularity`. General-graph
joint analyticity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.JointAnalyticity`. General-graph
Mayer analytic wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity`. General-graph
Mayer basic at-zero / at-one identity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities`. General-graph
Mayer edge-case identity and `polymerFreeEnergy = mayerPartialSum` wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases`. General-graph
Mayer expansion `n = 2`, no-polymer, edgeless, and absolute-bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases`. General-graph
Mayer epsilon infrastructure, first-term sign, and edgeless `allPolymers`
wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure`.
General-graph epsilon and `polymerFreeEnergy` positivity/zero iff wrappers
live in `IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity`.
General-graph Mayer filter-connected and epsilon-power wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerFilterConnected`.
General-graph Mayer recurrence, `polymerFreeEnergy` `HasSum`, and
`vdPolymerFamilies_sum - 1` tendsto-zero wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum`.
General-graph strict-monotonicity and strict-positivity wrappers under
`allPolymers` nonempty hypotheses live in
`IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity`. General-graph
ferromagnetic tanh iff wrappers for `polymerFreeEnergy` and
`vdPolymerFamilies_sum` live in
`IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff`. General-graph
Mayer trivial/no-polymer comparison wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases`. General-graph
`vdPolymerFamilies_sum` bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdBounds`. General-graph
`vdPolymerFamilies_sum` iff characterization wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdIff`. General-graph
Mayer and `vdPolymerFamilies_sum` regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity`. General-graph
magnetization convergence wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationConvergence`.
General-graph
magnetization regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity`.
General-graph
susceptibility convergence wrappers live in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence`.
General-graph along-exhaustion partition-function closed-form wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms`.
General-graph along-exhaustion partition-function h-symmetry and absolute-field
wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetry`.
General-graph
`polymerFreeEnergy` analytic wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity`.
General-graph basic `polymerFreeEnergy` at-zero / at-one / sandwich wrappers
live in `IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic`.
General-graph `polymerFreeEnergy` regularity and bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds`.
General-graph epsilon nonnegativity and non-tanh `polymerFreeEnergy`
sharpening wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening`.
General-graph `vdPolymerFamilies_sum` high-temperature sandwich/monotone and
`polymerFreeEnergy(tanh)` high-temperature bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds`.
General-graph `polymerFreeEnergy` tanh-bound, ferromagnetic, `HasDerivAt`,
and `log(1 + eps)` wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds`.
General-graph `polymerFreeEnergy` tanh sharpening and beta/J strict-mono
wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening`.
General-graph `vdPolymerFamilies_sum` and `log_vdPolymerFamilies_sum`
analytic wrappers live in
`IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity`.
General-graph high-temperature convergence and correction wrappers live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperature`.
General-graph high-temperature expansion and bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds`.
General-graph high-temperature partition-function/free-energy capstone
wrappers live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones`.
General-graph
`partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion` pointwise
regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity`,
general-graph `partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion`
Continuous and Differentiable wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity`,
general-graph `partitionFunctionAlongExhaustion` regularity-at-zero-field
wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity`,
general-graph `partitionFunctionAlongExhaustion` joint and general-h
analyticity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticity`,
and `susceptibilityAlongExhaustion` pointwise regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity`.
New narrow APIs should be added in dedicated child modules and re-exported here
only when they belong to the public ambient special-cases surface.
-/
