import IsingModel.AmbientLattice.SpecialCases.Legacy

/-!
# Ambient-lattice special cases umbrella

This module is intentionally a thin re-export. The legacy monolithic body lives
in `IsingModel.AmbientLattice.SpecialCases.Legacy`. Non-analytic free-energy
special cases live in `IsingModel.AmbientLattice.SpecialCases.FreeEnergy`, and
lightweight infinite-volume aliases live in
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
Mayer trivial/no-polymer comparison wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases`. General-graph
`vdPolymerFamilies_sum` bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdBounds`. General-graph
`vdPolymerFamilies_sum` iff characterization wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdIff`. General-graph
Mayer and `vdPolymerFamilies_sum` regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity`. General-graph
`polymerFreeEnergy` analytic wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity`.
General-graph `polymerFreeEnergy` regularity and bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds`.
General-graph `vdPolymerFamilies_sum` and `log_vdPolymerFamilies_sum`
analytic wrappers live in
`IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity`.
General-graph high-temperature convergence and correction wrappers live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperature`.
General-graph high-temperature expansion and bound wrappers live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds`.
General-graph
`partitionFunctionAlongExhaustion` / `freeEnergyAlongExhaustion` pointwise
regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity`,
and `susceptibilityAlongExhaustion` pointwise regularity wrappers live in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity`.
New narrow APIs should be added in dedicated child modules and re-exported here
only when they belong to the public ambient special-cases surface.
-/
