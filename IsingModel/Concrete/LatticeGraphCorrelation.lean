import IsingModel.Concrete.LatticeGraphCorrelation.Legacy

/-!
# Concrete correlation umbrella for the ℤ^d Ising model

This module is intentionally a thin re-export. The legacy monolithic
implementation lives in `IsingModel.Concrete.LatticeGraphCorrelation.Legacy`;
new narrow APIs should be added in dedicated child modules and re-exported
here only when they belong to the public concrete correlation surface. For
concrete `HasDerivAt` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.Regularity` directly. For
concrete joint `Continuous` / `Differentiable` / pointwise joint wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.JointRegularity`
directly. For concrete joint `AnalyticAt` / `AnalyticOnNhd` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.JointAnalyticity` directly. For
concrete Mayer `AnalyticAt` / `AnalyticOnNhd` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.MayerAnalyticity` directly. For
concrete J-direction `correlationAlongExhaustion` `ContinuousAt` /
`DifferentiableAt` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` directly. For
concrete per-parameter `magnetizationAlongExhaustion` pointwise wrappers,
import
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity`
directly. For concrete per-parameter `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity`
directly. For concrete `polymerFreeEnergy` analytic wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyAnalyticity`
directly. For concrete `vdPolymerFamilies_sum` and
`log_vdPolymerFamilies_sum` analytic wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.VdPolymerFamiliesAnalyticity`
directly. For concrete high-temperature convergence and correction wrappers,
import `IsingModel.Concrete.LatticeGraphCorrelation.HighTemperature`
directly. For concrete high-temperature expansion and bound wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBounds` directly.
For concrete per-parameter `susceptibilityAlongExhaustion`
pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
directly.
-/
