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
directly. For
concrete J-direction `correlationAlongExhaustion` `ContinuousAt` /
`DifferentiableAt` wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` directly. For
concrete per-parameter `magnetizationAlongExhaustion` pointwise wrappers,
import
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity`
directly. For concrete per-parameter `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity`
directly. For concrete per-parameter `susceptibilityAlongExhaustion`
pointwise wrappers, import
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
directly.
-/
