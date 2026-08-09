import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasicPartitionSingle
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompatLeeYangSubdomain
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNormContinuous
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranches
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchesLogZ
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexSlitPlane
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictions
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictionsRealParams
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntire
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntireContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexIsingPoly

/-!
# ℤ^d complex partition function and free energy on a fixed finite volume, assembled

Aggregates, for callers that want the family behind a single import, the ℤ^d specialisations
proved in the modules it imports, all stated at the subgraph induced on a fixed finite volume
`Λ : Finset (Fin d → ℤ)`: analyticity and continuity of `partitionFunctionComplex` at every
base point, in each parameter separately and jointly; analyticity of `freeEnergyComplex`
wherever `partitionFunctionComplex` lands in `Complex.slitPlane`, including at real
parameters and on the Lee-Yang subdomain; agreement of the complex partition function and
free energy with their real counterparts at real parameters; the Friedli-Velenik
factorisation of `partitionFunctionComplex` through `isingEdgePoly` and `leeYangFugacityVec`;
Lee-Yang non-vanishing on `leeYangDomain`; and the local logarithmic branches of the
partition function on balls inside `leeYangDomain`, together with the analytic branch of
`freeEnergyComplex` over `leeYangDomain`.
-/

namespace IsingModel

namespace Ambient

end Ambient
end IsingModel
