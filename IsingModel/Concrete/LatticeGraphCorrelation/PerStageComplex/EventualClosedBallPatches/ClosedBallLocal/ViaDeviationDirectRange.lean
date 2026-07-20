import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.AmbientLatticeSum.SuperadditiveConvergence
import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.Geometry
import IsingModel.AmbientComplexAnalyticity.Vitali.BranchFamilies
import IsingModel.ComplexAnalyticity.LeeYangDomain
import IsingModel.AmbientComplexAnalyticity.Vitali.BranchData
import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchLocallyBounded
import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.EventualOverlap

/-!
# ClosedBallLocal wrappers (3/5): via-deviation direct-range patches

Structural split (3/5) of
`Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal`.
This child holds the *via-deviation* direct-range route, in which closed-ball branch-local
boundedness is converted through closed-ball branch-deviation data using the automatic
closed-ball principal free-energy bound before direct-range patching: the abstract patch,
its compact-target form and the positive-real compact-target endpoint.  See the
`…EventualClosedBallPatches.ClosedBallLocal` facade module for the full contents overview.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d closed-ball branch-local data to direct-range patch via branch
deviation**: branch-local boundedness is converted to closed-ball
branch-deviation data using the automatic closed-ball principal free-energy
bound before directRange patching. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K closedData.data)
    (closedBallLocal :
      Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K closedData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom closedBallLocal

set_option linter.style.longLine false in
/-- **ℤ^d compact target to closed-ball branch-local via-deviation direct-range
patch input**: compactness extracts finite all-stage geometry; closed-ball
branch-local boundedness is converted through branch-deviation data before
directRange patching. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K closedData.data,
      Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K closedData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to closed-ball branch-local
via-deviation direct-range patch input**: positive real ferromagnetic
parameters construct closed-ball all-stage branch data, then branch-local
boundedness is converted through branch-deviation data before directRange
patching. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocalViaDeviation_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ closedData :
        Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K closedData.data,
        Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData
            (IsingModel.latticeGraph d) Λ p K closedData geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocalViaDeviation_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

end Ambient
end IsingModel
