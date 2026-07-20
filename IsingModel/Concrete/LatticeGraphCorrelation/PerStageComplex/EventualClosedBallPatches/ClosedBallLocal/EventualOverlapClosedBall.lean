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
import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.CompactTarget

/-!
# ClosedBallLocal wrappers (4/5): eventual-overlap closed-ball patches

Structural split (4/5) of
`Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal`.
This child holds the eventual-overlap **closed-ball** branch-local direct-range route, where
coherent selected-overlap equality is supplied by the pointwise-normalised eventual-overlap
package: the abstract patch and its compact-target form.  See the
`…EventualClosedBallPatches.ClosedBallLocal` facade module for the full contents overview.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap closed-ball branch local boundedness to
direct-range relatively compact patch**: coherent selected-overlap equality is
supplied by pointwise-normalised eventual-overlap data, while closed-ball
containment and branch-local Ascoli inputs remain explicit. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
        closedEventualData).data)
    (closedEventualLocal :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K closedEventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd
    closedEventualData geom closedEventualLocal

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap closed-ball branch-local
direct-range patch input**: compactness extracts the selected finite geometry,
and pointwise-normalised eventual-overlap data supplies coherent
selected-overlap equality for the closed-ball branch-local route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
          closedEventualData).data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K closedEventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK closedEventualData

end Ambient
end IsingModel
