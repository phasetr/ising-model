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
import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.BranchLocal
import IsingModel.AmbientComplexAnalyticity.CompactPatches.DirectRange
import IsingModel.AmbientComplexAnalyticity.CompactPatches.GeometryCOpen
import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.CompactTarget

/-!
# ClosedBallLocal wrappers (2/5): direct-range closed-ball patches

Structural split (2/5) of
`Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal`.
This child holds the direct closed-ball branch-local *range* route: closed-ball branch
locally bounded data converted directly to relatively compact range data before the
all-stage range patch endpoint, its compact-target form, and the positive-real
compact-target endpoint of the same route.  See the
`…EventualClosedBallPatches.ClosedBallLocal` facade module for the full contents overview.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d direct-range closed-ball branch local-boundedness patch input**:
closed-ball branch locally bounded data is converted directly to relatively
compact range data before applying the all-stage range patch endpoint. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
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
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd closedData.data geom
    (Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData.toBranchLocallyBoundedData
      (IsingModel.latticeGraph d) Λ p K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **ℤ^d compact target to direct-range closed-ball branch local-boundedness
patch input**: compactness extracts the finite all-stage geometry from
closed-ball branch data; closed-ball branch locally bounded data then feeds the
direct range relative-compactness route. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch_isCompact_latticeGraph
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
  by
    rcases Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
        (IsingModel.latticeGraph d) Λ p hK hKsub hpK closedData.data with
      ⟨geom⟩
    exact ⟨geom, fun closedBallLocal =>
      freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch_latticeGraph
        d Λ p hBED hd closedData geom closedBallLocal⟩

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to direct-range closed-ball branch
local-boundedness patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts finite
geometry, and branch local boundedness feeds the direct range route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_directRange_patch_isCompact_latticeGraph
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
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

end Ambient
end IsingModel
