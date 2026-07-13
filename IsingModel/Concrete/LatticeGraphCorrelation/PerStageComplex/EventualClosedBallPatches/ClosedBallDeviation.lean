import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal

/-!
# Per-stage complex analyticity wrappers: ClosedBallDeviation

Consolidated `ClosedBallDeviation` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d closed-ball branch-deviation data to a relatively compact range
patch**: closed-ball branch radii supply the principal finite-volume
free-energy local boundedness input; the remaining boundedness assumption is a
uniform branch-deviation estimate. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_latticeGraph
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
    (closedBallDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom
    closedBallDeviation

/-- **ℤ^d compact target to closed-ball branch-deviation relatively compact
patch input**: compactness extracts the finite all-stage geometry from the
underlying closed-ball branch data, then the branch-deviation data supplies the
relative-compactness input. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

/-- **ℤ^d positive-real compact target to closed-ball branch-deviation
relatively compact patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and the remaining branch-deviation data supplies the
relative-compactness input. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_patch_isCompact_latticeGraph
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
        Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

/-!
# ℤ^d closed-ball branch-deviation relatively compact patch wrappers

This compatibility module re-exports the split closed-ball branch-deviation
relatively compact wrapper layer.
-/

set_option linter.style.longLine false in
/-- **ℤ^d direct closed-ball branch-deviation patch input**: closed-ball
branch-deviation data feeds the direct range route through the branch-local
boundary. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_latticeGraph
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
    (closedBallDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom
    closedBallDeviation

set_option linter.style.longLine false in
/-- **ℤ^d compact target to direct closed-ball branch-deviation patch input**:
compactness extracts the finite all-stage geometry from the closed-ball branch
data, then branch-deviation data feeds the direct range route. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to direct closed-ball branch-deviation
patch input**: positive real ferromagnetic parameters construct the closed-ball
all-stage branch data, compactness extracts finite geometry, and
branch-deviation data feeds the direct range route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_direct_patch_isCompact_latticeGraph
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
        Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_direct_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

/-!
# ℤ^d direct closed-ball branch-deviation patch wrappers

This compatibility module re-exports the split direct closed-ball
branch-deviation wrapper layer.
-/

set_option linter.style.longLine false in
/-- **ℤ^d direct-range closed-ball branch-deviation patch input**:
closed-ball branch-deviation data feeds the direct-range route through the
branch-local boundary. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_latticeGraph
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
    (closedBallDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom
    closedBallDeviation

set_option linter.style.longLine false in
/-- **ℤ^d compact target to direct-range closed-ball branch-deviation patch
input**: compactness extracts the finite all-stage geometry from the
closed-ball branch data, then branch-deviation data feeds the direct-range
route. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

set_option linter.style.longLine false in
/-- **ℤ^d named via-local direct-range closed-ball branch-deviation patch
input**: closed-ball branch-deviation data feeds the named branch-local route
before the all-stage relatively compact range patch. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_latticeGraph
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
    (closedBallDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ closedData geom
    closedBallDeviation

set_option linter.style.longLine false in
/-- **ℤ^d compact target to named via-local closed-ball branch-deviation patch
input**: compactness extracts the finite all-stage geometry from the
closed-ball branch data, then branch-deviation data feeds the named via-local
route. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK closedData

/-!
# ℤ^d direct-range closed-ball branch-deviation patch wrappers

This compatibility module re-exports the split direct-range closed-ball
branch-deviation wrapper layer.
-/

/-!
# ℤ^d closed-ball branch-deviation patch wrappers

This compatibility module re-exports the split closed-ball branch-deviation
wrapper layer.
-/

end Ambient
end IsingModel
